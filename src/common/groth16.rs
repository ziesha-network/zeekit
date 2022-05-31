use crate::BellmanFr;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::{Field, PrimeFieldBits};
use std::ops::AddAssign;

pub fn bit_or<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::and(&mut *cs, &a.not(), &b.not())?.not())
}

// Check if a number is zero, 2 constraints
pub fn is_zero<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
) -> Result<AllocatedBit, SynthesisError> {
    let out = AllocatedBit::alloc(&mut *cs, a.get_value().map(|a| a.is_zero().into()))?;
    let inv = AllocatedNum::alloc(&mut *cs, || {
        a.get_value()
            .map(|a| {
                if a.is_zero().into() {
                    BellmanFr::zero()
                } else {
                    a.invert().unwrap()
                }
            })
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "calc out",
        |lc| lc - a.get_variable(),
        |lc| lc + inv.get_variable(),
        |lc| lc + out.get_variable() - CS::one(),
    );
    cs.enforce(
        || "calc out",
        |lc| lc + out.get_variable(),
        |lc| lc + a.get_variable(),
        |lc| lc,
    );
    Ok(out)
}

// Check a == b, two constraints
pub fn is_equal<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<AllocatedBit, SynthesisError> {
    let out = AllocatedBit::alloc(&mut *cs, a.get_value().map(|a| a.is_zero().into()))?;
    let inv = AllocatedNum::alloc(&mut *cs, || {
        a.get_value()
            .map(|a| {
                if a.is_zero().into() {
                    BellmanFr::zero()
                } else {
                    a.invert().unwrap()
                }
            })
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "calc out",
        |lc| lc - a.get_variable() + b.get_variable(),
        |lc| lc + inv.get_variable(),
        |lc| lc + out.get_variable() - CS::one(),
    );
    cs.enforce(
        || "calc out",
        |lc| lc + out.get_variable(),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc,
    );
    Ok(out)
}

// Convert number to u64, 65 constraints
pub fn to_u64<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let mut result = Vec::new();
    let mut coeff = BellmanFr::one();
    let mut all = LinearCombination::<BellmanFr>::zero();
    let bits: Option<Vec<bool>> = a
        .get_value()
        .map(|v| v.to_le_bits().iter().map(|b| *b).collect());
    for i in 0..64 {
        let bit = AllocatedBit::alloc(&mut *cs, bits.as_ref().map(|b| b[i]))?;
        all = all + (coeff, bit.get_variable());
        result.push(bit);
        coeff = coeff.double();
    }
    cs.enforce(
        || "u64 check",
        |lc| lc + &all,
        |lc| lc + CS::one(),
        |lc| lc + a.get_variable(),
    );
    Ok(result)
}

// Convert number to u64 and negate
pub fn to_u64_neg<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let mut result = Vec::new();
    let mut coeff = BellmanFr::one();
    let mut all = LinearCombination::<BellmanFr>::zero();
    let two_64 = BellmanFr::from(u64::MAX) + BellmanFr::one();
    let bits: Option<Vec<bool>> = a
        .get_value()
        .map(|v| (two_64 - v).to_le_bits().iter().map(|b| *b).collect());
    for i in 0..64 {
        let bit = AllocatedBit::alloc(&mut *cs, bits.as_ref().map(|b| b[i]))?;
        all = all + (coeff, bit.get_variable());
        result.push(bit);
        coeff = coeff.double();
    }
    let is_zero = is_zero(&mut *cs, a.clone())?;
    all = all + (two_64, is_zero.get_variable());
    cs.enforce(
        || "u64 neg check",
        |lc| lc + &all,
        |lc| lc + CS::one(),
        |lc| lc + (two_64, CS::one()) - a.get_variable(),
    );
    Ok(result)
}

// Convert number to u64 and negate
pub fn sum_u64<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: Vec<AllocatedBit>,
    b: Vec<AllocatedBit>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let sum = AllocatedNum::alloc(&mut *cs, || {
        let mut result = BellmanFr::zero();
        let mut coeff = BellmanFr::one();
        for (a_bit, b_bit) in a.iter().zip(b.iter()) {
            if a_bit.get_value().ok_or(SynthesisError::AssignmentMissing)? {
                result.add_assign(&coeff);
            }
            if b_bit.get_value().ok_or(SynthesisError::AssignmentMissing)? {
                result.add_assign(&coeff);
            }
            coeff = coeff.double();
        }
        Ok(result)
    })?;
    let mut coeff = BellmanFr::one();
    let mut all = LinearCombination::<BellmanFr>::zero();
    for i in 0..64 {
        all = all + (coeff, a[i].get_variable());
        all = all + (coeff, b[i].get_variable());
        coeff = coeff.double();
    }
    cs.enforce(
        || "sum u64s check",
        |lc| lc + &all,
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );
    Ok(sum)
}

pub fn bit_lt<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Boolean::and(&mut *cs, &a.not(), &b)
}

/*pub fn lte<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {\
    let a = to_u64(&mut *cs, a)?;
    let b_neg = to_u64_neg(&mut *cs, b)?;
    let c = a; // a + b_neg
    Ok(())
}*/

pub fn assert_equal<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: AllocatedBit,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {
    let enabled_value = enabled.get_value();
    let enabled_in_a = cs.alloc(
        || "",
        || {
            enabled_value
                .map(|e| {
                    if e {
                        a.get_value()
                    } else {
                        Some(BellmanFr::zero())
                    }
                })
                .unwrap_or(None)
                .ok_or(SynthesisError::AssignmentMissing)
        },
    )?;
    cs.enforce(
        || "enabled * a == enabled_in_a",
        |lc| lc + enabled.get_variable(),
        |lc| lc + a.get_variable(),
        |lc| lc + enabled_in_a,
    );
    cs.enforce(
        || "enabled * b == enabled_in_a",
        |lc| lc + enabled.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + enabled_in_a,
    );
    Ok(())
}
