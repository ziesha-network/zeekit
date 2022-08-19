use crate::BellmanFr;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::{Field, PrimeFieldBits};
use std::ops::AddAssign;

#[derive(Clone)]
pub struct WrappedLc(pub LinearCombination<BellmanFr>, pub Option<BellmanFr>);
impl WrappedLc {
    pub fn get_lc(&self) -> &LinearCombination<BellmanFr> {
        &self.0
    }
    pub fn get_value(&self) -> Option<BellmanFr> {
        self.1
    }
    pub fn add_constant<CS: ConstraintSystem<BellmanFr>>(&mut self, num: BellmanFr) {
        self.0 = self.0.clone() + (num, CS::one());
        self.1 = self.1.map(|v| v + num);
    }
    pub fn add_num(&mut self, num: &AllocatedNum<BellmanFr>) {
        self.0 = self.0.clone() + num.get_variable();
        self.1 = if let Some(v) = self.1 {
            num.get_value().map(|n| n + v)
        } else {
            None
        };
    }
    pub fn alloc_num(a: AllocatedNum<BellmanFr>) -> WrappedLc {
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + a.get_variable(),
            a.get_value(),
        )
    }
    pub fn constant<CS: ConstraintSystem<BellmanFr>>(v: BellmanFr) -> WrappedLc {
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + (v, CS::one()),
            Some(v),
        )
    }
    pub fn zero() -> WrappedLc {
        WrappedLc(
            LinearCombination::<BellmanFr>::zero(),
            Some(BellmanFr::zero()),
        )
    }
}

pub fn mux<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: &Boolean,
    a: &WrappedLc,
    b: &WrappedLc,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    Ok(match select {
        Boolean::Is(s) => {
            let ret = AllocatedNum::alloc(&mut *cs, || {
                s.get_value()
                    .and_then(|s| if s { b.get_value() } else { a.get_value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "(a - b) * s == a - ret",
                |lc| lc + &a.0 - &b.0,
                |lc| lc + s.get_variable(),
                |lc| lc + &a.0 - ret.get_variable(),
            );
            ret
        }
        Boolean::Not(not_s) => {
            let ret = AllocatedNum::alloc(&mut *cs, || {
                not_s
                    .get_value()
                    .and_then(|not_s| if not_s { a.get_value() } else { b.get_value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "(b - a) * not_s == b - ret",
                |lc| lc + &b.0 - &a.0,
                |lc| lc + not_s.get_variable(),
                |lc| lc + &b.0 - ret.get_variable(),
            );
            ret
        }
        Boolean::Constant(_) => {
            unimplemented!();
        }
    })
}

// Check if a number is zero, 2 constraints
pub fn is_zero<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
) -> Result<AllocatedBit, SynthesisError> {
    is_equal(cs, &WrappedLc::alloc_num(a), &WrappedLc::zero())
}

// Check a == b, two constraints
pub fn is_equal<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &WrappedLc,
    b: &WrappedLc,
) -> Result<AllocatedBit, SynthesisError> {
    let out = AllocatedBit::alloc(
        &mut *cs,
        a.get_value().zip(b.get_value()).map(|(a, b)| a == b),
    )?;
    let inv = AllocatedNum::alloc(&mut *cs, || {
        a.get_value()
            .zip(b.get_value())
            .map(|(a, b)| {
                if (a - b).is_zero().into() {
                    BellmanFr::zero()
                } else {
                    (a - b).invert().unwrap()
                }
            })
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "calc out",
        |lc| lc - a.get_lc() + b.get_lc(),
        |lc| lc + inv.get_variable(),
        |lc| lc + out.get_variable() - CS::one(),
    );
    cs.enforce(
        || "calc out",
        |lc| lc + out.get_variable(),
        |lc| lc + a.get_lc() - b.get_lc(),
        |lc| lc,
    );
    Ok(out)
}

pub fn from_bits<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    bits: Vec<AllocatedBit>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let sum = AllocatedNum::alloc(&mut *cs, || {
        let mut result = BellmanFr::zero();
        let mut coeff = BellmanFr::one();
        for bit in bits.iter() {
            if bit.get_value().ok_or(SynthesisError::AssignmentMissing)? {
                result.add_assign(&coeff);
            }
            coeff = coeff.double();
        }
        Ok(result)
    })?;
    let mut coeff = BellmanFr::one();
    let mut all = LinearCombination::<BellmanFr>::zero();
    for bit in bits.iter() {
        all = all + (coeff, bit.get_variable());
        coeff = coeff.double();
    }
    cs.enforce(
        || "sum check",
        |lc| lc + &all,
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );
    Ok(sum)
}

// Convert number to binary repr, bits + 1 constraints
pub fn to_bits<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
    num_bits: usize,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let mut result = Vec::new();
    let mut coeff = BellmanFr::one();
    let mut all = LinearCombination::<BellmanFr>::zero();
    let bits: Option<Vec<bool>> = a
        .get_value()
        .map(|v| v.to_le_bits().iter().map(|b| *b).collect());
    for i in 0..num_bits {
        let bit = AllocatedBit::alloc(&mut *cs, bits.as_ref().map(|b| b[i]))?;
        all = all + (coeff, bit.get_variable());
        result.push(bit);
        coeff = coeff.double();
    }
    cs.enforce(
        || "check",
        |lc| lc + &all,
        |lc| lc + CS::one(),
        |lc| lc + a.get_variable(),
    );
    Ok(result)
}

// Convert number to binary repr and negate
pub fn to_bits_neg<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
    num_bits: usize,
) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let mut result = Vec::new();
    let mut coeff = BellmanFr::one();
    let mut all = LinearCombination::<BellmanFr>::zero();
    let two_bits = BellmanFr::from(2).pow_vartime(&[num_bits as u64, 0, 0, 0]);
    let bits: Option<Vec<bool>> = a
        .get_value()
        .map(|v| (two_bits - v).to_le_bits().iter().map(|b| *b).collect());
    for i in 0..num_bits {
        let bit = AllocatedBit::alloc(&mut *cs, bits.as_ref().map(|b| b[i]))?;
        all = all + (coeff, bit.get_variable());
        result.push(bit);
        coeff = coeff.double();
    }
    let is_zero = is_zero(&mut *cs, a.clone())?;
    all = all + (two_bits, is_zero.get_variable());
    cs.enforce(
        || "neg check",
        |lc| lc + &all,
        |lc| lc + CS::one(),
        |lc| lc + (two_bits, CS::one()) - a.get_variable(),
    );
    Ok(result)
}

// Convert number to u64 and negate
pub fn sum_bits<CS: ConstraintSystem<BellmanFr>>(
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
    for (a_bit, b_bit) in a.iter().zip(b.iter()) {
        all = all + (coeff, a_bit.get_variable());
        all = all + (coeff, b_bit.get_variable());
        coeff = coeff.double();
    }
    cs.enforce(
        || "sum check",
        |lc| lc + &all,
        |lc| lc + CS::one(),
        |lc| lc + sum.get_variable(),
    );
    Ok(sum)
}

// ~200 constraints
pub fn lte<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<AllocatedBit, SynthesisError> {
    let a = to_bits(&mut *cs, a, 64)?;
    let b_neg = to_bits_neg(&mut *cs, b, 64)?;
    let c = sum_bits(&mut *cs, a, b_neg)?;
    let c_bits = to_bits(&mut *cs, c, 65)?;
    Ok(c_bits[63].clone())
}

pub fn assert_equal<CS: ConstraintSystem<BellmanFr>>(
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::Bls12;
    use bellman::gadgets::num::AllocatedNum;
    use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
    use ff::Field;
    use rand::rngs::OsRng;

    #[derive(Clone)]
    struct TestIsEqualCircuit {
        a: Option<BellmanFr>,
        b: Option<BellmanFr>,
        is_equal: Option<bool>,
    }

    impl Circuit<BellmanFr> for TestIsEqualCircuit {
        fn synthesize<CS: ConstraintSystem<BellmanFr>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let a =
                AllocatedNum::alloc(&mut *cs, || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            a.inputize(&mut *cs)?;
            let b =
                AllocatedNum::alloc(&mut *cs, || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            b.inputize(&mut *cs)?;
            let eq = AllocatedNum::alloc(&mut *cs, || {
                self.is_equal
                    .map(|b| {
                        if b {
                            BellmanFr::one()
                        } else {
                            BellmanFr::zero()
                        }
                    })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            eq.inputize(&mut *cs)?;

            let res = is_equal(&mut *cs, &WrappedLc::alloc_num(a), &WrappedLc::alloc_num(b))?;
            println!("{:?} {:?}", res.get_value(), eq.get_value());
            cs.enforce(
                || "",
                |lc| lc + res.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + eq.get_variable(),
            );

            Ok(())
        }
    }

    #[test]
    fn test_is_equal_circuit() {
        let params = {
            let c = TestIsEqualCircuit {
                a: None,
                b: None,
                is_equal: None,
            };
            groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
        };

        let pvk = groth16::prepare_verifying_key(&params.vk);

        for (a, b, eq, expected) in [
            (123, 123, false, false),
            (123, 123, true, true),
            (123, 234, false, true),
            (123, 234, true, false),
        ] {
            let c = TestIsEqualCircuit {
                a: Some(BellmanFr::from(a)),
                b: Some(BellmanFr::from(b)),
                is_equal: Some(eq),
            };
            let proof = groth16::create_random_proof(c.clone(), &params, &mut OsRng).unwrap();
            assert_eq!(
                groth16::verify_proof(
                    &pvk,
                    &proof,
                    &[
                        c.a.unwrap(),
                        c.b.unwrap(),
                        c.is_equal
                            .map(|b| if b {
                                BellmanFr::one()
                            } else {
                                BellmanFr::zero()
                            })
                            .unwrap()
                    ]
                )
                .is_ok(),
                expected
            );
        }
    }
}
