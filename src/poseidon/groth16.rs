use crate::BellmanFr;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};

pub struct WrappedLc(LinearCombination<BellmanFr>, Option<BellmanFr>);

pub fn sbox<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    sum: WrappedLc,
    a: AllocatedNum<BellmanFr>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let a_sum_2 = AllocatedNum::alloc(&mut *cs, || {
        a.get_value()
            .zip(sum.1)
            .map(|(v, sum_val)| (v + sum_val).square())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "",
        |lc| lc + a.get_variable() + &sum.0,
        |lc| lc + a.get_variable() + &sum.0,
        |lc| lc + a_sum_2.get_variable(),
    );
    let a_sum_4 = a_sum_2.mul(&mut *cs, &a_sum_2)?;
    let a_sum_5 = AllocatedNum::alloc(&mut *cs, || {
        a_sum_4
            .get_value()
            .zip(a.get_value())
            .zip(sum.1)
            .map(|((a_sum_4, a), sum_val)| a_sum_4 * (a + sum_val))
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "",
        |lc| lc + a_sum_4.get_variable(),
        |lc| lc + a.get_variable() + &sum.0,
        |lc| lc + a_sum_5.get_variable(),
    );
    Ok(a_sum_5)
}

pub fn product_mds<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    vals: [WrappedLc; 5],
) -> Result<[WrappedLc; 5], SynthesisError> {
    Ok(vals)
}

pub fn poseidon4<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
    c: AllocatedNum<BellmanFr>,
    d: AllocatedNum<BellmanFr>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let mut elems = [
        WrappedLc(
            LinearCombination::<BellmanFr>::zero(),
            Some(BellmanFr::zero()),
        ),
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + a.get_variable(),
            a.get_value(),
        ),
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + b.get_variable(),
            b.get_value(),
        ),
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + c.get_variable(),
            c.get_value(),
        ),
        WrappedLc(
            LinearCombination::<BellmanFr>::zero() + d.get_variable(),
            d.get_value(),
        ),
    ];
    elems = product_mds(&mut *cs, elems)?;
    Ok(a)
}

pub fn poseidon<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    vals: &[AllocatedNum<BellmanFr>],
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    unimplemented!();
}
