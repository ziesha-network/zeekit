use crate::BellmanFr;

use bazuka::zk::poseidon4::{MDS_MATRIX, ROUNDSF, ROUNDSP, ROUND_CONSTANTS};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};

#[derive(Clone)]
pub struct WrappedLc(LinearCombination<BellmanFr>, Option<BellmanFr>);
impl WrappedLc {
    fn add_assign<CS: ConstraintSystem<BellmanFr>>(&mut self, num: BellmanFr) {
        self.0 = self.0.clone() + (num, CS::one());
        self.1 = self.1.map(|v| v + num);
    }
    fn zero() -> WrappedLc {
        WrappedLc(
            LinearCombination::<BellmanFr>::zero(),
            Some(BellmanFr::zero()),
        )
    }
}

pub fn sbox<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: WrappedLc,
) -> Result<WrappedLc, SynthesisError> {
    let a2 = AllocatedNum::alloc(&mut *cs, || {
        a.1.map(|v| v.square())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "",
        |lc| lc + &a.0,
        |lc| lc + &a.0,
        |lc| lc + a2.get_variable(),
    );
    let a4 = a2.mul(&mut *cs, &a2)?;
    let a5 = AllocatedNum::alloc(&mut *cs, || {
        a4.get_value()
            .zip(a.1)
            .map(|(a4, a)| a4 * a)
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "",
        |lc| lc + a4.get_variable(),
        |lc| lc + &a.0,
        |lc| lc + a5.get_variable(),
    );
    Ok(WrappedLc(
        LinearCombination::<BellmanFr>::zero() + a5.get_variable(),
        a5.get_value(),
    ))
}

pub fn add_constants<CS: ConstraintSystem<BellmanFr>>(
    vals: &mut [WrappedLc; 5],
    const_offset: usize,
) {
    for i in 0..5 {
        vals[i].add_assign::<CS>(ROUND_CONSTANTS[const_offset + i].into());
    }
}

pub fn partial_round<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    const_offset: usize,
    mut vals: [WrappedLc; 5],
) -> Result<[WrappedLc; 5], SynthesisError> {
    add_constants::<CS>(&mut vals, const_offset);

    vals[0] = sbox(&mut *cs, vals[0].clone())?;

    product_mds(vals)
}

pub fn full_round<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    const_offset: usize,
    mut vals: [WrappedLc; 5],
) -> Result<[WrappedLc; 5], SynthesisError> {
    add_constants::<CS>(&mut vals, const_offset);

    for i in 0..5 {
        vals[i] = sbox(&mut *cs, vals[i].clone())?;
    }

    product_mds(vals)
}

pub fn product_mds(vals: [WrappedLc; 5]) -> Result<[WrappedLc; 5], SynthesisError> {
    let mut result = [
        WrappedLc::zero(),
        WrappedLc::zero(),
        WrappedLc::zero(),
        WrappedLc::zero(),
        WrappedLc::zero(),
    ];
    for j in 0..5 {
        for k in 0..5 {
            let mat_val: BellmanFr = MDS_MATRIX[j][k].into();
            result[j].0 = result[j].0.clone() + (mat_val, &vals[k].0);
            result[j].1.zip(vals[k].1).map(|(r, v)| r + v * mat_val);
        }
    }
    Ok(result)
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
    let mut const_offset = 0;

    for _ in 0..ROUNDSF / 2 {
        elems = full_round(&mut *cs, const_offset, elems)?;
        const_offset += 5;
    }

    for _ in 0..ROUNDSP {
        const_offset += 5;
    }

    for _ in 0..ROUNDSF / 2 {
        const_offset += 5;
    }

    Ok(a)
}

#[allow(dead_code)]
pub fn poseidon<'a, CS: ConstraintSystem<BellmanFr>>(
    _cs: &mut CS,
    _vals: &[AllocatedNum<BellmanFr>],
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    unimplemented!();
}
