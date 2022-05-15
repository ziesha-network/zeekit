use crate::BellmanFr;
use crate::{common, mimc};

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};

fn merge_hash<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: Boolean,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let (l, r) = AllocatedNum::conditionally_reverse(&mut *cs, &a, &b, &select)?;
    mimc::groth16::double_mimc(cs, l, r)
}

pub fn calc_root<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    index: AllocatedNum<BellmanFr>,
    val: AllocatedNum<BellmanFr>,
    proof: Vec<AllocatedNum<BellmanFr>>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let selectors = index.to_bits_le(&mut *cs)?;
    let mut curr = val.clone();
    for (p, dir) in proof.into_iter().zip(selectors.into_iter()) {
        curr = merge_hash(&mut *cs, dir, curr, p)?;
    }
    Ok(curr)
}

pub fn check_proof<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: AllocatedBit,
    index: AllocatedNum<BellmanFr>,
    val: AllocatedNum<BellmanFr>,
    proof: Vec<AllocatedNum<BellmanFr>>,
    root: AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {
    let new_root = calc_root(&mut *cs, index, val, proof)?;
    common::groth16::assert_equal(cs, enabled, root, new_root)?;
    Ok(())
}
