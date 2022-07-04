use crate::BellmanFr;
use crate::{common, poseidon};

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};

fn merge_hash_poseidon4<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: (Boolean, Boolean),
    v: AllocatedNum<BellmanFr>,
    p0: AllocatedNum<BellmanFr>,
    p1: AllocatedNum<BellmanFr>,
    p2: AllocatedNum<BellmanFr>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let and = Boolean::and(&mut *cs, &select.0, &select.1)?;
    let or = Boolean::and(&mut *cs, &select.0.not(), &select.1.not())?.not();

    // v0 == s0_or_s1 ? p0 : v
    let (_, v0) = AllocatedNum::conditionally_reverse(&mut *cs, &p0, &v, &or)?;

    //v1p == s0 ? v : p0
    let (_, v1p) = AllocatedNum::conditionally_reverse(&mut *cs, &v, &p0, &select.0)?;

    //v1 == s1 ? p1 : v1p
    let (_, v1) = AllocatedNum::conditionally_reverse(&mut *cs, &p1, &v1p, &select.1)?;

    //v2p == s0 ? p2 : v
    let (_, v2p) = AllocatedNum::conditionally_reverse(&mut *cs, &p2, &v, &select.0)?;

    //v2 == s1 ? v2p : p1
    let (_, v2) = AllocatedNum::conditionally_reverse(&mut *cs, &v2p, &p1, &select.1)?;

    //v3 == s0_and_s1 ? v : p2
    let (_, v3) = AllocatedNum::conditionally_reverse(&mut *cs, &v, &p2, &and)?;

    poseidon::groth16::poseidon4(cs, v0, v1, v2, v3)
}

fn merge_hash<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: Boolean,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let (l, r) = AllocatedNum::conditionally_reverse(&mut *cs, &a, &b, &select)?;
    poseidon::groth16::poseidon(cs, &[l, r])
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
