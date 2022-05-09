use crate::mimc;
use crate::BellmanFr;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};

fn merge_hash<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: Boolean,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let l = mimc::groth16::double_mimc(cs, a.clone(), b.clone())?;
    let r = mimc::groth16::double_mimc(cs, b.clone(), a.clone())?;
    let (l, _) = AllocatedNum::conditionally_reverse(&mut *cs, &l, &r, &select)?;
    Ok(l)
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

fn assert_equal<'a, CS: ConstraintSystem<BellmanFr>>(
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

pub fn check_proof<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: AllocatedBit,
    index: AllocatedNum<BellmanFr>,
    val: AllocatedNum<BellmanFr>,
    proof: Vec<AllocatedNum<BellmanFr>>,
    root: AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {
    let new_root = calc_root(&mut *cs, index, val, proof)?;
    assert_equal(cs, enabled, root, new_root)?;
    Ok(())
}
