use crate::common::groth16::Number;
use crate::BellmanFr;
use crate::{common, poseidon};

use crate::common::groth16::UnsignedInteger;
use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};

fn merge_hash_poseidon4<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: (&AllocatedBit, &AllocatedBit),
    v: &Number,
    p: &[AllocatedNum<BellmanFr>; 3],
) -> Result<Number, SynthesisError> {
    let select = (Boolean::Is(select.0.clone()), Boolean::Is(select.1.clone()));

    let and = Boolean::and(&mut *cs, &select.0, &select.1)?;
    let or = Boolean::and(&mut *cs, &select.0.not(), &select.1.not())?.not();

    // v0 == s0_or_s1 ? p[0] : v
    let v0 = common::groth16::mux(&mut *cs, &or, v, &p[0].clone().into())?;

    //v1p == s0 ? v : p[0]
    let v1p = common::groth16::mux(&mut *cs, &select.0, &p[0].clone().into(), v)?;

    //v1 == s1 ? p[1] : v1p
    let v1 = common::groth16::mux(&mut *cs, &select.1, &v1p.into(), &p[1].clone().into())?;

    //v2p == s0 ? p[2] : v
    let v2p = common::groth16::mux(&mut *cs, &select.0, v, &p[2].clone().into())?;

    //v2 == s1 ? v2p : p[1]
    let v2 = common::groth16::mux(&mut *cs, &select.1, &p[1].clone().into(), &v2p.into())?;

    //v3 == s0_and_s1 ? v : p[2]
    let v3 = common::groth16::mux(&mut *cs, &and, &p[2].clone().into(), &v)?;

    poseidon::groth16::poseidon(cs, &[&v0.into(), &v1.into(), &v2.into(), &v3.into()])
}

pub fn calc_root_poseidon4<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    index: &UnsignedInteger,
    val: &Number,
    proof: &[[AllocatedNum<BellmanFr>; 3]],
) -> Result<Number, SynthesisError> {
    assert_eq!(index.bits().len(), proof.len() * 2);
    let mut curr = val.clone();
    for (p, dir) in proof.into_iter().zip(index.bits().chunks(2)) {
        curr = merge_hash_poseidon4(&mut *cs, (&dir[0], &dir[1]), &curr, p)?;
    }
    Ok(curr)
}

pub fn check_proof_poseidon4<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: &Boolean,
    index: &UnsignedInteger,
    val: &Number,
    proof: &[[AllocatedNum<BellmanFr>; 3]],
    root: &Number,
) -> Result<(), SynthesisError> {
    let new_root = calc_root_poseidon4(&mut *cs, index, val, proof)?;
    common::groth16::assert_equal_if_enabled(cs, enabled, root, &new_root)?;
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Bls12;
    use bazuka::zk::{
        PoseidonHasher, ZkDataLocator, ZkDeltaPairs, ZkScalar, ZkStateBuilder, ZkStateModel,
    };
    use bellman::gadgets::num::AllocatedNum;
    use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
    use ff::Field;
    use rand::rngs::OsRng;

    struct TestPoseidon4MerkleProofCircuit {
        index: Option<BellmanFr>,
        val: Option<BellmanFr>,
        root: Option<BellmanFr>,
        proof: Vec<[Option<BellmanFr>; 3]>,
    }

    impl Circuit<BellmanFr> for TestPoseidon4MerkleProofCircuit {
        fn synthesize<CS: ConstraintSystem<BellmanFr>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let index = AllocatedNum::alloc(&mut *cs, || {
                self.index.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let val = AllocatedNum::alloc(&mut *cs, || {
                self.val.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let root = AllocatedNum::alloc(&mut *cs, || {
                self.root.ok_or(SynthesisError::AssignmentMissing)
            })?;
            index.inputize(&mut *cs)?;
            val.inputize(&mut *cs)?;
            root.inputize(&mut *cs)?;

            let mut proof = Vec::new();
            for p in self.proof {
                proof.push([
                    AllocatedNum::alloc(&mut *cs, || {
                        p[0].ok_or(SynthesisError::AssignmentMissing)
                    })?,
                    AllocatedNum::alloc(&mut *cs, || {
                        p[1].ok_or(SynthesisError::AssignmentMissing)
                    })?,
                    AllocatedNum::alloc(&mut *cs, || {
                        p[2].ok_or(SynthesisError::AssignmentMissing)
                    })?,
                ]);
            }

            let enabled = Boolean::Is(AllocatedBit::alloc(&mut *cs, Some(true))?);
            let index = UnsignedInteger::constrain(&mut *cs, index.into(), 8)?;

            check_proof_poseidon4(
                &mut *cs,
                &enabled,
                &index.into(),
                &val.into(),
                &proof,
                &root.into(),
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_poseidon4_merkle_proofs() {
        let params = {
            let c = TestPoseidon4MerkleProofCircuit {
                index: None,
                val: None,
                proof: vec![[None; 3]; 4],
                root: None,
            };
            groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
        };

        let pvk = groth16::prepare_verifying_key(&params.vk);

        let model = ZkStateModel::List {
            log4_size: 4,
            item_type: Box::new(ZkStateModel::Scalar),
        };
        let mut builder = ZkStateBuilder::<PoseidonHasher>::new(model);
        for i in 0..256 {
            builder
                .batch_set(&ZkDeltaPairs(
                    [(ZkDataLocator(vec![i]), Some(ZkScalar::from(i as u64)))].into(),
                ))
                .unwrap();
        }
        for i in 0..256 {
            let proof: Vec<[Option<BellmanFr>; 3]> = builder
                .prove(ZkDataLocator(vec![]), i)
                .unwrap()
                .into_iter()
                .map(|p| [Some(p[0].into()), Some(p[1].into()), Some(p[2].into())])
                .collect();

            let index = ZkScalar::from(i as u64);
            let val = ZkScalar::from(i as u64);
            let root = builder.get(ZkDataLocator(vec![])).unwrap();

            let c = TestPoseidon4MerkleProofCircuit {
                index: Some(index.into()),
                val: Some(val.into()),
                proof,
                root: Some(root.into()),
            };
            let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();
            assert!(
                groth16::verify_proof(&pvk, &proof, &[index.into(), val.into(), root.into()])
                    .is_ok()
            );

            assert!(!groth16::verify_proof(
                &pvk,
                &proof,
                &[index.into(), val.into(), root.double().into()]
            )
            .is_ok());
        }
    }
}
