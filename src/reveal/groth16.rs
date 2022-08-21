use crate::common::groth16::Number;
use crate::poseidon::groth16::{poseidon, poseidon4};
use crate::BellmanFr;
use bazuka::zk::ZkStateModel;
use bellman::{ConstraintSystem, SynthesisError};

#[derive(Clone)]
pub enum AllocatedState {
    Value(Number),
    Children(Vec<AllocatedState>),
}

pub fn reveal<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    state_model: ZkStateModel,
    state: AllocatedState,
) -> Result<Number, SynthesisError> {
    match state_model {
        ZkStateModel::Scalar => {
            if let AllocatedState::Value(v) = state {
                return Ok(v);
            } else {
                panic!("Invalid state!");
            }
        }
        ZkStateModel::Struct { field_types } => {
            let mut vals = Vec::new();
            if let AllocatedState::Children(children) = state {
                for (field_type, field_value) in field_types.iter().zip(children.into_iter()) {
                    vals.push(reveal(&mut *cs, field_type.clone(), field_value)?);
                }
            } else {
                panic!("Invalid state!");
            }
            poseidon(&mut *cs, &vals)
        }
        ZkStateModel::List {
            log4_size,
            item_type,
        } => {
            let mut leaves = Vec::new();
            if let AllocatedState::Children(children) = state {
                for i in 0..1 << (2 * log4_size) {
                    leaves.push(reveal(&mut *cs, *item_type.clone(), children[i].clone())?);
                }
            } else {
                panic!("Invalid state!");
            }
            while leaves.len() != 1 {
                let mut new_leaves = Vec::new();
                for chunk in leaves.chunks(4) {
                    let hash = poseidon4(
                        &mut *cs,
                        chunk[0].clone(),
                        chunk[1].clone(),
                        chunk[2].clone(),
                        chunk[3].clone(),
                    )?;
                    new_leaves.push(hash);
                }
                leaves = new_leaves;
            }
            Ok(leaves[0].clone())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Bls12;
    use bazuka::core::ZkHasher;
    use bazuka::zk::{ZkDataLocator, ZkDataPairs, ZkScalar, ZkStateBuilder};
    use bellman::gadgets::num::AllocatedNum;
    use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
    use rand::rngs::OsRng;

    struct TestRevealCircuit {
        state_model: ZkStateModel,
        data: Option<ZkDataPairs>,
        out: Option<BellmanFr>,
    }

    fn extract_witnesses<CS: ConstraintSystem<BellmanFr>>(
        cs: &mut CS,
        state_model: ZkStateModel,
        locator: ZkDataLocator,
        pairs: &Option<ZkDataPairs>,
    ) -> Result<AllocatedState, SynthesisError> {
        match state_model {
            ZkStateModel::Scalar => {
                let num = AllocatedNum::alloc(&mut *cs, || {
                    if let Some(pairs) = pairs {
                        Ok(pairs
                            .0
                            .get(&locator)
                            .cloned()
                            .unwrap_or_else(|| state_model.compress_default::<ZkHasher>())
                            .into())
                    } else {
                        Err(SynthesisError::AssignmentMissing)
                    }
                })?;
                Ok(AllocatedState::Value(num.into()))
            }
            ZkStateModel::Struct { field_types } => {
                let mut children = Vec::new();
                for (i, field_type) in field_types.into_iter().enumerate() {
                    children.push(extract_witnesses(
                        &mut *cs,
                        field_type,
                        locator.index(i as u32),
                        pairs,
                    )?);
                }
                Ok(AllocatedState::Children(children))
            }
            ZkStateModel::List {
                log4_size,
                item_type,
            } => {
                let mut children = Vec::new();
                for i in 0..(1 << (2 * log4_size)) {
                    children.push(extract_witnesses(
                        &mut *cs,
                        *item_type.clone(),
                        locator.index(i as u32),
                        pairs,
                    )?);
                }
                Ok(AllocatedState::Children(children))
            }
        }
    }

    impl Circuit<BellmanFr> for TestRevealCircuit {
        fn synthesize<CS: ConstraintSystem<BellmanFr>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let out = AllocatedNum::alloc(&mut *cs, || {
                self.out.ok_or(SynthesisError::AssignmentMissing)
            })?;
            out.inputize(&mut *cs)?;

            let alloc_state = extract_witnesses(
                &mut *cs,
                self.state_model.clone(),
                ZkDataLocator(vec![]),
                &self.data,
            )?;

            let root = reveal(&mut *cs, self.state_model.clone(), alloc_state)?;

            cs.enforce(
                || "",
                |lc| lc + root.get_lc(),
                |lc| lc + CS::one(),
                |lc| lc + out.get_variable(),
            );

            Ok(())
        }
    }

    #[test]
    fn test_reveal_circuit() {
        let state_model = ZkStateModel::Struct {
            field_types: vec![
                ZkStateModel::Scalar,
                ZkStateModel::List {
                    item_type: Box::new(ZkStateModel::Scalar),
                    log4_size: 2,
                },
                ZkStateModel::Scalar,
                ZkStateModel::Scalar,
            ],
        };
        let params = {
            let c = TestRevealCircuit {
                state_model: state_model.clone(),
                data: None,
                out: None,
            };
            groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
        };

        let pvk = groth16::prepare_verifying_key(&params.vk);

        let data = ZkDataPairs(
            [
                (ZkDataLocator(vec![1, 2]), ZkScalar::from(10)),
                (ZkDataLocator(vec![1, 4]), ZkScalar::from(10)),
                (ZkDataLocator(vec![1, 10]), ZkScalar::from(15)),
                (ZkDataLocator(vec![0]), ZkScalar::from(123)),
            ]
            .into(),
        );

        let mut builder = ZkStateBuilder::<ZkHasher>::new(state_model.clone());
        builder.batch_set(&data.as_delta()).unwrap();
        let expected = builder.compress().unwrap().state_hash;

        let c = TestRevealCircuit {
            state_model: state_model.clone(),
            data: Some(data),
            out: Some(expected.into()),
        };
        let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();
        assert!(groth16::verify_proof(&pvk, &proof, &[expected.into()]).is_ok());
    }
}
