use crate::common::Number;
use crate::BellmanFr;

use bazuka::zk::poseidon::params_for_arity;
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};

pub fn sbox<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &Number,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let a2 = a.mul(&mut *cs, &a)?;
    let a4 = a2.mul(&mut *cs, &a2)?;
    a.mul(&mut *cs, &a4.into())
}

pub fn add_constants<CS: ConstraintSystem<BellmanFr>>(vals: &mut [Number], const_offset: usize) {
    let params = params_for_arity(vals.len() - 1);
    for (i, val) in vals.iter_mut().enumerate() {
        val.add_constant::<CS>(params.round_constants[const_offset + i].into());
    }
}

pub fn partial_round<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    const_offset: usize,
    mut vals: Vec<Number>,
) -> Result<Vec<Number>, SynthesisError> {
    add_constants::<CS>(&mut vals, const_offset);

    vals[0] = sbox(&mut *cs, &vals[0])?.into();
    for i in 1..vals.len() {
        vals[i] = vals[i].clone().compress(&mut *cs)?.into();
    }

    product_mds(vals)
}

pub fn full_round<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    const_offset: usize,
    mut vals: Vec<Number>,
) -> Result<Vec<Number>, SynthesisError> {
    add_constants::<CS>(&mut vals, const_offset);

    for val in vals.iter_mut() {
        *val = sbox(&mut *cs, val)?.into();
    }

    product_mds(vals)
}

pub fn product_mds(vals: Vec<Number>) -> Result<Vec<Number>, SynthesisError> {
    let params = params_for_arity(vals.len() - 1);
    let mut result = vec![Number::zero(); vals.len()];
    for j in 0..vals.len() {
        for k in 0..vals.len() {
            let mat_val: BellmanFr = params.mds_constants[j][k].into();
            result[j].0 = result[j].0.clone() + (mat_val, &vals[k].0);
            result[j].1 = result[j].1.zip(vals[k].1).map(|(r, v)| r + v * mat_val);
        }
    }
    Ok(result)
}

pub fn poseidon<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    vals: &[&Number],
) -> Result<Number, SynthesisError> {
    let mut elems = vals.iter().map(|v| (*v).clone()).collect::<Vec<Number>>();
    elems.insert(0, Number::zero());

    let params = params_for_arity(elems.len() - 1);
    let mut const_offset = 0;

    for _ in 0..params.full_rounds / 2 {
        elems = full_round(&mut *cs, const_offset, elems)?;
        const_offset += elems.len();
    }

    for _ in 0..params.partial_rounds {
        elems = partial_round(&mut *cs, const_offset, elems)?;
        const_offset += elems.len();
    }

    for _ in 0..params.full_rounds / 2 {
        elems = full_round(&mut *cs, const_offset, elems)?;
        const_offset += elems.len();
    }

    Ok(elems[1].clone())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Bls12;
    use bazuka::zk::ZkScalar;
    use bellman::gadgets::num::AllocatedNum;
    use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
    use rand::rngs::OsRng;

    struct TestPoseidon4Circuit {
        pub a: Option<BellmanFr>,
        pub b: Option<BellmanFr>,
        pub c: Option<BellmanFr>,
        pub d: Option<BellmanFr>,
        pub e: Option<BellmanFr>,
        pub out1: Option<BellmanFr>,
        pub out2: Option<BellmanFr>,
        pub out3: Option<BellmanFr>,
        pub out4: Option<BellmanFr>,
        pub out5: Option<BellmanFr>,
    }

    impl Circuit<BellmanFr> for TestPoseidon4Circuit {
        fn synthesize<CS: ConstraintSystem<BellmanFr>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let out1 = AllocatedNum::alloc(&mut *cs, || {
                self.out1.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let out2 = AllocatedNum::alloc(&mut *cs, || {
                self.out2.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let out3 = AllocatedNum::alloc(&mut *cs, || {
                self.out3.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let out4 = AllocatedNum::alloc(&mut *cs, || {
                self.out4.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let out5 = AllocatedNum::alloc(&mut *cs, || {
                self.out5.ok_or(SynthesisError::AssignmentMissing)
            })?;
            out1.inputize(&mut *cs)?;
            out2.inputize(&mut *cs)?;
            out3.inputize(&mut *cs)?;
            out4.inputize(&mut *cs)?;
            out5.inputize(&mut *cs)?;

            let a =
                AllocatedNum::alloc(&mut *cs, || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b =
                AllocatedNum::alloc(&mut *cs, || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c =
                AllocatedNum::alloc(&mut *cs, || self.c.ok_or(SynthesisError::AssignmentMissing))?;
            let d =
                AllocatedNum::alloc(&mut *cs, || self.d.ok_or(SynthesisError::AssignmentMissing))?;
            let e =
                AllocatedNum::alloc(&mut *cs, || self.e.ok_or(SynthesisError::AssignmentMissing))?;

            let res1 = poseidon(&mut *cs, &[&a.clone().into()])?;
            let res2 = poseidon(&mut *cs, &[&a.clone().into(), &b.clone().into()])?;
            let res3 = poseidon(
                &mut *cs,
                &[&a.clone().into(), &b.clone().into(), &c.clone().into()],
            )?;
            let res4 = poseidon(
                &mut *cs,
                &[
                    &a.clone().into(),
                    &b.clone().into(),
                    &c.clone().into(),
                    &d.clone().into(),
                ],
            )?;
            let res5 = poseidon(
                &mut *cs,
                &[&a.into(), &b.into(), &c.into(), &d.into(), &e.into()],
            )?;
            cs.enforce(
                || "",
                |lc| lc + out1.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + res1.get_lc(),
            );
            cs.enforce(
                || "",
                |lc| lc + out2.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + res2.get_lc(),
            );
            cs.enforce(
                || "",
                |lc| lc + out3.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + res3.get_lc(),
            );
            cs.enforce(
                || "",
                |lc| lc + out4.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + res4.get_lc(),
            );
            cs.enforce(
                || "",
                |lc| lc + out5.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + res5.get_lc(),
            );
            Ok(())
        }
    }

    #[test]
    fn test_poseidon_circuit() {
        let params = {
            let c = TestPoseidon4Circuit {
                a: None,
                b: None,
                c: None,
                d: None,
                e: None,
                out1: None,
                out2: None,
                out3: None,
                out4: None,
                out5: None,
            };
            groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
        };

        let pvk = groth16::prepare_verifying_key(&params.vk);

        let expecteds = (0..5)
            .map(|i| {
                bazuka::zk::poseidon::poseidon(
                    &[
                        ZkScalar::from(123),
                        ZkScalar::from(234),
                        ZkScalar::from(345),
                        ZkScalar::from(456),
                        ZkScalar::from(567),
                    ]
                    .into_iter()
                    .take(i + 1)
                    .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>();

        let c = TestPoseidon4Circuit {
            a: Some(ZkScalar::from(123).into()),
            b: Some(ZkScalar::from(234).into()),
            c: Some(ZkScalar::from(345).into()),
            d: Some(ZkScalar::from(456).into()),
            e: Some(ZkScalar::from(567).into()),
            out1: Some(expecteds[0].into()),
            out2: Some(expecteds[1].into()),
            out3: Some(expecteds[2].into()),
            out4: Some(expecteds[3].into()),
            out5: Some(expecteds[4].into()),
        };
        let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();
        assert!(groth16::verify_proof(
            &pvk,
            &proof,
            &expecteds
                .iter()
                .map(|v| v.clone().into())
                .collect::<Vec<BellmanFr>>()
        )
        .is_ok());

        let c = TestPoseidon4Circuit {
            a: Some(ZkScalar::from(123).into()),
            b: Some(ZkScalar::from(234).into()),
            c: Some(ZkScalar::from(345).into()),
            d: Some(ZkScalar::from(457).into()),
            e: Some(ZkScalar::from(567).into()),
            out1: Some(expecteds[0].into()),
            out2: Some(expecteds[1].into()),
            out3: Some(expecteds[2].into()),
            out4: Some(expecteds[3].into()),
            out5: Some(expecteds[4].into()),
        };
        let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();
        assert!(!groth16::verify_proof(
            &pvk,
            &proof,
            &expecteds
                .iter()
                .map(|v| v.clone().into())
                .collect::<Vec<BellmanFr>>()
        )
        .is_ok());
    }
}
