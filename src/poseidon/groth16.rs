use crate::common::groth16::Number;
use crate::BellmanFr;

use bazuka::zk::poseidon4::{MDS_MATRIX, ROUNDSF, ROUNDSP, ROUND_CONSTANTS};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};

pub fn sbox<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: Number,
) -> Result<Number, SynthesisError> {
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
    Ok(Number(
        LinearCombination::<BellmanFr>::zero() + a5.get_variable(),
        a5.get_value(),
    ))
}

pub fn add_constants<CS: ConstraintSystem<BellmanFr>>(vals: &mut [Number; 5], const_offset: usize) {
    for i in 0..5 {
        vals[i].add_constant::<CS>(ROUND_CONSTANTS[const_offset + i].into());
    }
}

pub fn partial_round<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    const_offset: usize,
    mut vals: [Number; 5],
) -> Result<[Number; 5], SynthesisError> {
    add_constants::<CS>(&mut vals, const_offset);

    vals[0] = sbox(&mut *cs, vals[0].clone())?;
    for i in 1..5 {
        vals[i] = vals[i].clone().alloc(&mut *cs)?.into();
    }

    product_mds(vals)
}

pub fn full_round<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    const_offset: usize,
    mut vals: [Number; 5],
) -> Result<[Number; 5], SynthesisError> {
    add_constants::<CS>(&mut vals, const_offset);

    for i in 0..5 {
        vals[i] = sbox(&mut *cs, vals[i].clone())?;
    }

    product_mds(vals)
}

pub fn product_mds(vals: [Number; 5]) -> Result<[Number; 5], SynthesisError> {
    let mut result = [
        Number::zero(),
        Number::zero(),
        Number::zero(),
        Number::zero(),
        Number::zero(),
    ];
    for j in 0..5 {
        for k in 0..5 {
            let mat_val: BellmanFr = MDS_MATRIX[j][k].into();
            result[j].0 = result[j].0.clone() + (mat_val, &vals[k].0);
            result[j].1 = result[j].1.zip(vals[k].1).map(|(r, v)| r + v * mat_val);
        }
    }
    Ok(result)
}

pub fn poseidon4<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: Number,
    b: Number,
    c: Number,
    d: Number,
) -> Result<Number, SynthesisError> {
    let mut elems = [Number::zero(), a, b, c, d];
    let mut const_offset = 0;

    for _ in 0..ROUNDSF / 2 {
        elems = full_round(&mut *cs, const_offset, elems)?;
        const_offset += 5;
    }

    for _ in 0..ROUNDSP {
        elems = partial_round(&mut *cs, const_offset, elems)?;
        const_offset += 5;
    }

    for _ in 0..ROUNDSF / 2 {
        elems = full_round(&mut *cs, const_offset, elems)?;
        const_offset += 5;
    }

    Ok(elems[1].clone())
}

pub fn poseidon<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    vals: &[Number],
) -> Result<Number, SynthesisError> {
    let mut first = vals[0].clone();

    for chunk in vals[1..].chunks(3) {
        first = match chunk.len() {
            1 => poseidon4(
                &mut *cs,
                first.clone(),
                chunk[0].clone(),
                Number::zero(),
                Number::zero(),
            )?,
            2 => poseidon4(
                &mut *cs,
                first.clone(),
                chunk[0].clone(),
                chunk[1].clone(),
                Number::zero(),
            )?,
            3 => poseidon4(
                &mut *cs,
                first.clone(),
                chunk[0].clone(),
                chunk[1].clone(),
                chunk[2].clone(),
            )?,
            _ => panic!(),
        };
    }

    Ok(first)
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
        pub out: Option<BellmanFr>,
    }

    impl Circuit<BellmanFr> for TestPoseidon4Circuit {
        fn synthesize<CS: ConstraintSystem<BellmanFr>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let out = AllocatedNum::alloc(&mut *cs, || {
                self.out.ok_or(SynthesisError::AssignmentMissing)
            })?;
            out.inputize(&mut *cs)?;
            let a =
                AllocatedNum::alloc(&mut *cs, || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b =
                AllocatedNum::alloc(&mut *cs, || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c =
                AllocatedNum::alloc(&mut *cs, || self.c.ok_or(SynthesisError::AssignmentMissing))?;
            let d =
                AllocatedNum::alloc(&mut *cs, || self.d.ok_or(SynthesisError::AssignmentMissing))?;

            let res = poseidon4(&mut *cs, a.into(), b.into(), c.into(), d.into())?;
            cs.enforce(
                || "",
                |lc| lc + out.get_variable(),
                |lc| lc + CS::one(),
                |lc| lc + res.get_lc(),
            );
            Ok(())
        }
    }

    #[test]
    fn test_poseidon4_circuit() {
        let params = {
            let c = TestPoseidon4Circuit {
                a: None,
                b: None,
                c: None,
                d: None,
                out: None,
            };
            groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
        };

        let pvk = groth16::prepare_verifying_key(&params.vk);

        let expected = bazuka::zk::poseidon4::poseidon4(
            ZkScalar::from(123),
            ZkScalar::from(234),
            ZkScalar::from(345),
            ZkScalar::from(456),
        );

        let c = TestPoseidon4Circuit {
            a: Some(ZkScalar::from(123).into()),
            b: Some(ZkScalar::from(234).into()),
            c: Some(ZkScalar::from(345).into()),
            d: Some(ZkScalar::from(456).into()),
            out: Some(expected.into()),
        };
        let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();
        assert!(groth16::verify_proof(&pvk, &proof, &[expected.into()]).is_ok());

        let c = TestPoseidon4Circuit {
            a: Some(ZkScalar::from(123).into()),
            b: Some(ZkScalar::from(234).into()),
            c: Some(ZkScalar::from(345).into()),
            d: Some(ZkScalar::from(457).into()),
            out: Some(expected.into()),
        };
        let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();
        assert!(!groth16::verify_proof(&pvk, &proof, &[expected.into()]).is_ok());
    }
}
