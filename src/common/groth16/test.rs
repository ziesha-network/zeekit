use super::*;
use crate::Bls12;
use bellman::gadgets::num::AllocatedNum;
use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
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
        let a = AllocatedNum::alloc(&mut *cs, || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        a.inputize(&mut *cs)?;
        let b = AllocatedNum::alloc(&mut *cs, || self.b.ok_or(SynthesisError::AssignmentMissing))?;
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

        let res_bool = is_equal(&mut *cs, &a.into(), &b.into())?;
        let res = extract_bool::<CS>(&res_bool);
        cs.enforce(
            || "",
            |lc| lc + res.get_lc(),
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

#[derive(Clone)]
struct TestLteCircuit {
    num_bits: usize,
    a: Option<BellmanFr>,
    b: Option<BellmanFr>,
    is_lte: Option<bool>,
}

impl Circuit<BellmanFr> for TestLteCircuit {
    fn synthesize<CS: ConstraintSystem<BellmanFr>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let a = AllocatedNum::alloc(&mut *cs, || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        a.inputize(&mut *cs)?;
        let a_64 = UnsignedInteger::constrain(&mut *cs, a.into(), self.num_bits)?;
        let b = AllocatedNum::alloc(&mut *cs, || self.b.ok_or(SynthesisError::AssignmentMissing))?;
        b.inputize(&mut *cs)?;
        let b_64 = UnsignedInteger::constrain(&mut *cs, b.into(), self.num_bits)?;
        let is_lte = AllocatedNum::alloc(&mut *cs, || {
            self.is_lte
                .map(|b| {
                    if b {
                        BellmanFr::one()
                    } else {
                        BellmanFr::zero()
                    }
                })
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        is_lte.inputize(&mut *cs)?;

        let res_bool = a_64.lte(&mut *cs, &b_64)?;
        let res = extract_bool::<CS>(&res_bool);
        cs.enforce(
            || "",
            |lc| lc + res.get_lc(),
            |lc| lc + CS::one(),
            |lc| lc + is_lte.get_variable(),
        );

        Ok(())
    }
}

#[test]
fn test_lte_circuit() {
    let params = {
        let c = TestLteCircuit {
            num_bits: 8,
            a: None,
            b: None,
            is_lte: None,
        };
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    let pvk = groth16::prepare_verifying_key(&params.vk);

    for (a, b, eq, expected) in [
        (0, 0, true, true),
        (0, 0, false, false),
        (0, 123, true, true),
        (0, 123, false, false),
        (123, 0, true, false),
        (123, 0, false, true),
        (122, 123, true, true),
        (123, 123, true, true),
        (124, 123, false, true),
        (122, 123, false, false),
        (123, 123, false, false),
        (124, 123, true, false),
        (252, 253, true, true),
        (253, 253, true, true),
        (254, 253, false, true),
        (252, 253, false, false),
        (253, 253, false, false),
        (254, 253, true, false),
        (254, 255, true, true),
        (255, 256, false, false),
        (255, 256, true, false),
        (256, 255, false, false),
        (256, 255, true, false),
        (255, 257, false, false),
        (255, 257, true, false),
        (257, 255, false, false),
        (257, 255, true, false),
    ] {
        let c = TestLteCircuit {
            num_bits: 8,
            a: Some(BellmanFr::from(a)),
            b: Some(BellmanFr::from(b)),
            is_lte: Some(eq),
        };
        let proof = groth16::create_random_proof(c.clone(), &params, &mut OsRng).unwrap();
        assert_eq!(
            groth16::verify_proof(
                &pvk,
                &proof,
                &[
                    c.a.unwrap(),
                    c.b.unwrap(),
                    c.is_lte
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

#[derive(Clone)]
struct TestOrCircuit {
    a: Option<bool>,
    b: Option<bool>,
    or_result: Option<bool>,
}

impl Circuit<BellmanFr> for TestOrCircuit {
    fn synthesize<CS: ConstraintSystem<BellmanFr>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let a = Boolean::Is(AllocatedBit::alloc(&mut *cs, self.a)?);
        let b = Boolean::Is(AllocatedBit::alloc(&mut *cs, self.b)?);
        let expected = AllocatedNum::alloc(&mut *cs, || {
            Ok(
                if self.or_result.ok_or(SynthesisError::AssignmentMissing)? {
                    1
                } else {
                    0
                }
                .into(),
            )
        })?;
        expected.inputize(&mut *cs)?;
        let or = boolean_or(&mut *cs, &a, &b)?;
        let or_num = extract_bool::<CS>(&or);
        assert_equal(&mut *cs, &or_num, &expected.into());

        Ok(())
    }
}

#[test]
fn test_or_circuit() {
    let params = {
        let c = TestOrCircuit {
            a: None,
            b: None,
            or_result: None,
        };
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    let pvk = groth16::prepare_verifying_key(&params.vk);

    for (a, b, or, expected) in [
        (false, false, false, true),
        (true, false, true, true),
        (false, true, true, true),
        (true, true, true, true),
        (false, false, true, false),
        (true, false, false, false),
        (false, true, false, false),
        (true, true, false, false),
    ] {
        let c = TestOrCircuit {
            a: Some(a),
            b: Some(b),
            or_result: Some(or),
        };
        let proof = groth16::create_random_proof(c.clone(), &params, &mut OsRng).unwrap();
        assert_eq!(
            groth16::verify_proof(
                &pvk,
                &proof,
                &[c.or_result
                    .map(|b| if b {
                        BellmanFr::one()
                    } else {
                        BellmanFr::zero()
                    })
                    .unwrap()]
            )
            .is_ok(),
            expected
        );
    }
}
