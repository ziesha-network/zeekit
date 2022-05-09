use bellman::gadgets::num::AllocatedNum;
use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
use bls12_381::{Bls12, Scalar as BellmanFr};
use rand::rngs::OsRng;
use zeekit::{eddsa, Fr};

#[derive(Clone)]
pub struct DummyDemo {
    curve_a: Option<BellmanFr>,
    curve_d: Option<BellmanFr>,
    a: (Option<BellmanFr>, Option<BellmanFr>),
    mul: Option<BellmanFr>,
    c: (Option<BellmanFr>, Option<BellmanFr>),
}

impl Circuit<BellmanFr> for DummyDemo {
    fn synthesize<CS: ConstraintSystem<BellmanFr>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let curve_a = AllocatedNum::alloc(&mut *cs, || {
            self.curve_a.ok_or(SynthesisError::AssignmentMissing)
        })?;
        curve_a.inputize(&mut *cs)?;
        let curve_d = AllocatedNum::alloc(&mut *cs, || {
            self.curve_d.ok_or(SynthesisError::AssignmentMissing)
        })?;
        curve_d.inputize(&mut *cs)?;

        let a_x = AllocatedNum::alloc(&mut *cs, || {
            self.a.0.ok_or(SynthesisError::AssignmentMissing)
        })?;
        a_x.inputize(&mut *cs)?;

        let a_y = AllocatedNum::alloc(&mut *cs, || {
            self.a.1.ok_or(SynthesisError::AssignmentMissing)
        })?;
        a_y.inputize(&mut *cs)?;

        let mul = AllocatedNum::alloc(&mut *cs, || {
            self.mul.ok_or(SynthesisError::AssignmentMissing)
        })?;
        mul.inputize(&mut *cs)?;

        let c_x = AllocatedNum::alloc(&mut *cs, || {
            self.c.0.ok_or(SynthesisError::AssignmentMissing)
        })?;
        c_x.inputize(&mut *cs)?;

        let c_y = AllocatedNum::alloc(&mut *cs, || {
            self.c.1.ok_or(SynthesisError::AssignmentMissing)
        })?;
        c_y.inputize(&mut *cs)?;

        let calc = eddsa::groth16::mul_point(
            &mut *cs,
            curve_a,
            curve_d,
            eddsa::groth16::AllocatedPoint { x: a_x, y: a_y },
            mul,
        )?;

        cs.enforce(
            || "",
            |lc| lc + calc.x.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + c_x.get_variable(),
        );

        cs.enforce(
            || "",
            |lc| lc + calc.y.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + c_y.get_variable(),
        );

        Ok(())
    }
}

fn main() {
    let params = {
        let c = DummyDemo {
            curve_a: None,
            curve_d: None,
            a: (None, None),
            mul: None,
            c: (None, None),
        };
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    let pvk = groth16::prepare_verifying_key(&params.vk);

    let curve_a = eddsa::A.clone();
    let curve_d = eddsa::D.clone();
    let a = eddsa::BASE.clone();
    let mul = Fr::from(1234567);
    let c = a.multiply(&mul);

    let circ = DummyDemo {
        curve_a: Some(curve_a.into()),
        curve_d: Some(curve_d.into()),
        a: (Some(a.0.into()), Some(a.1.into())),
        mul: Some(mul.into()),
        c: (Some(c.0.into()), Some(c.1.into())),
    };

    let proof = groth16::create_random_proof(circ, &params, &mut OsRng).unwrap();

    let inputs = vec![
        curve_a.into(),
        curve_d.into(),
        a.0.into(),
        a.1.into(),
        Fr::from(1234567).into(),
        c.0.into(),
        c.1.into(),
    ];

    println!(
        "Verify: {}",
        groth16::verify_proof(&pvk, &proof, &inputs).is_ok()
    );
}
