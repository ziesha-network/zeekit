use bellman::{
    gadgets::{
        boolean::{AllocatedBit, Boolean},
    },
    groth16, Circuit, ConstraintSystem, SynthesisError, Variable
};
use bls12_381::{Bls12, Scalar as Fr};
use ff::PrimeField;
use rand::rngs::OsRng;

fn my_gadget<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
) -> Result<Variable, SynthesisError> {
    Ok(cs.alloc(|| "", || Ok(Scalar::one()))?)
}


#[derive(Clone)]
pub struct DummyDemo {
    pub private: usize,
}

impl<Scalar: PrimeField> Circuit<Scalar> for DummyDemo {
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut x_val = Scalar::from(2);
        let mut x = cs.alloc_input(|| "", || Ok(x_val))?;

        for _ in 0..self.private {
            let x2_val = x_val.square();

            let x2 = cs.alloc(|| "", || Ok(x2_val))?;

            cs.enforce(|| "", |lc| lc + x, |lc| lc + x, |lc| lc + x2);

            x = x2;
            x_val = x2_val;
        }

        cs.enforce(
            || "",
            |lc| lc + (x_val, CS::one()),
            |lc| lc + CS::one(),
            |lc| lc + x,
        );

        Ok(())
    }
}


fn main() {
    let params = {
        let c = DummyDemo { private: 128 };
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    let pvk = groth16::prepare_verifying_key(&params.vk);

    let c = DummyDemo {
        private: 128,
    };

    let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();

    let inputs = vec![Fr::from(2)];

    assert!(groth16::verify_proof(&pvk, &proof, &inputs).is_ok());
}
