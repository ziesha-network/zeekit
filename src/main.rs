use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
use bls12_381::{Bls12, Scalar as Fr};
use ff::PrimeField;
use rand::rngs::OsRng;
use zeekit::experiment::{mimc, mimc_gadget};

fn build_mimc_params<Scalar: PrimeField>() -> Vec<Scalar> {
    (0..322).map(|i| Scalar::from(i)).collect()
}

#[derive(Clone)]
pub struct DummyDemo<Scalar: PrimeField> {
    xl: Option<Scalar>,
    xr: Option<Scalar>,
    hash: Option<Scalar>,
}

impl<Scalar: PrimeField> Circuit<Scalar> for DummyDemo<Scalar> {
    fn synthesize<CS: ConstraintSystem<Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let xl = cs.alloc(|| "", || self.xl.ok_or(SynthesisError::AssignmentMissing))?;
        let xr = cs.alloc(|| "", || self.xr.ok_or(SynthesisError::AssignmentMissing))?;
        let claimed_hash =
            cs.alloc_input(|| "", || self.hash.ok_or(SynthesisError::AssignmentMissing))?;
        let hash = mimc_gadget(cs, xl, xr, self.xl, self.xr, &build_mimc_params())?;

        cs.enforce(
            || "",
            |lc| lc + hash,
            |lc| lc + CS::one(),
            |lc| lc + claimed_hash,
        );

        Ok(())
    }
}

fn main() {
    let params = {
        let c = DummyDemo::<Fr> {
            xl: None,
            xr: None,
            hash: None,
        };
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    let pvk = groth16::prepare_verifying_key(&params.vk);

    let xl = Fr::one();
    let xr = Fr::one();
    let hash = mimc(xl, xr, &build_mimc_params());

    let c = DummyDemo::<Fr> {
        xl: Some(xl),
        xr: Some(xr),
        hash: Some(hash),
    };

    let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();

    let inputs = vec![hash];

    assert!(groth16::verify_proof(&pvk, &proof, &inputs).is_ok());
}
