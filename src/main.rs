use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
use bls12_381::{Bls12, Scalar as Fr};
use rand::rngs::OsRng;
use zeekit::mimc::groth16::{mimc, mimc_gadget};

#[derive(Clone)]
pub struct DummyDemo {
    xl: Option<Fr>,
    xr: Option<Fr>,
    hash: Option<Fr>,
}

impl Circuit<Fr> for DummyDemo {
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let xl = cs.alloc(|| "", || self.xl.ok_or(SynthesisError::AssignmentMissing))?;
        let xr = cs.alloc(|| "", || self.xr.ok_or(SynthesisError::AssignmentMissing))?;
        let claimed_hash =
            cs.alloc_input(|| "", || self.hash.ok_or(SynthesisError::AssignmentMissing))?;
        let hash = mimc_gadget(cs, xl, xr, self.xl, self.xr)?;

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
        let c = DummyDemo {
            xl: None,
            xr: None,
            hash: None,
        };
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    let pvk = groth16::prepare_verifying_key(&params.vk);

    let xl = Fr::one();
    let xr = Fr::one();
    let hash = mimc(xl.into(), xr.into());

    let c = DummyDemo {
        xl: Some(xl),
        xr: Some(xr),
        hash: Some(hash.into()),
    };

    let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();

    let inputs: Vec<Fr> = vec![hash.into()];

    assert!(groth16::verify_proof(&pvk, &proof, &inputs).is_ok());
}
