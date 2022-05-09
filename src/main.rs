use bellman::gadgets::num::AllocatedNum;
use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
use bls12_381::{Bls12, Scalar as BellmanFr};
use ff::Field;
use rand::rngs::OsRng;
use zeekit::{mimc, Fr};

#[derive(Clone)]
pub struct DummyDemo {
    xl: Option<BellmanFr>,
    xr: Option<BellmanFr>,
    hash: Option<BellmanFr>,
}

impl Circuit<BellmanFr> for DummyDemo {
    fn synthesize<CS: ConstraintSystem<BellmanFr>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let xl = AllocatedNum::alloc(&mut *cs, || {
            self.xl.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let xr = AllocatedNum::alloc(&mut *cs, || {
            self.xr.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let claimed_hash = AllocatedNum::alloc(&mut *cs, || {
            self.hash.ok_or(SynthesisError::AssignmentMissing)
        })?;
        claimed_hash.inputize(&mut *cs)?;

        let hash = mimc::groth16::double_mimc(&mut *cs, xl, xr)?;

        cs.enforce(
            || "",
            |lc| lc + hash.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + claimed_hash.get_variable(),
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

    let xl = Fr::zero();
    let xr = Fr::one();
    let hash = mimc::double_mimc(xl, xr);

    let c = DummyDemo {
        xl: Some(xl.into()),
        xr: Some(xr.into()),
        hash: Some(hash.into()),
    };

    let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();

    let inputs = vec![hash.into()];

    println!("Verify: {}",groth16::verify_proof(&pvk, &proof, &inputs).is_ok());
}
