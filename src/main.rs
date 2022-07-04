use bellman::gadgets::num::AllocatedNum;
use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
use rand::rngs::OsRng;
use zeekit::poseidon::groth16::poseidon4;
use zeekit::BellmanFr;
use zeekit::Bls12;

struct MyCircuit {}

impl Circuit<BellmanFr> for MyCircuit {
    fn synthesize<CS: ConstraintSystem<BellmanFr>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let a1 = AllocatedNum::alloc(&mut *cs, || Ok(BellmanFr::from(123)))?;
        let a2 = AllocatedNum::alloc(&mut *cs, || Ok(BellmanFr::from(234)))?;
        let a3 = AllocatedNum::alloc(&mut *cs, || Ok(BellmanFr::from(345)))?;
        let a4 = AllocatedNum::alloc(&mut *cs, || Ok(BellmanFr::from(456)))?;
        let res = poseidon4(&mut *cs, a1, a2, a3, a4)?;
        println!("{:?}", res.1);
        Ok(())
    }
}

fn main() {
    // be generated securely using a multiparty computation.
    let params = {
        let c = MyCircuit {};
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    // Prepare the verification key (for proof verification).
    let pvk = groth16::prepare_verifying_key(&params.vk);

    // Create an instance of our circuit (with the preimage as a witness).
    let c = MyCircuit {};

    // Create a Groth16 proof with our parameters.
    let proof = groth16::create_random_proof(c, &params, &mut OsRng).unwrap();

    println!(
        "{:?}",
        bazuka::zk::poseidon4::poseidon4(
            bazuka::zk::ZkScalar::from(123),
            bazuka::zk::ZkScalar::from(234),
            bazuka::zk::ZkScalar::from(345),
            bazuka::zk::ZkScalar::from(456)
        )
    );

    // Check the proof!
    println!("{:?}", groth16::verify_proof(&pvk, &proof, &[]).unwrap());
}
