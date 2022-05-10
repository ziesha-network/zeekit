use bellman::gadgets::boolean::AllocatedBit;
use bellman::gadgets::num::AllocatedNum;
use bellman::{groth16, Circuit, ConstraintSystem, SynthesisError};
use bls12_381::{Bls12, Scalar as BellmanFr};
use rand::rngs::OsRng;
use zeekit::{eddsa, Fr};

#[derive(Clone)]
pub struct DummyDemo {
    curve_a: Option<BellmanFr>,
    curve_d: Option<BellmanFr>,
    base: (Option<BellmanFr>, Option<BellmanFr>),
    msg: Option<BellmanFr>,
    pk: (Option<BellmanFr>, Option<BellmanFr>),
    sig_r: (Option<BellmanFr>, Option<BellmanFr>),
    sig_s: Option<BellmanFr>,
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

        let base_x = AllocatedNum::alloc(&mut *cs, || {
            self.base.0.ok_or(SynthesisError::AssignmentMissing)
        })?;
        base_x.inputize(&mut *cs)?;

        let base_y = AllocatedNum::alloc(&mut *cs, || {
            self.base.1.ok_or(SynthesisError::AssignmentMissing)
        })?;
        base_y.inputize(&mut *cs)?;

        let msg = AllocatedNum::alloc(&mut *cs, || {
            self.msg.ok_or(SynthesisError::AssignmentMissing)
        })?;
        msg.inputize(&mut *cs)?;

        let pk_x = AllocatedNum::alloc(&mut *cs, || {
            self.pk.0.ok_or(SynthesisError::AssignmentMissing)
        })?;
        pk_x.inputize(&mut *cs)?;

        let pk_y = AllocatedNum::alloc(&mut *cs, || {
            self.pk.1.ok_or(SynthesisError::AssignmentMissing)
        })?;
        pk_y.inputize(&mut *cs)?;

        let sig_s = AllocatedNum::alloc(&mut *cs, || {
            self.sig_s.ok_or(SynthesisError::AssignmentMissing)
        })?;
        sig_s.inputize(&mut *cs)?;

        let sig_r_x = AllocatedNum::alloc(&mut *cs, || {
            self.sig_r.0.ok_or(SynthesisError::AssignmentMissing)
        })?;
        sig_r_x.inputize(&mut *cs)?;

        let sig_r_y = AllocatedNum::alloc(&mut *cs, || {
            self.sig_r.1.ok_or(SynthesisError::AssignmentMissing)
        })?;
        sig_r_y.inputize(&mut *cs)?;

        let base = eddsa::groth16::AllocatedPoint {
            x: base_x,
            y: base_y,
        };

        let pk = eddsa::groth16::AllocatedPoint { x: pk_x, y: pk_y };

        let sig_r = eddsa::groth16::AllocatedPoint {
            x: sig_r_x,
            y: sig_r_y,
        };

        let enabled = AllocatedBit::alloc(&mut *cs, Some(true))?;

        eddsa::groth16::verify_eddsa(
            &mut *cs, enabled, curve_a, curve_d, base, pk, msg, sig_r, sig_s,
        )?;

        Ok(())
    }
}

fn main() {
    let params = {
        let c = DummyDemo {
            curve_a: None,
            curve_d: None,
            base: (None, None),
            msg: None,
            pk: (None, None),
            sig_r: (None, None),
            sig_s: None,
        };
        groth16::generate_random_parameters::<Bls12, _, _>(c, &mut OsRng).unwrap()
    };

    let pvk = groth16::prepare_verifying_key(&params.vk);

    let (publ, priva) = eddsa::generate_keys(Fr::from(123456), Fr::from(2345567));
    let pk = publ.0.decompress();
    let msg = Fr::from(12345678);
    let sig = eddsa::sign(&priva, msg);

    let curve_a = eddsa::A.clone();
    let curve_d = eddsa::D.clone();
    let base = eddsa::BASE.clone();

    let sig_s = sig.s;
    let sig_r = sig.r;

    let circ = DummyDemo {
        curve_a: Some(curve_a.into()),
        curve_d: Some(curve_d.into()),
        base: (Some(base.0.into()), Some(base.1.into())),
        msg: Some(msg.into()),
        pk: (Some(pk.0.into()), Some(pk.1.into())),
        sig_s: Some(sig_s.into()),
        sig_r: (Some(sig_r.0.into()), Some(sig_r.1.into())),
    };

    let proof = groth16::create_random_proof(circ, &params, &mut OsRng).unwrap();

    let inputs = vec![
        curve_a.into(),
        curve_d.into(),
        base.0.into(),
        base.1.into(),
        msg.into(),
        pk.0.into(),
        pk.1.into(),
        sig_s.into(),
        sig_r.0.into(),
        sig_r.1.into(),
    ];

    println!(
        "Verify: {}",
        groth16::verify_proof(&pvk, &proof, &inputs).is_ok()
    );
}
