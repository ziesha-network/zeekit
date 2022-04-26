mod curve;
pub mod gadget;
use curve::*;

use crate::{mimc, Fr};
use ff::PrimeField;
use num_bigint::BigUint;
use num_integer::Integer;
use serde::{Deserialize, Serialize};
use std::ops::*;

#[derive(Clone)]
pub struct PrivateKey {
    pub public_key: PointAffine,
    pub randomness: Fr,
    pub scalar: Fr,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PublicKey(PointCompressed);

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Signature {
    pub r: PointAffine,
    pub s: Fr,
}

fn generate_keys(randomness: Fr, scalar: Fr) -> (PublicKey, PrivateKey) {
    let point = BASE.multiply(&scalar);
    let pk = PublicKey(point.compress());
    (
        pk.clone(),
        PrivateKey {
            public_key: point,
            randomness,
            scalar,
        },
    )
}
fn sign(sk: &PrivateKey, message: Fr) -> Signature {
    // r=H(b,M)
    let r = mimc::mimc(vec![sk.randomness, message]);

    // R=rB
    let rr = BASE.multiply(&r);

    // h=H(R,A,M)
    let h = mimc::mimc(vec![rr.0, rr.1, sk.public_key.0, sk.public_key.1, message]);

    // s = (r + ha) mod ORDER
    let mut s = BigUint::from_bytes_le(r.to_repr().as_ref());
    let mut ha = BigUint::from_bytes_le(h.to_repr().as_ref());
    ha.mul_assign(&BigUint::from_bytes_le(sk.scalar.to_repr().as_ref()));
    s.add_assign(&ha);
    s = s.mod_floor(&*ORDER);

    Signature {
        r: rr,
        s: h, //FIX!
    }
}

fn verify(pk: &PublicKey, message: Fr, sig: &Signature) -> bool {
    let pk = pk.0.decompress();

    // h=H(R,A,M)
    let h = mimc::mimc(vec![sig.r.0, sig.r.1, pk.0, pk.1, message]);

    let sb = BASE.multiply(&sig.s);

    let mut r_plus_ha = pk.multiply(&h);
    r_plus_ha.add_assign(&sig.r);

    r_plus_ha == sb
}
