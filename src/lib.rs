use ff::PrimeField;
use num_bigint::BigUint;
use num_integer::Integer;
use serde::{Deserialize, Serialize};
use std::str::FromStr;

#[cfg(feature = "plonk")]
use dusk_plonk::prelude::BlsScalar;

#[cfg(feature = "groth16")]
pub use bls12_381::Scalar as BellmanFr;

#[macro_use]
extern crate lazy_static;

lazy_static! {
    static ref FR_MODULUS: BigUint = BigUint::from_str(
        "52435875175126190479447740508185965837690552500527637822603658699938581184513"
    )
    .unwrap();
}

// Scalar field of Bls12-381
#[derive(PrimeField, Serialize, Deserialize)]
#[PrimeFieldModulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "little"]
pub struct Fr([u64; 4]);

impl Fr {
    pub fn new(num_le: [u8; 32]) -> Self {
        let bts = BigUint::from_bytes_le(&num_le)
            .mod_floor(&FR_MODULUS)
            .to_bytes_le();
        let mut data = [0u8; 32];
        data[0..bts.len()].copy_from_slice(&bts);
        Fr::from_repr_vartime(FrRepr(data)).unwrap()
    }
}

#[cfg(feature = "plonk")]
impl Into<BlsScalar> for Fr {
    fn into(self) -> BlsScalar {
        BlsScalar(self.0)
    }
}

#[cfg(feature = "plonk")]
impl From<BlsScalar> for Fr {
    fn from(bls: BlsScalar) -> Fr {
        Fr(bls.0)
    }
}

#[cfg(feature = "groth16")]
impl Into<BellmanFr> for Fr {
    fn into(self) -> BellmanFr {
        unsafe { std::mem::transmute::<Fr, BellmanFr>(self) }
    }
}

#[cfg(feature = "groth16")]
impl From<BellmanFr> for Fr {
    fn from(bls: BellmanFr) -> Fr {
        unsafe { std::mem::transmute::<BellmanFr, Fr>(bls) }
    }
}

pub mod common;
mod config;
pub mod eddsa;
pub mod merkle;
pub mod mimc;
