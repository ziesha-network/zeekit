use dusk_plonk::prelude::*;
use ff::PrimeField;
use serde::{Deserialize, Serialize};

#[macro_use]
extern crate lazy_static;

// Scalar field of Bls12-381
#[derive(PrimeField, Serialize, Deserialize)]
#[PrimeFieldModulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "little"]
pub struct Fr([u64; 4]);

impl Into<BlsScalar> for Fr {
    fn into(self) -> BlsScalar {
        BlsScalar(self.0)
    }
}

impl From<BlsScalar> for Fr {
    fn from(bls: BlsScalar) -> Fr {
        Fr(bls.0)
    }
}

mod config;
pub mod eddsa;
pub mod gadgets;
pub mod merkle;
pub mod mimc;
