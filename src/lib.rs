#[cfg(feature = "groth16")]
pub use bls12_381::{Bls12, G1Affine as BellmanG1, G2Affine as BellmanG2, Scalar as BellmanFr};

#[macro_use]
extern crate lazy_static;

pub mod common;
pub mod eddsa;
pub mod merkle;
pub mod poseidon;
