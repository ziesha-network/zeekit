use crate::config::MIMC_PARAMS;
use crate::Fr;
use ff::Field;

pub mod gadget;

pub fn mimc_encrypt(mut inp: Fr, k: Fr) -> Fr {
    for c in MIMC_PARAMS.iter() {
        inp = inp + k + c;
        inp = inp * inp * inp;
    }
    inp
}

pub fn mimc(inp: Vec<Fr>) -> Fr {
    let mut digest = Fr::zero();
    for d in inp {
        let encrypted = mimc_encrypt(d, digest);
        digest = digest + encrypted;
    }
    digest
}
