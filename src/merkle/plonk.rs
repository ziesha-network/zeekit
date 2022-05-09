use crate::common;
use crate::{config, mimc};
use dusk_plonk::prelude::*;

fn merge_hash(composer: &mut TurboComposer, dir: Witness, a: Witness, b: Witness) -> Witness {
    let l = mimc::plonk::double_mimc(composer, a, b);
    let r = mimc::plonk::double_mimc(composer, b, a);
    composer.component_boolean(dir);
    composer.component_select(dir, r, l)
}

pub fn calc_root(
    composer: &mut TurboComposer,
    index: Witness,
    val: Witness,
    proof: Vec<Witness>,
) -> Witness {
    let selectors = composer.component_decomposition::<{ config::LOG_TREE_SIZE }>(index);
    let mut curr = val;
    for (p, dir) in proof.into_iter().zip(selectors.into_iter()) {
        curr = merge_hash(composer, dir, curr, p);
    }
    curr
}

pub fn check_proof(
    composer: &mut TurboComposer,
    enabled: Witness,
    index: Witness,
    val: Witness,
    proof: Vec<Witness>,
    root: Witness,
) {
    let new_root = calc_root(composer, index, val, proof);
    common::plonk::controllable_assert_eq(composer, enabled, new_root, root);
}
