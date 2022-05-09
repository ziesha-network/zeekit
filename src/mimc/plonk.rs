use super::MIMC_PARAMS;
use dusk_plonk::prelude::*;

// Constraints:
// q_mult · a · b  + q_left · a + q_right · b + q_output · o + q_fourth · d + q_constant + public_input = 0

pub fn double_mimc(composer: &mut TurboComposer, mut xl: Witness, mut xr: Witness) -> Witness {
    for c in MIMC_PARAMS.iter() {
        let tmp1 = composer.gate_add(
            Constraint::new()
                .left(1)
                .constant(c.clone())
                .output(1)
                .a(xl),
        );
        let mut tmp2 = composer.gate_mul(Constraint::new().mult(1).output(1).a(tmp1).b(tmp1));
        tmp2 = composer.gate_mul(Constraint::new().mult(1).output(1).a(tmp2).b(tmp1));
        tmp2 = composer.gate_add(Constraint::new().left(1).right(1).output(1).a(tmp2).b(xr));
        xr = xl;
        xl = tmp2;
    }
    xl
}

pub fn mimc(composer: &mut TurboComposer, data: &[Witness]) -> Witness {
    assert!(data.len() >= 2);
    let mut accum = double_mimc(composer, data[0], data[1]);
    for w in data[2..].iter() {
        accum = double_mimc(composer, accum, *w);
    }
    accum
}
