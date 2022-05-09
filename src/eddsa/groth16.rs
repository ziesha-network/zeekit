use crate::mimc;
use crate::BellmanFr;

use super::curve::PointAffine;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};
use std::ops::*;

pub struct AllocatedPoint {
    variables: (AllocatedNum<BellmanFr>, AllocatedNum<BellmanFr>),
    value: Option<PointAffine>,
}

impl AllocatedPoint {
    pub fn get_value(&self) -> Option<PointAffine> {
        self.value
    }
}

pub fn add_point<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedPoint,
    b: AllocatedPoint,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let added = a.get_value().zip(b.get_value()).map(|(mut a, b)| {
        a.add_assign(&b);
        a
    });
    unimplemented!();
}

// Mul by 8
/*fn mul_cofactor(composer: &mut TurboComposer, mut point: Point) -> WitnessPoint {
    point = composer.component_add_point(point, point);
    point = composer.component_add_point(point, point);
    point = composer.component_add_point(point, point);
    point
}

fn mul(composer: &mut TurboComposer, scalar: Witness, point: WitnessPoint) -> WitnessPoint {
    let scalar_bits = composer.component_decomposition::<255>(scalar);

    let identity = composer.append_constant_identity();
    let mut result = identity;

    for bit in scalar_bits.iter().rev() {
        result = composer.component_add_point(result, result);

        let point_to_add = composer.component_select_identity(*bit, point);
        result = composer.component_add_point(result, point_to_add);
    }

    result
}

pub fn verify(
    composer: &mut TurboComposer,
    enabled: Witness,
    pk: WitnessPoint,
    msg: Witness,
    sig: WitnessSignature,
) {
    // h=H(R,A,M)
    let h = mimc::plonk::mimc(composer, &[*sig.r.x(), *sig.r.y(), *pk.x(), *pk.y(), msg]);

    let mut sb = composer.component_mul_generator(sig.s, *BASE);
    sb = mul_cofactor(composer, sb);

    let mut r_plus_ha = mul(composer, h, pk);
    r_plus_ha = composer.component_add_point(r_plus_ha, sig.r);
    r_plus_ha = mul_cofactor(composer, r_plus_ha);

    common::plonk::controllable_assert_eq(composer, enabled, *r_plus_ha.x(), *sb.x());
    common::plonk::controllable_assert_eq(composer, enabled, *r_plus_ha.y(), *sb.y());
}*/
