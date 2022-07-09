use crate::BellmanFr;
use crate::{common, poseidon};

use bazuka::crypto::jubjub::{PointAffine, A, D};

use bellman::gadgets::boolean::AllocatedBit;
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};
use std::ops::*;

#[derive(Clone)]
pub struct AllocatedPoint {
    pub x: AllocatedNum<BellmanFr>,
    pub y: AllocatedNum<BellmanFr>,
}

pub fn add_point<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedPoint,
    b: AllocatedPoint,
) -> Result<AllocatedPoint, SynthesisError> {
    let sum_value =
        a.x.get_value()
            .zip(a.y.get_value())
            .zip(b.x.get_value().zip(b.y.get_value()))
            .map(|((a_x, a_y), (b_x, b_y))| {
                let mut sum = PointAffine(a_x.into(), a_y.into());
                sum.add_assign(&PointAffine(b_x.into(), b_y.into()));
                sum
            });
    let sum_x = AllocatedNum::alloc(&mut *cs, || {
        sum_value
            .map(|v| v.0.into())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    let sum_y = AllocatedNum::alloc(&mut *cs, || {
        sum_value
            .map(|v| v.1.into())
            .ok_or(SynthesisError::AssignmentMissing)
    })?;

    let curve_d: BellmanFr = D.clone().into();
    let common =
        a.x.mul(&mut *cs, &b.x)?
            .mul(&mut *cs, &a.y)?
            .mul(&mut *cs, &b.y)?; // * CURVE_D

    let x_1 = a.x.mul(&mut *cs, &b.y)?;
    let x_2 = a.y.mul(&mut *cs, &b.x)?;
    cs.enforce(
        || "x_1 + x_2 == sum_x * (1 + common)",
        |lc| lc + CS::one() + (curve_d, common.get_variable()),
        |lc| lc + sum_x.get_variable(),
        |lc| lc + x_1.get_variable() + x_2.get_variable(),
    );

    let y_1 = a.y.mul(&mut *cs, &b.y)?;
    let y_2 = a.x.mul(&mut *cs, &b.x)?; // * CURVE_A
    cs.enforce(
        || "y_1 - y_2 == sum_y * (1 - common)",
        |lc| lc + CS::one() - (curve_d, common.get_variable()),
        |lc| lc + sum_y.get_variable(),
        |lc| lc + y_1.get_variable() - (A.clone().into(), y_2.get_variable()),
    );

    Ok(AllocatedPoint { x: sum_x, y: sum_y })
}

pub fn mul_point<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    base: AllocatedPoint,
    b: AllocatedNum<BellmanFr>,
) -> Result<AllocatedPoint, SynthesisError> {
    let bits = b.to_bits_le(&mut *cs)?;
    let mut result = AllocatedPoint {
        x: AllocatedNum::alloc(&mut *cs, || Ok(BellmanFr::zero()))?,
        y: AllocatedNum::alloc(&mut *cs, || Ok(BellmanFr::one()))?,
    };
    for bit in bits.iter().rev() {
        result = add_point(&mut *cs, result.clone(), result)?;
        let result_plus_base = add_point(&mut *cs, result.clone(), base.clone())?;
        let result_x = common::groth16::mux(&mut *cs, &bit, &result.x, &result_plus_base.x)?;
        let result_y = common::groth16::mux(&mut *cs, &bit, &result.y, &result_plus_base.y)?;
        result = AllocatedPoint {
            x: result_x,
            y: result_y,
        };
    }
    Ok(result)
}

// Mul by 8
pub fn mul_cofactor<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    mut point: AllocatedPoint,
) -> Result<AllocatedPoint, SynthesisError> {
    point = add_point(&mut *cs, point.clone(), point)?;
    point = add_point(&mut *cs, point.clone(), point)?;
    point = add_point(&mut *cs, point.clone(), point)?;
    Ok(point)
}

pub fn verify_eddsa<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: AllocatedBit,
    base: AllocatedPoint,
    pk: AllocatedPoint,
    msg: AllocatedNum<BellmanFr>,
    sig_r: AllocatedPoint,
    sig_s: AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {
    // h=H(R,A,M)
    let h = poseidon::groth16::poseidon(
        &mut *cs,
        &[
            sig_r.x.clone(),
            sig_r.y.clone(),
            pk.x.clone(),
            pk.y.clone(),
            msg,
        ],
    )?;

    let sb = mul_point(&mut *cs, base.clone(), sig_s)?;
    //sb = mul_cofactor(&mut *cs, sb)?;

    let mut r_plus_ha = mul_point(&mut *cs, pk.clone(), h)?;
    r_plus_ha = add_point(&mut *cs, r_plus_ha.clone(), sig_r)?;
    //r_plus_ha = mul_cofactor(&mut *cs, r_plus_ha)?;

    common::groth16::assert_equal(cs, enabled.clone(), r_plus_ha.x, sb.x)?;
    common::groth16::assert_equal(cs, enabled, r_plus_ha.y, sb.y)?;
    Ok(())
}
