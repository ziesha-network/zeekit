use crate::common::groth16::{is_zero, Number};
use crate::BellmanFr;
use crate::{common, poseidon};

use bazuka::crypto::jubjub::{PointAffine, A, BASE_COFACTOR, D};

use bellman::gadgets::boolean::Boolean;
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};
use ff::Field;
use std::ops::*;

#[derive(Clone)]
pub struct AllocatedPoint {
    pub x: AllocatedNum<BellmanFr>,
    pub y: AllocatedNum<BellmanFr>,
}

impl AllocatedPoint {
    pub fn alloc<
        CS: ConstraintSystem<BellmanFr>,
        F: FnOnce() -> Result<PointAffine, SynthesisError>,
    >(
        cs: &mut CS,
        f: F,
    ) -> Result<AllocatedPoint, SynthesisError> {
        let pnt = f()?;
        let x = AllocatedNum::<BellmanFr>::alloc(&mut *cs, || Ok(pnt.0.into()))?;
        let y = AllocatedNum::<BellmanFr>::alloc(&mut *cs, || Ok(pnt.1.into()))?;
        Ok(Self { x, y })
    }

    pub fn is_null<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
    ) -> Result<Boolean, SynthesisError> {
        let x_is_zero = is_zero(&mut *cs, &self.x.clone().into())?;
        let y_is_zero = is_zero(&mut *cs, &self.y.clone().into())?;
        Ok(Boolean::and(&mut *cs, &x_is_zero, &y_is_zero)?)
    }

    pub fn assert_on_curve<CS: ConstraintSystem<BellmanFr>>(
        &self,
        cs: &mut CS,
        enabled: &Boolean,
    ) -> Result<(), SynthesisError> {
        let x2 = self.x.mul(&mut *cs, &self.x)?;
        let y2 = self.y.mul(&mut *cs, &self.y)?;
        let x2y2 = x2.mul(&mut *cs, &y2)?;
        let lhs = Number::from(y2) - Number::from(x2);
        let rhs = Number::from((BellmanFr::from(*D), x2y2)) + Number::one::<CS>();
        common::groth16::assert_equal_if_enabled(cs, enabled, &lhs, &rhs)
    }
}

pub fn add_point<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &AllocatedPoint,
    b: &AllocatedPoint,
) -> Result<AllocatedPoint, SynthesisError> {
    let sum_value =
        a.x.get_value()
            .zip(a.y.get_value())
            .zip(b.x.get_value().zip(b.y.get_value()))
            .map(|((a_x, a_y), (b_x, b_y))| {
                if a_x.is_zero().into() && a_y.is_zero().into() {
                    // If empty, do not need to calculate
                    Default::default()
                } else {
                    let mut sum = PointAffine(a_x.into(), a_y.into());
                    sum.add_assign(&PointAffine(b_x.into(), b_y.into()));
                    sum
                }
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

pub fn add_const_point<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &AllocatedPoint,
    b: &PointAffine,
) -> Result<AllocatedPoint, SynthesisError> {
    let sum_value = a.x.get_value().zip(a.y.get_value()).map(|(a_x, a_y)| {
        let mut sum = PointAffine(a_x.into(), a_y.into());
        sum.add_assign(&b);
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

    let bx: BellmanFr = b.0.into();
    let by: BellmanFr = b.1.into();
    let curve_d_bx_by: BellmanFr = Into::<BellmanFr>::into(D.clone()) * bx * by;
    let common = a.x.mul(&mut *cs, &a.y)?; // * CURVE_D * bx * by

    cs.enforce(
        || "x_1 + x_2 == sum_x * (1 + common)",
        |lc| lc + CS::one() + (curve_d_bx_by, common.get_variable()),
        |lc| lc + sum_x.get_variable(),
        |lc| lc + (by, a.x.get_variable()) + (bx, a.y.get_variable()),
    );

    cs.enforce(
        || "y_1 - y_2 == sum_y * (1 - common)",
        |lc| lc + CS::one() - (curve_d_bx_by, common.get_variable()),
        |lc| lc + sum_y.get_variable(),
        |lc| {
            lc + (by, a.y.get_variable())
                - (Into::<BellmanFr>::into(A.clone()) * bx, a.x.get_variable())
        },
    );

    Ok(AllocatedPoint { x: sum_x, y: sum_y })
}

pub fn mul_point<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    base: &AllocatedPoint,
    b: &AllocatedNum<BellmanFr>,
) -> Result<AllocatedPoint, SynthesisError> {
    let bits: Vec<Boolean> = b.to_bits_le_strict(&mut *cs)?.into_iter().rev().collect();
    let mut result = AllocatedPoint {
        x: common::groth16::mux(&mut *cs, &bits[0], &Number::zero(), &base.x.clone().into())?,
        y: common::groth16::mux(
            &mut *cs,
            &bits[0],
            &Number::constant::<CS>(BellmanFr::one()),
            &base.y.clone().into(),
        )?,
    };
    for bit in bits[1..].iter() {
        result = add_point(&mut *cs, &result, &result)?;
        let result_plus_base = add_point(&mut *cs, &result, base)?;
        let result_x =
            common::groth16::mux(&mut *cs, &bit, &result.x.into(), &result_plus_base.x.into())?;
        let result_y =
            common::groth16::mux(&mut *cs, &bit, &result.y.into(), &result_plus_base.y.into())?;
        result = AllocatedPoint {
            x: result_x,
            y: result_y,
        };
    }
    Ok(result)
}

pub fn mul_const_point<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    base: &PointAffine,
    b: &AllocatedNum<BellmanFr>,
) -> Result<AllocatedPoint, SynthesisError> {
    let bits: Vec<Boolean> = b.to_bits_le_strict(&mut *cs)?.into_iter().rev().collect();
    let mut result = AllocatedPoint {
        x: common::groth16::mux(
            &mut *cs,
            &bits[0],
            &Number::zero(),
            &Number::constant::<CS>(base.0.into()),
        )?,
        y: common::groth16::mux(
            &mut *cs,
            &bits[0],
            &Number::constant::<CS>(BellmanFr::one()),
            &Number::constant::<CS>(base.1.into()),
        )?,
    };
    for bit in bits[1..].iter() {
        result = add_point(&mut *cs, &result, &result)?;
        let result_plus_base = add_const_point(&mut *cs, &result, base)?;
        let result_x =
            common::groth16::mux(&mut *cs, &bit, &result.x.into(), &result_plus_base.x.into())?;
        let result_y =
            common::groth16::mux(&mut *cs, &bit, &result.y.into(), &result_plus_base.y.into())?;
        result = AllocatedPoint {
            x: result_x,
            y: result_y,
        };
    }
    Ok(result)
}

// Mul by 8
pub fn mul_cofactor<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    point: &AllocatedPoint,
) -> Result<AllocatedPoint, SynthesisError> {
    let mut pnt = add_point(&mut *cs, point, point)?;
    pnt = add_point(&mut *cs, &pnt, &pnt)?;
    pnt = add_point(&mut *cs, &pnt, &pnt)?;
    Ok(pnt)
}

pub fn verify_eddsa<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: &Boolean,
    pk: &AllocatedPoint,
    msg: &Number,
    sig_r: &AllocatedPoint,
    sig_s: &AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {
    // h=H(R,A,M)
    let h = poseidon::groth16::poseidon(
        &mut *cs,
        &[
            &sig_r.x.clone().into(),
            &sig_r.y.clone().into(),
            &pk.x.clone().into(),
            &pk.y.clone().into(),
            msg,
        ],
    )?
    .compress(&mut *cs)?;

    let sb = mul_const_point(&mut *cs, &BASE_COFACTOR, sig_s)?;

    let mut r_plus_ha = mul_point(&mut *cs, pk, &h)?;
    r_plus_ha = add_point(&mut *cs, &r_plus_ha, sig_r)?;
    r_plus_ha = mul_cofactor(&mut *cs, &r_plus_ha)?;

    common::groth16::assert_equal_if_enabled(cs, enabled, &r_plus_ha.x.into(), &sb.x.into())?;
    common::groth16::assert_equal_if_enabled(cs, enabled, &r_plus_ha.y.into(), &sb.y.into())?;
    Ok(())
}
