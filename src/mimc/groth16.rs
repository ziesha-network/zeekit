use super::MIMC_PARAMS;
use crate::BellmanFr;
use crate::Fr;
use ff::Field;
use std::ops::*;

use bellman::{ConstraintSystem, SynthesisError, Variable};

pub fn mimc(mut xl: Fr, mut xr: Fr) -> Fr {
    for c in MIMC_PARAMS.iter() {
        let mut tmp1 = xl;
        tmp1.add_assign(c);
        let mut tmp2 = tmp1.square();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}

pub fn mimc_gadget<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    mut xl: Variable,
    mut xr: Variable,
    mut xl_value: Option<BellmanFr>,
    mut xr_value: Option<BellmanFr>,
) -> Result<Variable, SynthesisError> {
    for (i, c) in MIMC_PARAMS.iter().cloned().enumerate() {
        // xL, xR := xR + (xL + Ci)^3, xL
        let cs = &mut cs.namespace(|| format!("round {}", i));

        // tmp = (xL + Ci)^2
        let tmp_value = xl_value.map(|mut e| {
            e.add_assign(&c.into());
            e.square()
        });
        let tmp = cs.alloc(
            || "tmp",
            || tmp_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "tmp = (xL + Ci)^2",
            |lc| lc + xl + (c.into(), CS::one()),
            |lc| lc + xl + (c.into(), CS::one()),
            |lc| lc + tmp,
        );

        // new_xL = xR + (xL + Ci)^3
        // new_xL = xR + tmp * (xL + Ci)
        // new_xL - xR = tmp * (xL + Ci)
        let new_xl_value = xl_value.map(|mut e| {
            e.add_assign(&c.into());
            e.mul_assign(&tmp_value.unwrap());
            e.add_assign(&xr_value.unwrap());
            e
        });

        let new_xl = cs.alloc(
            || "new_xl",
            || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "new_xL = xR + (xL + Ci)^3",
            |lc| lc + tmp,
            |lc| lc + xl + (c.into(), CS::one()),
            |lc| lc + new_xl - xr,
        );

        // xR = xL
        xr = xl;
        xr_value = xl_value;

        // xL = new_xL
        xl = new_xl;
        xl_value = new_xl_value;
    }

    Ok(xl)
}
