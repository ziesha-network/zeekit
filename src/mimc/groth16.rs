use super::MIMC_PARAMS;
use crate::BellmanFr;
use std::ops::*;

use bellman::{ConstraintSystem, SynthesisError, Variable};

pub fn double_mimc<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    mut xl: (Variable, Option<BellmanFr>),
    mut xr: (Variable, Option<BellmanFr>),
) -> Result<(Variable, Option<BellmanFr>), SynthesisError> {
    for (i, c) in MIMC_PARAMS.iter().cloned().enumerate() {
        // xL, xR := xR + (xL + Ci)^3, xL
        let cs = &mut cs.namespace(|| format!("round {}", i));

        // tmp = (xL + Ci)^2
        let tmp_value = xl.1.map(|mut e| {
            e.add_assign(&c.into());
            e.square()
        });
        let tmp = cs.alloc(
            || "tmp",
            || tmp_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "tmp = (xL + Ci)^2",
            |lc| lc + xl.0 + (c.into(), CS::one()),
            |lc| lc + xl.0 + (c.into(), CS::one()),
            |lc| lc + tmp,
        );

        // new_xL = xR + (xL + Ci)^3
        // new_xL = xR + tmp * (xL + Ci)
        // new_xL - xR = tmp * (xL + Ci)
        let new_xl_value = xl.1.map(|mut e| {
            e.add_assign(&c.into());
            e.mul_assign(&tmp_value.unwrap());
            e.add_assign(&xr.1.unwrap());
            e
        });

        let new_xl = (
            cs.alloc(
                || "new_xl",
                || new_xl_value.ok_or(SynthesisError::AssignmentMissing),
            )?,
            new_xl_value,
        );

        cs.enforce(
            || "new_xL = xR + (xL + Ci)^3",
            |lc| lc + tmp,
            |lc| lc + xl.0 + (c.into(), CS::one()),
            |lc| lc + new_xl.0 - xr.0,
        );

        // xR = xL
        xr = xl;

        // xL = new_xL
        xl = new_xl;
    }

    Ok(xl)
}

pub fn mimc<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    data: &[(Variable, Option<BellmanFr>)],
) -> Result<(Variable, Option<BellmanFr>), SynthesisError> {
    assert!(data.len() >= 2);
    let mut accum = double_mimc(cs, data[0], data[1])?;
    for w in data[2..].iter() {
        accum = double_mimc(cs, accum, *w)?;
    }
    Ok(accum)
}
