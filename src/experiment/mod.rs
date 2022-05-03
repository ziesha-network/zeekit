use ff::PrimeField;

use bellman::{ConstraintSystem, SynthesisError, Variable};

pub const MIMC_ROUNDS: usize = 322;

pub fn mimc<S: PrimeField>(mut xl: S, mut xr: S, constants: &[S]) -> S {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for c in constants {
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

pub fn mimc_gadget<'a, Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    cs: &mut CS,
    mut xl: Variable,
    mut xr: Variable,
    mut xl_value: Option<Scalar>,
    mut xr_value: Option<Scalar>,
    constants: &'a [Scalar],
) -> Result<Variable, SynthesisError> {
    for i in 0..MIMC_ROUNDS {
        // xL, xR := xR + (xL + Ci)^3, xL
        let cs = &mut cs.namespace(|| format!("round {}", i));

        // tmp = (xL + Ci)^2
        let tmp_value = xl_value.map(|mut e| {
            e.add_assign(&constants[i]);
            e.square()
        });
        let tmp = cs.alloc(
            || "tmp",
            || tmp_value.ok_or(SynthesisError::AssignmentMissing),
        )?;

        cs.enforce(
            || "tmp = (xL + Ci)^2",
            |lc| lc + xl + (constants[i], CS::one()),
            |lc| lc + xl + (constants[i], CS::one()),
            |lc| lc + tmp,
        );

        // new_xL = xR + (xL + Ci)^3
        // new_xL = xR + tmp * (xL + Ci)
        // new_xL - xR = tmp * (xL + Ci)
        let new_xl_value = xl_value.map(|mut e| {
            e.add_assign(&constants[i]);
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
            |lc| lc + xl + (constants[i], CS::one()),
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
