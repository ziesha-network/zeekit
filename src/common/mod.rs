mod mux;
mod number;
mod uint;
pub use mux::*;
pub use number::*;
pub use uint::*;

use crate::BellmanFr;

use bellman::gadgets::boolean::Boolean;
use bellman::{ConstraintSystem, SynthesisError};

pub fn assert_equal_if_enabled<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: &Boolean,
    a: &Number,
    b: &Number,
) -> Result<(), SynthesisError> {
    match enabled {
        Boolean::Is(enabled) => {
            let enabled_value = enabled.get_value();
            let enabled_in_a = cs.alloc(
                || "",
                || {
                    enabled_value
                        .map(|e| {
                            if e {
                                a.get_value()
                            } else {
                                Some(BellmanFr::zero())
                            }
                        })
                        .unwrap_or(None)
                        .ok_or(SynthesisError::AssignmentMissing)
                },
            )?;
            cs.enforce(
                || "enabled * a == enabled_in_a",
                |lc| lc + enabled.get_variable(),
                |lc| lc + a.get_lc(),
                |lc| lc + enabled_in_a,
            );
            cs.enforce(
                || "enabled * b == enabled_in_a",
                |lc| lc + enabled.get_variable(),
                |lc| lc + b.get_lc(),
                |lc| lc + enabled_in_a,
            );
        }
        Boolean::Not(_) => {
            unimplemented!();
        }
        Boolean::Constant(enabled) => {
            if *enabled {
                a.assert_equal(&mut *cs, b);
            }
        }
    }
    Ok(())
}

pub fn extract_bool<CS: ConstraintSystem<BellmanFr>>(b: &Boolean) -> Number {
    match b.clone() {
        Boolean::Is(b) => b.into(),
        Boolean::Not(not_b) => Number::one::<CS>() - not_b.into(),
        Boolean::Constant(b_val) => {
            if b_val {
                Number::one::<CS>()
            } else {
                Number::zero()
            }
        }
    }
}

pub fn assert_true<CS: ConstraintSystem<BellmanFr>>(cs: &mut CS, b: &Boolean) {
    extract_bool::<CS>(b).assert_equal(cs, &Number::one::<CS>());
}

pub fn assert_true_if_enabled<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: &Boolean,
    cond: &Boolean,
) -> Result<(), SynthesisError> {
    assert_equal_if_enabled(cs, enabled, &extract_bool::<CS>(cond), &Number::one::<CS>())
}

pub fn boolean_or<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::and(&mut *cs, &a.not(), &b.not())?.not())
}

#[cfg(test)]
mod test;
