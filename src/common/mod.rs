mod mux;
mod number;
mod uint;
pub use mux::*;
pub use number::*;
pub use uint::*;

use crate::BellmanFr;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};
use ff::Field;

// Check if a number is zero, 2 constraints
pub fn is_zero<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    num: &Number,
) -> Result<Boolean, SynthesisError> {
    let is_zero = AllocatedBit::alloc(&mut *cs, num.get_value().map(|num| num.is_zero().into()))?;
    let inv = AllocatedNum::alloc(&mut *cs, || {
        num.get_value()
            .map(|num| {
                if num.is_zero().into() {
                    BellmanFr::zero()
                } else {
                    num.invert().unwrap()
                }
            })
            .ok_or(SynthesisError::AssignmentMissing)
    })?;

    // Alice claims "is_zero == 0", so "-num * inv == -1", so "inv" should be "1/num"
    // Calculating inv is only possible if num != 0

    cs.enforce(
        || "-num * inv == is_zero - 1",
        |lc| lc - num.get_lc(),
        |lc| lc + inv.get_variable(),
        |lc| lc + is_zero.get_variable() - CS::one(),
    );

    // Alice claims "is_zero == 1". Since "is_zero * num == 0", num can only be 0
    cs.enforce(
        || "is_zero * num == 0",
        |lc| lc + is_zero.get_variable(),
        |lc| lc + num.get_lc(),
        |lc| lc,
    );
    Ok(Boolean::Is(is_zero))
}

// Check a == b, two constraints
pub fn is_equal<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &Number,
    b: &Number,
) -> Result<Boolean, SynthesisError> {
    is_zero(cs, &(a.clone() - b.clone()))
}

pub fn assert_equal<CS: ConstraintSystem<BellmanFr>>(cs: &mut CS, a: &Number, b: &Number) {
    cs.enforce(
        || "",
        |lc| lc + a.get_lc(),
        |lc| lc + CS::one(),
        |lc| lc + b.get_lc(),
    );
}

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
        _ => {
            unimplemented!();
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
    assert_equal(cs, &extract_bool::<CS>(b), &Number::one::<CS>());
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
