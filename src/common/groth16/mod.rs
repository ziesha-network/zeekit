mod mux;
mod uint;
mod wrapped_lc;
pub use mux::*;
pub use uint::*;
pub use wrapped_lc::*;

use crate::BellmanFr;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use ff::{Field, PrimeFieldBits};
use std::ops::{Add, Sub};

// Check if a number is zero, 2 constraints
pub fn is_zero<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    num: &WrappedLc,
) -> Result<AllocatedBit, SynthesisError> {
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
    Ok(is_zero)
}

// Check a == b, two constraints
pub fn is_equal<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &WrappedLc,
    b: &WrappedLc,
) -> Result<AllocatedBit, SynthesisError> {
    is_zero(cs, &(a.clone() - b.clone()))
}

pub fn not<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedBit,
) -> Result<AllocatedBit, SynthesisError> {
    let bit = AllocatedBit::alloc(&mut *cs, a.get_value().map(|b| !b))?;
    cs.enforce(
        || "",
        |lc| lc + CS::one() - a.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + bit.get_variable(),
    );
    Ok(bit)
}

pub fn assert_equal<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    enabled: AllocatedBit,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {
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
        |lc| lc + a.get_variable(),
        |lc| lc + enabled_in_a,
    );
    cs.enforce(
        || "enabled * b == enabled_in_a",
        |lc| lc + enabled.get_variable(),
        |lc| lc + b.get_variable(),
        |lc| lc + enabled_in_a,
    );
    Ok(())
}

#[cfg(test)]
mod test;
