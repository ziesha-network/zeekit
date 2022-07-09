use crate::BellmanFr;

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};

pub fn mux<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: &Boolean,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    Ok(match select {
        Boolean::Is(s) => {
            let ret = AllocatedNum::alloc(&mut *cs, || {
                s.get_value()
                    .and_then(|s| if s { b.get_value() } else { a.get_value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "(a - b) * s == a - ret",
                |lc| lc + a.get_variable() - b.get_variable(),
                |lc| lc + s.get_variable(),
                |lc| lc + a.get_variable() - ret.get_variable(),
            );
            ret
        }
        Boolean::Not(not_s) => {
            let ret = AllocatedNum::alloc(&mut *cs, || {
                not_s
                    .get_value()
                    .and_then(|not_s| if not_s { a.get_value() } else { b.get_value() })
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "(b - a) * not_s == b - ret",
                |lc| lc + b.get_variable() - a.get_variable(),
                |lc| lc + not_s.get_variable(),
                |lc| lc + b.get_variable() - ret.get_variable(),
            );
            ret
        }
        Boolean::Constant(s) => {
            if *s {
                b
            } else {
                a
            }
        }
    })
}

pub fn bit_or<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Ok(Boolean::and(&mut *cs, &a.not(), &b.not())?.not())
}

pub fn bit_lt<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: &Boolean,
    b: &Boolean,
) -> Result<Boolean, SynthesisError> {
    Boolean::and(&mut *cs, &a.not(), &b)
}

pub fn lte<'a, CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    a: AllocatedNum<BellmanFr>,
    b: AllocatedNum<BellmanFr>,
) -> Result<(), SynthesisError> {
    let a_bits = a.to_bits_le(&mut *cs)?;
    let b_bits = b.to_bits_le(&mut *cs)?;

    let mut lt = Boolean::Constant(false);
    let mut gt = Boolean::Constant(false);
    for (a, b) in a_bits.into_iter().zip(b_bits.into_iter()).rev() {
        let a_lt_b = bit_lt(&mut *cs, &a, &b)?;
        let not_gt_and_a_lt_b = Boolean::and(&mut *cs, &gt.not(), &a_lt_b)?;
        lt = bit_or(&mut *cs, &lt, &not_gt_and_a_lt_b)?;

        let b_lt_a = bit_lt(&mut *cs, &b, &a)?;
        let not_lt_and_b_lt_a = Boolean::and(&mut *cs, &lt.not(), &b_lt_a)?;
        gt = bit_or(&mut *cs, &gt, &not_lt_and_b_lt_a)?;
    }

    let not_lt_and_not_gt = Boolean::and(&mut *cs, &lt.not(), &gt.not())?;
    let lt_or_not_lt_and_not_gt = bit_or(&mut *cs, &lt, &not_lt_and_not_gt)?;
    Boolean::enforce_equal(&mut *cs, &lt_or_not_lt_and_not_gt, &Boolean::Constant(true))?;
    Ok(())
}

pub fn assert_equal<'a, CS: ConstraintSystem<BellmanFr>>(
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
