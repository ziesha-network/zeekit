use super::*;

pub fn mux<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    select: &Boolean,
    a: &WrappedLc,
    b: &WrappedLc,
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
                |lc| lc + &a.0 - &b.0,
                |lc| lc + s.get_variable(),
                |lc| lc + &a.0 - ret.get_variable(),
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
                |lc| lc + &b.0 - &a.0,
                |lc| lc + not_s.get_variable(),
                |lc| lc + &b.0 - ret.get_variable(),
            );
            ret
        }
        Boolean::Constant(_) => {
            unimplemented!();
        }
    })
}
