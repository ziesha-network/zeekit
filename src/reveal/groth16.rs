use crate::BellmanFr;

use bazuka::core::ZkHasher;
use bazuka::zk::{ZkDataPairs, ZkStateBuilder, ZkStateModel};
use bellman::gadgets::num::AllocatedNum;
use bellman::{ConstraintSystem, SynthesisError};

pub fn reveal<CS: ConstraintSystem<BellmanFr>>(
    cs: &mut CS,
    state_model: ZkStateModel,
    data_pairs: Option<ZkDataPairs>,
) -> Result<AllocatedNum<BellmanFr>, SynthesisError> {
    let root = AllocatedNum::alloc(&mut *cs, || {
        let mut state_builder = ZkStateBuilder::<ZkHasher>::new(state_model);
        data_pairs
            .map(|data_pairs| {
                state_builder.batch_set(&data_pairs.as_delta()).unwrap();
                state_builder.compress().unwrap().state_hash.into()
            })
            .ok_or(SynthesisError::AssignmentMissing)
    })?;
    Ok(root)
}
