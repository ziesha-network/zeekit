#[cfg(feature = "groth16")]
pub mod groth16;

use bazuka::zk::ZkScalar;
use ff::Field;

const LOG_TREE_SIZE: usize = 3;

#[derive(Debug, Clone)]
pub struct Proof(pub [ZkScalar; LOG_TREE_SIZE]);
impl Default for Proof {
    fn default() -> Self {
        Self([ZkScalar::zero(); LOG_TREE_SIZE])
    }
}
