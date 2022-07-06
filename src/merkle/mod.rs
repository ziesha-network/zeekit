#[cfg(feature = "groth16")]
pub mod groth16;

use bazuka::zk::ZkScalar;
use ff::Field;

#[derive(Debug, Clone)]
pub struct Proof<const LOG4_TREE_SIZE: usize>(pub Vec<[ZkScalar; 3]>);

impl<const LOG4_TREE_SIZE: usize> Default for Proof<LOG4_TREE_SIZE> {
    fn default() -> Self {
        Self(vec![[ZkScalar::zero(); 3]; LOG4_TREE_SIZE])
    }
}
