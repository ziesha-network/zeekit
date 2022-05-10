use crate::Fr;

pub const LOG_TREE_SIZE: usize = 29;

lazy_static! {
    pub static ref MIMC_PARAMS: Vec<Fr> = (0..322).map(|i| Fr::from(i)).collect();
}
