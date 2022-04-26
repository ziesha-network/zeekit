use crate::Fr;

pub const LOG_TREE_SIZE: usize = 10;

lazy_static! {
    pub static ref MIMC_PARAMS: Vec<Fr> = vec![Fr::from(1u64), Fr::from(2u64)];
}
