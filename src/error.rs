use thiserror::Error;

#[derive(Debug, Error)]
pub enum OrdinalError {
    #[error("CNF terms must have a non-zero multiplicity.")]
    CnfTermConstructionError,
    #[error("Terms in a CNF decomposition must be non-decreasing and the leading term must be transfinite.")]
    TransfiniteConstructionError,
}

pub type Result<T> = std::result::Result<T, OrdinalError>;
