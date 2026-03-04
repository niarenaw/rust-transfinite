use thiserror::Error;

/// Errors that can occur during ordinal construction or operations.
///
/// This enum represents all error conditions that can arise when constructing
/// or manipulating ordinal numbers in this library.
///
/// # Examples
///
/// ```
/// use transfinite::{CnfTerm, Ordinal, OrdinalError};
///
/// // CnfTermConstructionError: multiplicity must be positive
/// let result = CnfTerm::new(&Ordinal::one(), 0);
/// assert!(matches!(result, Err(OrdinalError::CnfTermConstructionError)));
///
/// // TransfiniteConstructionError: empty terms
/// let result = Ordinal::new_transfinite(&vec![]);
/// assert!(matches!(result, Err(OrdinalError::TransfiniteConstructionError)));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum OrdinalError {
    /// Error when constructing a CNF term with invalid parameters.
    ///
    /// This error occurs when attempting to create a [`CnfTerm`](crate::CnfTerm)
    /// with a multiplicity of 0. In Cantor Normal Form, all coefficients must be
    /// positive (non-zero).
    ///
    /// # Common Causes
    ///
    /// - Calling `CnfTerm::new(exponent, 0)`
    /// - Mathematical operations that would produce a zero coefficient
    ///
    /// # How to Avoid
    ///
    /// Always ensure multiplicities are at least 1. If you need to represent "nothing,"
    /// use an empty vector of terms or a different ordinal representation.
    ///
    /// # Example
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal, OrdinalError};
    ///
    /// // This will fail because multiplicity is 0
    /// let result = CnfTerm::new(&Ordinal::one(), 0);
    /// assert!(result.is_err());
    ///
    /// // Use a positive multiplicity instead
    /// let term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
    /// ```
    #[error("CNF terms must have a non-zero multiplicity.")]
    CnfTermConstructionError,

    /// Error when constructing a transfinite ordinal with invalid terms.
    ///
    /// This error occurs when attempting to create a transfinite [`Ordinal`](crate::Ordinal)
    /// with terms that violate CNF requirements.
    ///
    /// # Common Causes
    ///
    /// 1. **Empty terms vector**: Transfinite ordinals must have at least one term
    /// 2. **Leading term is finite**: The first term must have a non-zero exponent
    ///    (use [`Ordinal::new_finite`](crate::Ordinal::new_finite) for finite ordinals)
    ///
    /// # How to Avoid
    ///
    /// - Ensure terms vector is non-empty
    /// - Ensure the leading (first) term has exponent > 0
    /// - For finite ordinals, use `Ordinal::new_finite()` instead
    /// - Future versions will also enforce strictly decreasing exponent order
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{Ordinal, CnfTerm, OrdinalError};
    ///
    /// // Error: empty terms
    /// let result = Ordinal::new_transfinite(&vec![]);
    /// assert!(result.is_err());
    ///
    /// // Error: leading term is finite (exponent 0)
    /// let finite_term = CnfTerm::new_finite(42);
    /// let result = Ordinal::new_transfinite(&vec![finite_term]);
    /// assert!(result.is_err());
    ///
    /// // Correct: leading term is transfinite
    /// let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
    /// let omega = Ordinal::new_transfinite(&vec![omega_term]).unwrap();
    /// ```
    #[error("Terms in a CNF decomposition must be non-decreasing and the leading term must be transfinite.")]
    TransfiniteConstructionError,
}

/// A specialized [`Result`](std::result::Result) type for ordinal operations.
///
/// This is a type alias for `Result<T, OrdinalError>`, providing a convenient
/// shorthand for functions that can fail with ordinal-specific errors.
///
/// # Examples
///
/// ```
/// use transfinite::{Result, Ordinal, CnfTerm};
///
/// fn create_omega_squared() -> Result<Ordinal> {
///     let term = CnfTerm::new(&Ordinal::new_finite(2), 1)?;
///     Ordinal::new_transfinite(&vec![term])
/// }
///
/// let omega_squared = create_omega_squared().unwrap();
/// ```
pub type Result<T> = std::result::Result<T, OrdinalError>;
