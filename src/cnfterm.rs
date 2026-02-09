use crate::error::{OrdinalError, Result};
use crate::ordinal::Ordinal;

/// A term in Cantor Normal Form representing ω^exponent · multiplicity.
///
/// `CnfTerm` is the building block for representing transfinite ordinals. Each term
/// consists of:
/// - An **exponent**: Another ordinal (can be finite or transfinite)
/// - A **multiplicity**: A positive finite coefficient (u32, must be > 0)
///
/// # Mathematical Representation
///
/// A CNF term represents: `ω^exponent · multiplicity`
///
/// For example:
/// - `ω^1 · 1` = ω (omega)
/// - `ω^2 · 3` = ω² · 3 (omega-squared times three)
/// - `ω^0 · 7` = 7 (a finite term)
/// - `ω^ω · 1` = ω^ω (omega to the omega)
///
/// # Cantor Normal Form
///
/// Multiple CNF terms combine additively to represent larger ordinals:
///
/// ```text
/// α = ω^β₁·c₁ + ω^β₂·c₂ + ... + ω^βₙ·cₙ
/// ```
///
/// where β₁ > β₂ > ... > βₙ (strictly decreasing exponents).
///
/// # Invariants
///
/// - **multiplicity must be positive** (> 0) - Enforced by [`CnfTerm::new`]
/// - **exponent can be any ordinal** - Including 0 for finite terms
///
/// # Examples
///
/// ## Creating CNF Terms
///
/// ```
/// use transfinite::{CnfTerm, Ordinal};
///
/// // ω^1 · 1 = ω
/// let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
///
/// // ω^2 · 5 = ω² · 5
/// let omega_squared_term = CnfTerm::new(&Ordinal::new_finite(2), 5).unwrap();
///
/// // ω^0 · 42 = 42 (finite term)
/// let finite_term = CnfTerm::new_finite(42);
/// ```
///
/// ## Combining Terms to Build Ordinals
///
/// ```
/// use transfinite::{CnfTerm, Ordinal};
///
/// // Build ω² + ω·3 + 7
/// let ordinal = Ordinal::new_transfinite(&vec![
///     CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),  // ω²
///     CnfTerm::new(&Ordinal::one(), 3).unwrap(),          // ω·3
///     CnfTerm::new_finite(7),                             // 7
/// ]).unwrap();
///
/// println!("{}", ordinal);  // Prints: ω^2 + ω * 3 + 7
/// ```
///
/// ## Error Handling
///
/// ```
/// use transfinite::{CnfTerm, Ordinal, OrdinalError};
///
/// // Multiplicity must be positive
/// let result = CnfTerm::new(&Ordinal::one(), 0);
/// assert!(result.is_err());
/// ```
///
/// # Display Format
///
/// CNF terms are displayed using ω (omega) notation:
/// - `ω` for ω^1·1
/// - `ω * 3` for ω^1·3
/// - `ω^2` for ω^2·1
/// - `ω^2 * 5` for ω^2·5
/// - `42` for ω^0·42 (finite terms)
///
/// # See Also
///
/// - [`Ordinal`] - The main ordinal type that contains CNF terms
/// - [`Ordinal::new_transfinite`] - Constructs ordinals from CNF terms
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct CnfTerm {
    exponent: Ordinal,
    // u32 provides ~4 billion coefficients while keeping memory compact.
    multiplicity: u32,
}

impl CnfTerm {
    /// Creates a new CNF term with the given exponent and multiplicity.
    ///
    /// # Arguments
    ///
    /// * `exponent` - The exponent of ω in this term (can be any ordinal)
    /// * `multiplicity` - The coefficient (must be positive, > 0)
    ///
    /// # Returns
    ///
    /// - `Ok(CnfTerm)` if multiplicity > 0
    /// - `Err(OrdinalError::CnfTermConstructionError)` if multiplicity == 0
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal};
    ///
    /// // Create ω (omega)
    /// let omega = CnfTerm::new(&Ordinal::one(), 1).unwrap();
    ///
    /// // Create ω² · 5
    /// let term = CnfTerm::new(&Ordinal::new_finite(2), 5).unwrap();
    ///
    /// // Error: multiplicity must be positive
    /// assert!(CnfTerm::new(&Ordinal::one(), 0).is_err());
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if `multiplicity` is 0, as CNF terms must have positive coefficients.
    pub fn new(exponent: &Ordinal, multiplicity: u32) -> Result<Self> {
        if multiplicity == 0 {
            return Err(OrdinalError::CnfTermConstructionError);
        }

        Ok(CnfTerm {
            exponent: exponent.clone(),
            multiplicity,
        })
    }

    /// Creates a finite CNF term (ω^0 · n = n).
    ///
    /// This is a convenience constructor for creating terms that represent finite numbers.
    /// Equivalent to `CnfTerm::new(&Ordinal::Finite(0), n).unwrap()`.
    ///
    /// # Arguments
    ///
    /// * `n` - The finite value (must be > 0)
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::CnfTerm;
    ///
    /// let seven = CnfTerm::new_finite(7);
    /// assert!(seven.is_finite());
    /// assert_eq!(seven.multiplicity(), 7);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `n` is 0, as multiplicity must be positive.
    pub fn new_finite(n: u32) -> Self {
        CnfTerm::new(&Ordinal::Finite(0), n).unwrap()
    }

    /// Returns the exponent of this CNF term.
    ///
    /// For a term ω^exponent · multiplicity, this returns the exponent.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal};
    ///
    /// let term = CnfTerm::new(&Ordinal::new_finite(2), 3).unwrap();
    /// assert_eq!(term.exponent(), Ordinal::new_finite(2));
    /// ```
    ///
    /// # Performance Note
    ///
    /// This method clones the exponent ordinal. For inspection without cloning,
    /// use [`exponent_ref`](Self::exponent_ref) instead.
    pub fn exponent(&self) -> Ordinal {
        self.exponent.clone()
    }

    /// Returns a reference to the exponent of this CNF term.
    ///
    /// This avoids cloning when you only need to inspect or compare the exponent.
    pub fn exponent_ref(&self) -> &Ordinal {
        &self.exponent
    }

    /// Returns the multiplicity (coefficient) of this CNF term.
    ///
    /// For a term ω^exponent · multiplicity, this returns the multiplicity.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal};
    ///
    /// let term = CnfTerm::new(&Ordinal::one(), 5).unwrap();
    /// assert_eq!(term.multiplicity(), 5);
    /// ```
    pub fn multiplicity(&self) -> u32 {
        self.multiplicity
    }

    /// Consumes this term and returns the exponent and multiplicity.
    ///
    /// Use this when you need owned access to the exponent without cloning.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal};
    ///
    /// let term = CnfTerm::new(&Ordinal::one(), 5).unwrap();
    /// let (exponent, multiplicity) = term.into_parts();
    /// assert_eq!(exponent, Ordinal::one());
    /// assert_eq!(multiplicity, 5);
    /// ```
    pub fn into_parts(self) -> (Ordinal, u32) {
        (self.exponent, self.multiplicity)
    }

    /// Returns `true` if this term represents a limit ordinal.
    ///
    /// A CNF term represents a limit ordinal if its exponent is non-zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal};
    ///
    /// // ω^1 · 1 = ω (limit)
    /// let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
    /// assert!(omega_term.is_limit());
    ///
    /// // ω^0 · 5 = 5 (successor)
    /// let finite_term = CnfTerm::new_finite(5);
    /// assert!(!finite_term.is_limit());
    /// ```
    ///
    /// # Mathematical Background
    ///
    /// - ω^0 · c = c (finite, a successor ordinal if c > 0)
    /// - ω^n · c where n > 0 (transfinite, a limit ordinal)
    pub fn is_limit(&self) -> bool {
        // A CNF term represents a limit ordinal if its exponent is non-zero
        // ω^0 · c = c (finite, successor ordinal)
        // ω^n · c where n > 0 (transfinite, limit ordinal)
        !matches!(self.exponent, Ordinal::Finite(0))
    }

    /// Returns `true` if this term represents a successor ordinal.
    ///
    /// A CNF term represents a successor ordinal if its exponent is zero (i.e., it's finite).
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal};
    ///
    /// // ω^0 · 5 = 5 (successor)
    /// let finite_term = CnfTerm::new_finite(5);
    /// assert!(finite_term.is_successor());
    ///
    /// // ω^1 · 1 = ω (limit)
    /// let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
    /// assert!(!omega_term.is_successor());
    /// ```
    pub fn is_successor(&self) -> bool {
        // A CNF term represents a successor ordinal if its exponent is zero
        matches!(self.exponent, Ordinal::Finite(0))
    }

    /// Returns `true` if this term represents a finite ordinal.
    ///
    /// Equivalent to checking if the exponent is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{CnfTerm, Ordinal};
    ///
    /// let finite = CnfTerm::new_finite(42);
    /// assert!(finite.is_finite());
    ///
    /// let omega = CnfTerm::new(&Ordinal::one(), 1).unwrap();
    /// assert!(!omega.is_finite());
    /// ```
    pub fn is_finite(&self) -> bool {
        matches!(self.exponent, Ordinal::Finite(0))
    }
}

impl std::fmt::Display for CnfTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let exponent = self.exponent_ref();

        if matches!(exponent, Ordinal::Finite(0)) {
            return write!(f, "{}", self.multiplicity);
        }

        write!(f, "ω")?;

        if !matches!(exponent, Ordinal::Finite(1)) {
            write!(f, "^{exponent}")?;
        }

        if self.multiplicity != 1 {
            write!(f, " * {}", self.multiplicity)?;
        }

        Ok(())
    }
}

impl PartialOrd for CnfTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CnfTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.exponent_ref()
            .cmp(other.exponent_ref())
            .then_with(|| self.multiplicity.cmp(&other.multiplicity))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_cnf_term() {
        let one = Ordinal::one();
        let cnf_term = CnfTerm::new(&one, 1).unwrap();
        assert_eq!(cnf_term.exponent(), one);
        assert_eq!(cnf_term.multiplicity(), 1);
    }

    #[test]
    fn test_cnf_term_is_limit() {
        let one = Ordinal::one();
        let cnf_term = CnfTerm::new(&one, 1).unwrap();
        assert!(cnf_term.is_limit());
    }

    #[test]
    fn test_cnf_term_is_successor() {
        let one = Ordinal::one();
        let cnf_term = CnfTerm::new(&one, 1).unwrap();
        assert!(!cnf_term.is_successor());
    }

    #[test]
    fn test_cnf_term_is_finite() {
        let finite = Ordinal::new_finite(0);
        let cnf_term = CnfTerm::new(&finite, 1).unwrap();
        assert!(cnf_term.is_finite());
    }

    #[test]
    fn test_cnf_term_display() {
        let one = Ordinal::one();
        let cnf_term = CnfTerm::new(&one, 1).unwrap();
        assert_eq!(format!("{}", cnf_term), "ω");
    }

    #[test]
    fn test_cnf_term_display_with_multiplicity() {
        let one = Ordinal::one();
        let cnf_term = CnfTerm::new(&one, 2).unwrap();
        assert_eq!(format!("{}", cnf_term), "ω * 2");
    }

    #[test]
    fn test_cnf_term_display_with_exponent() {
        let two = Ordinal::new_finite(2);
        let cnf_term = CnfTerm::new(&two, 1).unwrap();
        assert_eq!(format!("{}", cnf_term), "ω^2");
    }

    #[test]

    fn test_partial_eq() {
        let one = Ordinal::one();
        let cnf_term1 = CnfTerm::new(&one, 1).unwrap();
        let cnf_term2 = CnfTerm::new(&one, 1).unwrap();
        assert_eq!(cnf_term1, cnf_term2);
    }

    #[test]
    fn test_partial_eq_different_exponents() {
        let one = Ordinal::one();
        let two = Ordinal::new_finite(2);
        let cnf_term1 = CnfTerm::new(&one, 1).unwrap();
        let cnf_term2 = CnfTerm::new(&two, 1).unwrap();
        assert_ne!(cnf_term1, cnf_term2);
    }

    #[test]
    fn test_partial_eq_different_multiplicities() {
        let one = Ordinal::one();
        let cnf_term1 = CnfTerm::new(&one, 1).unwrap();
        let cnf_term2 = CnfTerm::new(&one, 2).unwrap();
        assert_ne!(cnf_term1, cnf_term2);
    }

    #[test]
    fn test_ord_same_exponent() {
        let one = Ordinal::one();
        let cnf_term1 = CnfTerm::new(&one, 1).unwrap();
        let cnf_term2 = CnfTerm::new(&one, 2).unwrap();
        assert!(cnf_term1 < cnf_term2);
    }

    #[test]
    fn test_ord_different_exponents() {
        let one = Ordinal::one();
        let two = Ordinal::new_finite(2);
        let cnf_term1 = CnfTerm::new(&one, 1).unwrap();
        let cnf_term2 = CnfTerm::new(&two, 1).unwrap();
        assert!(cnf_term1 < cnf_term2);
    }

    #[test]
    fn test_partial_ord_same_exponent() {
        let one = Ordinal::one();
        let cnf_term1 = CnfTerm::new(&one, 1).unwrap();
        let cnf_term2 = CnfTerm::new(&one, 2).unwrap();
        assert!(cnf_term1.partial_cmp(&cnf_term2).unwrap() == std::cmp::Ordering::Less);
    }

    #[test]
    fn test_partial_ord_different_exponents() {
        let one = Ordinal::one();
        let two = Ordinal::new_finite(2);
        let cnf_term1 = CnfTerm::new(&one, 1).unwrap();
        let cnf_term2 = CnfTerm::new(&two, 1).unwrap();
        assert!(cnf_term1.partial_cmp(&cnf_term2).unwrap() == std::cmp::Ordering::Less);
    }

    #[test]
    fn test_nested_transfinite_exponent() {
        // Term with w^w as exponent
        let omega = Ordinal::omega();
        let term = CnfTerm::new(&omega, 1).unwrap();
        assert!(term.is_limit());
        assert!(!term.is_finite());
        assert_eq!(term.exponent(), omega);
    }

    #[test]
    fn test_deeply_nested_exponent_display() {
        // Term w^(w^2) should display correctly
        let omega_squared = Ordinal::builder().omega_power(2).build().unwrap();
        let term = CnfTerm::new(&omega_squared, 1).unwrap();
        assert_eq!(format!("{}", term), "ω^ω^2");
    }

    #[test]
    fn test_exponent_ref_avoids_clone() {
        let omega = Ordinal::omega();
        let term = CnfTerm::new(&omega, 5).unwrap();
        // exponent_ref returns a reference, no cloning
        assert_eq!(term.exponent_ref(), &omega);
        assert_eq!(*term.exponent_ref(), term.exponent());
    }

    #[test]
    fn test_large_multiplicity() {
        let one = Ordinal::one();
        let term = CnfTerm::new(&one, u32::MAX).unwrap();
        assert_eq!(term.multiplicity(), u32::MAX);
    }
}
