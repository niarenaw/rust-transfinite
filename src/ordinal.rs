use num_traits::Pow;
use std::ops::{Add, Mul};

use crate::cnfterm::CnfTerm;
use crate::error::{OrdinalError, Result};

/// An ordinal number, either finite or transfinite.
///
/// Ordinals extend the natural numbers to describe order types of well-ordered sets.
/// This type represents ordinals up to ε₀ (epsilon-zero) using Cantor Normal Form.
///
/// # Variants
///
/// - [`Finite(u32)`](Ordinal::Finite) - Natural numbers: 0, 1, 2, 3, ...
/// - [`Transfinite(Vec<CnfTerm>)`](Ordinal::Transfinite) - Infinite ordinals ≥ ω in Cantor Normal Form
///
/// # Cantor Normal Form
///
/// Transfinite ordinals are stored as a sum of terms:
///
/// ```text
/// α = ω^β₁·c₁ + ω^β₂·c₂ + ... + ω^βₙ·cₙ
/// ```
///
/// where β₁ > β₂ > ... > βₙ (strictly decreasing exponents) and c₁, c₂, ..., cₙ
/// are positive finite coefficients.
///
/// # Invariants
///
/// - Finite ordinals must use the `Finite` variant (never represented as transfinite with exponent 0)
/// - CNF terms must be in strictly decreasing order by exponent
/// - All CNF term multiplicities must be positive (non-zero)
/// - The leading CNF term must have a non-finite exponent
///
/// # Examples
///
/// ## Creating Ordinals
///
/// ```
/// use transfinite::Ordinal;
///
/// // Finite ordinals
/// let zero = Ordinal::zero();
/// let five = Ordinal::new_finite(5);
///
/// // Transfinite ordinals
/// let omega = Ordinal::omega();                    // ω
/// let omega_plus_one = omega.successor();          // ω + 1
/// ```
///
/// ## Arithmetic Operations
///
/// ```
/// use transfinite::Ordinal;
/// use num_traits::Pow;
///
/// let omega = Ordinal::omega();
/// let two = Ordinal::new_finite(2);
///
/// // Addition (non-commutative!)
/// assert_eq!(two.clone() + omega.clone(), omega);           // 2 + ω = ω
/// assert_ne!(omega.clone() + two.clone(), omega);           // ω + 2 ≠ ω
///
/// // Multiplication (non-commutative!)
/// assert_eq!(two.clone() * omega.clone(), omega);           // 2 · ω = ω
/// assert_ne!(omega.clone() * two.clone(), omega);           // ω · 2 = ω + ω ≠ ω
///
/// // Exponentiation
/// let omega_squared = omega.clone().pow(two);               // ω²
/// ```
///
/// ## Classification
///
/// ```
/// use transfinite::Ordinal;
///
/// let zero = Ordinal::zero();
/// let one = Ordinal::one();
/// let omega = Ordinal::omega();
///
/// // Limit ordinals have no immediate predecessor
/// assert!(zero.is_limit());
/// assert!(omega.is_limit());
///
/// // Successor ordinals are of the form α + 1
/// assert!(one.is_successor());
/// assert!(omega.successor().is_successor());
/// ```
///
/// # Ordinal Arithmetic
///
/// Ordinal arithmetic differs from standard arithmetic:
///
/// - **Addition is not commutative**: `α + β` may not equal `β + α`
/// - **Multiplication is not commutative**: `α · β` may not equal `β · α`
/// - **Both are associative**: `(α + β) + γ = α + (β + γ)` and `(α · β) · γ = α · (β · γ)`
///
/// The right operand "dominates" in addition and multiplication for transfinite ordinals.
///
/// # Performance
///
/// - Finite ordinals use native `u32` arithmetic (very fast)
/// - Transfinite ordinals allocate a vector of CNF terms (typically 1-3 terms)
/// - Arithmetic operations currently clone data; future optimizations planned
///
/// # See Also
///
/// - [`CnfTerm`] - Individual terms in Cantor Normal Form
/// - [`OrdinalError`] - Errors that can occur during construction
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Ordinal {
    /// A finite natural number (0, 1, 2, 3, ...).
    ///
    /// Stored as a native `u32` for efficiency.
    Finite(u32),

    /// A transfinite ordinal (ω, ω+1, ω², ω^ω, ...) represented in Cantor Normal Form.
    ///
    /// Stored as a vector of [`CnfTerm`]s in strictly decreasing order by exponent.
    Transfinite(Vec<CnfTerm>),
}

impl Ordinal {
    /// Creates a finite ordinal from a natural number.
    ///
    /// This is the most efficient way to create small ordinals, as they are stored
    /// as native `u32` values.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let zero = Ordinal::new_finite(0);
    /// let five = Ordinal::new_finite(5);
    /// let large = Ordinal::new_finite(1_000_000);
    ///
    /// assert!(zero.is_finite());
    /// assert!(five.is_finite());
    /// ```
    ///
    /// # Limits
    ///
    /// Finite ordinals are limited to `u32::MAX` (4,294,967,295). For ordinals beyond
    /// this, you need transfinite ordinals like ω.
    pub fn new_finite(n: u32) -> Self {
        Ordinal::Finite(n)
    }

    /// Creates a transfinite ordinal from Cantor Normal Form terms.
    ///
    /// The terms must be provided in strictly decreasing order by exponent, and the
    /// leading term must be transfinite (have a non-zero exponent).
    ///
    /// # Arguments
    ///
    /// * `terms` - A vector of [`CnfTerm`]s representing the ordinal in CNF
    ///
    /// # Returns
    ///
    /// - `Ok(Ordinal)` if the terms are valid
    /// - `Err(OrdinalError::TransfiniteConstructionError)` if:
    ///   - The terms vector is empty
    ///   - The leading term has exponent 0 (use [`Ordinal::new_finite`] instead)
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{Ordinal, CnfTerm};
    ///
    /// // Create ω² (omega squared)
    /// let omega_squared = Ordinal::new_transfinite(&vec![
    ///     CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap()
    /// ]).unwrap();
    ///
    /// // Create ω² + ω·3 + 7
    /// let complex = Ordinal::new_transfinite(&vec![
    ///     CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),  // ω²
    ///     CnfTerm::new(&Ordinal::one(), 3).unwrap(),          // ω·3
    ///     CnfTerm::new_finite(7),                             // 7
    /// ]).unwrap();
    ///
    /// assert!(omega_squared.is_transfinite());
    /// assert!(complex.is_transfinite());
    /// ```
    ///
    /// # Errors
    ///
    /// ```
    /// use transfinite::{Ordinal, CnfTerm, OrdinalError};
    ///
    /// // Empty terms vector
    /// assert!(Ordinal::new_transfinite(&vec![]).is_err());
    ///
    /// // Leading term has exponent 0 (this should be finite)
    /// let finite_term = CnfTerm::new_finite(42);
    /// assert!(Ordinal::new_transfinite(&vec![finite_term]).is_err());
    /// ```
    ///
    /// # Validation
    ///
    /// This method validates that:
    /// 1. The terms vector is non-empty
    /// 2. The leading term has a non-zero exponent (is transfinite)
    /// 3. Terms are in strictly decreasing order by exponent (CNF requirement)
    ///
    /// If any validation fails, returns `Err(OrdinalError::TransfiniteConstructionError)`.
    ///
    /// # See Also
    ///
    /// For a more ergonomic API, see [`Ordinal::builder`] which provides a fluent
    /// interface for constructing ordinals without manually creating [`CnfTerm`]s.
    pub fn new_transfinite(terms: &[CnfTerm]) -> Result<Self> {
        Self::validate_cnf_terms(terms)?;
        Ok(Ordinal::Transfinite(terms.to_vec()))
    }

    /// Wraps an already-validated `Vec<CnfTerm>` into a `Transfinite` ordinal.
    ///
    /// Skips validation in release builds. In debug builds, asserts that the
    /// terms satisfy CNF ordering as a safety net for internal arithmetic.
    pub(crate) fn transfinite_unchecked(terms: Vec<CnfTerm>) -> Self {
        debug_assert!(
            Self::validate_cnf_terms(&terms).is_ok(),
            "internal arithmetic produced invalid CNF: {terms:?}"
        );
        Ordinal::Transfinite(terms)
    }

    /// Validates that CNF terms satisfy ordering and leading-term constraints.
    fn validate_cnf_terms(terms: &[CnfTerm]) -> Result<()> {
        match terms.first() {
            None => return Err(OrdinalError::TransfiniteConstructionError),
            Some(term) if term.is_finite() => {
                return Err(OrdinalError::TransfiniteConstructionError);
            }
            _ => {}
        }

        for pair in terms.windows(2) {
            if pair[0].exponent_ref() <= pair[1].exponent_ref() {
                return Err(OrdinalError::TransfiniteConstructionError);
            }
        }

        Ok(())
    }

    /// Returns `true` if this is a limit ordinal.
    ///
    /// A limit ordinal has no immediate predecessor. Informally, it's reached "from below"
    /// by an infinite sequence rather than by adding 1 to some ordinal.
    ///
    /// Limit ordinals include: 0, ω, ω·2, ω², ω^ω, etc.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let zero = Ordinal::zero();
    /// let one = Ordinal::one();
    /// let omega = Ordinal::omega();
    ///
    /// assert!(zero.is_limit());        // 0 is a limit ordinal
    /// assert!(!one.is_limit());        // 1 is a successor (0 + 1)
    /// assert!(omega.is_limit());       // ω is a limit ordinal
    /// assert!(!omega.successor().is_limit());  // ω+1 is a successor
    /// ```
    ///
    /// # Mathematical Definition
    ///
    /// An ordinal α is a limit ordinal if α ≠ β+1 for any ordinal β.
    /// Equivalently, α is a limit if it equals the supremum of all ordinals less than α.
    pub fn is_limit(&self) -> bool {
        match self {
            Ordinal::Finite(0) => true,
            Ordinal::Finite(_) => false,
            Ordinal::Transfinite(terms) => terms
                .last()
                .expect("transfinite ordinals always have at least one CNF term")
                .is_limit(),
        }
    }

    /// Returns `true` if this is a successor ordinal.
    ///
    /// A successor ordinal has an immediate predecessor and is of the form α+1 for some
    /// ordinal α.
    ///
    /// Successor ordinals include: 1, 2, 3, ..., ω+1, ω+2, ..., ω²+1, etc.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let one = Ordinal::one();
    /// let five = Ordinal::new_finite(5);
    /// let omega = Ordinal::omega();
    /// let omega_plus_one = omega.successor();
    ///
    /// assert!(one.is_successor());           // 1 = 0 + 1
    /// assert!(five.is_successor());          // 5 = 4 + 1
    /// assert!(!omega.is_successor());        // ω is a limit
    /// assert!(omega_plus_one.is_successor()); // ω+1 = ω + 1
    /// ```
    ///
    /// # Relationship to Limit Ordinals
    ///
    /// Every ordinal is either a limit ordinal or a successor ordinal (never both).
    /// This method returns `!self.is_limit()`.
    pub fn is_successor(&self) -> bool {
        !self.is_limit()
    }

    /// Returns the successor of this ordinal (α + 1).
    ///
    /// For any ordinal α, the successor α+1 is the smallest ordinal greater than α.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let zero = Ordinal::zero();
    /// let one = Ordinal::one();
    /// let omega = Ordinal::omega();
    ///
    /// assert_eq!(zero.successor(), one);
    /// assert_eq!(one.successor(), Ordinal::new_finite(2));
    ///
    /// // For transfinite ordinals
    /// let omega_plus_one = omega.successor();
    /// assert!(omega_plus_one.is_successor());
    /// assert!(omega_plus_one > omega);
    /// ```
    ///
    /// # Implementation Notes
    ///
    /// - For finite ordinals: returns `n + 1`
    /// - For transfinite ordinals: appends a finite term `+1` to the CNF representation
    ///   (or increments the existing finite trailing term)
    ///
    /// # Overflow Behavior
    ///
    /// Uses saturating arithmetic - calling successor on `Ordinal::new_finite(u32::MAX)`
    /// will return `u32::MAX` (it saturates at the boundary).
    /// In practice, ordinals this large should be represented as transfinite.
    pub fn successor(&self) -> Self {
        match self {
            // Use saturating_add to prevent overflow
            Ordinal::Finite(n) => Ordinal::new_finite(n.saturating_add(1)),
            Ordinal::Transfinite(terms) => {
                let mut new_terms = terms.clone();
                if let Some(last_term) = new_terms.pop() {
                    if last_term.is_finite() {
                        // Last term is finite (e.g., ω + 5), increment it to ω + 6
                        // Use saturating_add to prevent overflow
                        new_terms.push(CnfTerm::new_finite(
                            last_term.multiplicity().saturating_add(1),
                        ));
                    } else {
                        // Last term is transfinite (e.g., ω²), append +1
                        new_terms.push(last_term);
                        new_terms.push(CnfTerm::new_finite(1));
                    }
                }
                Ordinal::Transfinite(new_terms)
            }
        }
    }

    /// Returns `true` if this is a finite ordinal (a natural number).
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let five = Ordinal::new_finite(5);
    /// let omega = Ordinal::omega();
    ///
    /// assert!(five.is_finite());
    /// assert!(!omega.is_finite());
    /// ```
    pub fn is_finite(&self) -> bool {
        matches!(self, Ordinal::Finite(_))
    }

    /// Returns `true` if this is a transfinite ordinal (≥ ω).
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let five = Ordinal::new_finite(5);
    /// let omega = Ordinal::omega();
    ///
    /// assert!(!five.is_transfinite());
    /// assert!(omega.is_transfinite());
    /// ```
    pub fn is_transfinite(&self) -> bool {
        matches!(self, Ordinal::Transfinite(_))
    }

    /// Returns `true` if this is the ordinal zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// assert!(Ordinal::zero().is_zero());
    /// assert!(!Ordinal::one().is_zero());
    /// assert!(!Ordinal::omega().is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        matches!(self, Ordinal::Finite(0))
    }

    /// Returns `true` if this is the ordinal one.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// assert!(Ordinal::one().is_one());
    /// assert!(!Ordinal::zero().is_one());
    /// assert!(!Ordinal::omega().is_one());
    /// ```
    pub fn is_one(&self) -> bool {
        matches!(self, Ordinal::Finite(1))
    }

    /// Returns the leading (highest-order) CNF term, if this is a transfinite ordinal.
    ///
    /// For transfinite ordinals in CNF, the leading term has the largest exponent and
    /// dominates the value of the ordinal.
    ///
    /// # Returns
    ///
    /// - `Some(CnfTerm)` - The leading term for transfinite ordinals
    /// - `None` - For finite ordinals
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{Ordinal, CnfTerm};
    ///
    /// let omega = Ordinal::omega();
    /// let leading = omega.leading_cnf_term().unwrap();
    /// assert_eq!(leading.exponent(), Ordinal::one());
    /// assert_eq!(leading.multiplicity(), 1);
    ///
    /// // Finite ordinals have no CNF terms
    /// let five = Ordinal::new_finite(5);
    /// assert!(five.leading_cnf_term().is_none());
    /// ```
    pub fn leading_cnf_term(&self) -> Option<CnfTerm> {
        match self {
            Ordinal::Finite(_) => None,
            Ordinal::Transfinite(terms) => terms.first().cloned(),
        }
    }

    /// Returns a reference to the leading CNF term, avoiding the clone that
    /// [`leading_cnf_term`](Self::leading_cnf_term) performs.
    ///
    /// Prefer this method when you only need to inspect the leading term and
    /// do not need to keep an owned copy.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega = Ordinal::omega();
    /// let leading = omega.leading_cnf_term_ref().unwrap();
    /// assert_eq!(leading.multiplicity(), 1);
    /// ```
    pub fn leading_cnf_term_ref(&self) -> Option<&CnfTerm> {
        match self {
            Ordinal::Finite(_) => None,
            Ordinal::Transfinite(terms) => terms.first(),
        }
    }

    /// Returns the trailing (lowest-order) CNF term, if this is a transfinite ordinal.
    ///
    /// The trailing term has the smallest exponent in the CNF representation. This term
    /// determines whether the ordinal is a limit or successor.
    ///
    /// # Returns
    ///
    /// - `Some(CnfTerm)` - The trailing term for transfinite ordinals
    /// - `None` - For finite ordinals
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{Ordinal, CnfTerm};
    ///
    /// // ω² + ω·3 + 7
    /// let ordinal = Ordinal::new_transfinite(&vec![
    ///     CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),  // ω²
    ///     CnfTerm::new(&Ordinal::one(), 3).unwrap(),          // ω·3
    ///     CnfTerm::new_finite(7),                             // 7 (trailing term)
    /// ]).unwrap();
    ///
    /// let trailing = ordinal.trailing_cnf_term().unwrap();
    /// assert_eq!(trailing.exponent(), Ordinal::zero());
    /// assert_eq!(trailing.multiplicity(), 7);
    /// ```
    pub fn trailing_cnf_term(&self) -> Option<CnfTerm> {
        match self {
            Ordinal::Finite(_) => None,
            Ordinal::Transfinite(terms) => terms.last().cloned(),
        }
    }

    /// Reference-returning variant of [`trailing_cnf_term`](Self::trailing_cnf_term);
    /// see [`leading_cnf_term_ref`](Self::leading_cnf_term_ref) for the rationale.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega_plus_one = Ordinal::omega().successor();
    /// let trailing = omega_plus_one.trailing_cnf_term_ref().unwrap();
    /// assert_eq!(trailing.multiplicity(), 1);
    /// ```
    pub fn trailing_cnf_term_ref(&self) -> Option<&CnfTerm> {
        match self {
            Ordinal::Finite(_) => None,
            Ordinal::Transfinite(terms) => terms.last(),
        }
    }

    /// Returns all CNF terms for transfinite ordinals.
    ///
    /// Returns a vector of all terms in the Cantor Normal Form representation,
    /// in decreasing order by exponent.
    ///
    /// # Returns
    ///
    /// - `Some(Vec<CnfTerm>)` - All CNF terms for transfinite ordinals
    /// - `None` - For finite ordinals
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::{Ordinal, CnfTerm};
    ///
    /// let omega = Ordinal::omega();
    /// let terms = omega.cnf_terms().unwrap();
    /// assert_eq!(terms.len(), 1);
    ///
    /// // Finite ordinals return None
    /// let five = Ordinal::new_finite(5);
    /// assert!(five.cnf_terms().is_none());
    /// ```
    ///
    /// # Performance Note
    ///
    /// This method clones the entire vector of terms. For inspection without cloning,
    /// consider using [`leading_cnf_term`](Self::leading_cnf_term) or
    /// [`trailing_cnf_term`](Self::trailing_cnf_term).
    pub fn cnf_terms(&self) -> Option<Vec<CnfTerm>> {
        match self {
            Ordinal::Finite(_) => None,
            Ordinal::Transfinite(terms) => Some(terms.clone()),
        }
    }

    /// Returns an iterator over the CNF terms without cloning.
    ///
    /// For finite ordinals the iterator is empty. For transfinite ordinals it
    /// yields each term in CNF order (decreasing exponent). Prefer this over
    /// [`cnf_terms`](Self::cnf_terms) when you only need to walk the terms
    /// once.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega = Ordinal::omega();
    /// assert_eq!(omega.cnf_terms_iter().count(), 1);
    ///
    /// let five = Ordinal::new_finite(5);
    /// assert_eq!(five.cnf_terms_iter().count(), 0);
    /// ```
    pub fn cnf_terms_iter(&self) -> std::slice::Iter<'_, CnfTerm> {
        match self {
            Ordinal::Finite(_) => [].iter(),
            Ordinal::Transfinite(terms) => terms.iter(),
        }
    }

    /// Returns the ordinal zero (0).
    ///
    /// Zero is the smallest ordinal and the only finite limit ordinal.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let zero = Ordinal::zero();
    /// assert_eq!(zero, Ordinal::new_finite(0));
    /// assert!(zero.is_limit());
    /// assert!(zero.is_finite());
    /// ```
    pub const fn zero() -> Self {
        Ordinal::Finite(0)
    }

    /// Returns the ordinal one (1).
    ///
    /// One is the first successor ordinal (0 + 1).
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let one = Ordinal::one();
    /// assert_eq!(one, Ordinal::new_finite(1));
    /// assert_eq!(one, Ordinal::zero().successor());
    /// assert!(one.is_successor());
    /// ```
    pub const fn one() -> Self {
        Ordinal::Finite(1)
    }

    /// Returns omega (ω), the first infinite ordinal.
    ///
    /// Omega represents the order type of the natural numbers. It is the smallest
    /// transfinite ordinal and the first limit ordinal after 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega = Ordinal::omega();
    /// assert!(omega.is_transfinite());
    /// assert!(omega.is_limit());
    ///
    /// // All finite ordinals are less than omega
    /// let million = Ordinal::new_finite(1_000_000);
    /// assert!(million < omega);
    ///
    /// // Arithmetic with omega
    /// let omega_plus_one = omega.successor();
    /// let omega_times_two = omega.clone() * Ordinal::new_finite(2);
    /// ```
    ///
    /// # Representation
    ///
    /// Omega is represented in CNF as ω^1·1, i.e., a single term with exponent 1
    /// and multiplicity 1.
    pub fn omega() -> Self {
        Ordinal::Transfinite(vec![
            CnfTerm::new(&Ordinal::one(), 1).expect("omega term has positive multiplicity")
        ])
    }

    /// Creates a new [`OrdinalBuilder`](crate::OrdinalBuilder) for fluent ordinal construction.
    ///
    /// # Example
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// // Build w^2 + w*3 + 7
    /// let ordinal = Ordinal::builder()
    ///     .omega_power(2)
    ///     .omega_times(3)
    ///     .plus(7)
    ///     .build()
    ///     .unwrap();
    /// ```
    pub fn builder() -> crate::OrdinalBuilder {
        crate::OrdinalBuilder::new()
    }
}

/// Formats the ordinal in a human-readable mathematical notation.
///
/// # Format
///
/// - Finite ordinals display as their numeric value: `0`, `5`, `42`
/// - Transfinite ordinals display in CNF notation: `ω`, `ω^2`, `ω^2 + ω*3 + 7`
/// - Terms are joined with ` + ` and displayed in decreasing exponent order
///
/// # Examples
///
/// ```
/// use transfinite::Ordinal;
///
/// assert_eq!(format!("{}", Ordinal::zero()), "0");
/// assert_eq!(format!("{}", Ordinal::omega()), "ω");
///
/// let complex = Ordinal::builder()
///     .omega_power(2)
///     .omega_times(3)
///     .plus(7)
///     .build()
///     .unwrap();
/// assert_eq!(format!("{}", complex), "ω^2 + ω * 3 + 7");
/// ```
impl std::fmt::Display for Ordinal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ordinal::Finite(n) => write!(f, "{n}"),
            Ordinal::Transfinite(terms) => {
                for (i, term) in terms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " + ")?;
                    }
                    write!(f, "{term}")?;
                }
                Ok(())
            }
        }
    }
}

impl From<u32> for Ordinal {
    fn from(n: u32) -> Self {
        Ordinal::new_finite(n)
    }
}

/// Identity for ordinal addition. Enables generic algorithms that need a
/// zero value via [`num_traits::Zero`].
impl num_traits::Zero for Ordinal {
    fn zero() -> Self {
        Ordinal::zero()
    }

    fn is_zero(&self) -> bool {
        Ordinal::is_zero(self)
    }
}

/// Identity for ordinal multiplication. Enables generic algorithms that need
/// a one value via [`num_traits::One`].
impl num_traits::One for Ordinal {
    fn one() -> Self {
        Ordinal::one()
    }

    fn is_one(&self) -> bool {
        Ordinal::is_one(self)
    }
}

impl PartialOrd for Ordinal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ordinal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Ordinal::Finite(m), Ordinal::Finite(n)) => m.cmp(n),
            (Ordinal::Finite(_), Ordinal::Transfinite(_)) => std::cmp::Ordering::Less,
            (Ordinal::Transfinite(_), Ordinal::Finite(_)) => std::cmp::Ordering::Greater,
            (Ordinal::Transfinite(terms_lhs), Ordinal::Transfinite(terms_rhs)) => {
                for (term_lhs, term_rhs) in terms_lhs.iter().zip(terms_rhs.iter()) {
                    let cmp = term_lhs.cmp(term_rhs);
                    if cmp != std::cmp::Ordering::Equal {
                        return cmp;
                    }
                }
                terms_lhs.len().cmp(&terms_rhs.len())
            }
        }
    }
}

/// Ordinal addition is associative but NOT commutative for transfinite ordinals.
/// For example, `1 + w = w` but `w + 1 = w + 1`.
///
/// # Overflow Behavior
///
/// Finite ordinal addition uses saturating arithmetic. Adding two finite ordinals
/// that would exceed `u32::MAX` returns `u32::MAX` instead of panicking.
impl Add<Ordinal> for Ordinal {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            // Case 1: Finite + Finite behaves like integer addition
            // Use saturating arithmetic to prevent overflow
            (Ordinal::Finite(m), Ordinal::Finite(n)) => Ordinal::new_finite(m.saturating_add(n)),

            // Case 2: Finite + Transfinite returns the Transfinite ordinal (move rhs)
            (Ordinal::Finite(_), rhs_transfinite) => rhs_transfinite,

            // Case 3: Transfinite + Finite adds finite to the trailing cnf term
            (Ordinal::Transfinite(mut terms), Ordinal::Finite(n)) => {
                // Adding zero doesn't change the ordinal (move self)
                if n == 0 {
                    return Ordinal::Transfinite(terms);
                }

                // Modify terms in place - no cloning needed!
                if let Some(last_term) = terms.last() {
                    if last_term.is_finite() {
                        // Replace the last finite term with the sum
                        // Use saturating_add to prevent overflow
                        let new_mult = last_term.multiplicity().saturating_add(n);
                        let last_idx = terms.len() - 1;
                        terms[last_idx] = CnfTerm::new_finite(new_mult);
                    } else {
                        // Last term is transfinite, append new finite term
                        terms.push(CnfTerm::new_finite(n));
                    }
                }
                Ordinal::Transfinite(terms) // Return modified terms (no clone needed)
            }

            // Case 4: Transfinite + Transfinite - CNF cases
            (Ordinal::Transfinite(terms_lhs), Ordinal::Transfinite(terms_rhs)) => {
                let leading_exponent_rhs = terms_rhs[0].exponent();
                let leading_mult_rhs = terms_rhs[0].multiplicity();

                if terms_lhs[0].exponent_ref() < &leading_exponent_rhs {
                    // rhs dominates, return it (move rhs)
                    Ordinal::Transfinite(terms_rhs)
                } else {
                    let mut index_lhs = terms_lhs.len() - 1;
                    while index_lhs > 0
                        && terms_lhs[index_lhs].exponent_ref() < &leading_exponent_rhs
                    {
                        index_lhs -= 1;
                    }

                    if terms_lhs[index_lhs].exponent_ref() == &leading_exponent_rhs {
                        let mut new_terms = terms_lhs[..index_lhs].to_vec();
                        new_terms.push(
                            CnfTerm::from_parts(
                                leading_exponent_rhs,
                                terms_lhs[index_lhs]
                                    .multiplicity()
                                    .saturating_add(leading_mult_rhs),
                            )
                            .expect("combined CNF term has positive multiplicity"),
                        );
                        new_terms.extend(terms_rhs.into_iter().skip(1));
                        Ordinal::transfinite_unchecked(new_terms)
                    } else {
                        let mut new_terms = terms_lhs[..index_lhs + 1].to_vec();
                        new_terms.extend(terms_rhs);
                        Ordinal::transfinite_unchecked(new_terms)
                    }
                }
            }
        }
    }
}

impl Add<&Ordinal> for Ordinal {
    type Output = Self;

    fn add(self, rhs: &Ordinal) -> Self::Output {
        self + rhs.clone()
    }
}

impl Add<Ordinal> for &Ordinal {
    type Output = Ordinal;

    fn add(self, rhs: Ordinal) -> Self::Output {
        self.clone() + rhs
    }
}

impl Add<&Ordinal> for &Ordinal {
    type Output = Ordinal;

    fn add(self, rhs: &Ordinal) -> Self::Output {
        self.clone() + rhs.clone()
    }
}

/// Ordinal multiplication is associative and left-distributive over addition,
/// but NOT commutative for transfinite ordinals.
/// For example, `2 * w = w` but `w * 2 = w + w`.
///
/// # Overflow Behavior
///
/// Finite ordinal multiplication uses saturating arithmetic. Multiplying two finite
/// ordinals that would exceed `u32::MAX` returns `u32::MAX` instead of panicking.
// Ordinal multiplication legitimately pattern-matches on zero in a way
// that looks "suspicious" to clippy but is mathematically correct:
// any ordinal multiplied by zero equals zero (absorbing element).
#[expect(clippy::suspicious_arithmetic_impl)]
impl Mul<Ordinal> for Ordinal {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            // Case 1: Any multiplication by zero is zero
            (Ordinal::Finite(0), _) | (_, Ordinal::Finite(0)) => Ordinal::zero(),

            // Case 2: Finite x Finite behaves like integer multiplication
            // Use saturating arithmetic to prevent overflow
            (Ordinal::Finite(m), Ordinal::Finite(n)) => Ordinal::new_finite(m.saturating_mul(n)),

            // Case 3: Finite × Transfinite - scale the trailing finite term
            (Ordinal::Finite(m), Ordinal::Transfinite(mut terms_rhs)) => {
                let last_term_rhs = terms_rhs
                    .pop()
                    .expect("transfinite ordinals always have at least one CNF term");
                if last_term_rhs.is_finite() {
                    terms_rhs.push(CnfTerm::new_finite(
                        last_term_rhs.multiplicity().saturating_mul(m),
                    ));
                } else {
                    terms_rhs.push(last_term_rhs);
                }
                Ordinal::transfinite_unchecked(terms_rhs)
            }

            // Case 4: Transfinite × Finite - scale the leading multiplicity
            (Ordinal::Transfinite(mut terms_lhs), Ordinal::Finite(n)) => {
                terms_lhs[0] = CnfTerm::new(
                    terms_lhs[0].exponent_ref(),
                    terms_lhs[0].multiplicity().saturating_mul(n),
                )
                .expect("scaled multiplicity is positive when n > 0");
                Ordinal::transfinite_unchecked(terms_lhs)
            }

            // Case 5: Transfinite × Transfinite - complex CNF multiplication
            (Ordinal::Transfinite(terms_lhs), Ordinal::Transfinite(terms_rhs)) => {
                let mut new_terms: Vec<CnfTerm> = Vec::new();

                let leading_exp_lhs = terms_lhs[0].exponent();
                let leading_mult_lhs = terms_lhs[0].multiplicity();
                let trailing_rhs = terms_rhs
                    .last()
                    .expect("transfinite ordinals always have at least one CNF term");
                let rhs_is_limit = trailing_rhs.is_limit();
                let trailing_mult_rhs = trailing_rhs.multiplicity();
                let rhs_len = terms_rhs.len();

                if rhs_is_limit {
                    new_terms.extend(terms_rhs.into_iter().map(|term| {
                        let (exp, mult) = term.into_parts();
                        CnfTerm::from_parts(&leading_exp_lhs + exp, mult)
                            .expect("exponent addition and positive multiplicity yield valid term")
                    }));
                } else {
                    new_terms.extend(terms_rhs.into_iter().take(rhs_len - 1).map(|term| {
                        let (exp, mult) = term.into_parts();
                        CnfTerm::from_parts(&leading_exp_lhs + exp, mult)
                            .expect("exponent addition and positive multiplicity yield valid term")
                    }));
                    new_terms.push(
                        CnfTerm::from_parts(
                            leading_exp_lhs,
                            leading_mult_lhs.saturating_mul(trailing_mult_rhs),
                        )
                        .expect("product of positive multiplicities is positive"),
                    );

                    new_terms.extend(terms_lhs.into_iter().skip(1));
                }

                Ordinal::transfinite_unchecked(new_terms)
            }
        }
    }
}

impl Mul<&Ordinal> for Ordinal {
    type Output = Self;

    fn mul(self, rhs: &Ordinal) -> Self::Output {
        self * rhs.clone()
    }
}

impl Mul<Ordinal> for &Ordinal {
    type Output = Ordinal;

    fn mul(self, rhs: Ordinal) -> Self::Output {
        self.clone() * rhs
    }
}

impl Mul<&Ordinal> for &Ordinal {
    type Output = Ordinal;

    fn mul(self, rhs: &Ordinal) -> Self::Output {
        self.clone() * rhs.clone()
    }
}

/// Ordinal exponentiation. Note that ordinal exponentiation is NOT associative:
/// `w^(1^w) = w` but `(w^1)^w = w^w`.
///
/// # Overflow Behavior
///
/// Finite ordinal exponentiation uses saturating arithmetic. Computing `m^n` for
/// finite ordinals that would exceed `u32::MAX` returns `u32::MAX` instead of panicking.
///
/// # Panics
///
/// Panics on finite base with a transfinite exponent whose leading term has a
/// transfinite exponent itself (e.g., `2^(ω^ω·3)`). This case is not yet implemented.
impl Pow<Ordinal> for Ordinal {
    type Output = Self;

    fn pow(self, rhs: Self) -> Self::Output {
        // Handle base cases first to enable ownership-based matching below
        if matches!(rhs, Ordinal::Finite(0)) || matches!(self, Ordinal::Finite(1)) {
            return Ordinal::one();
        }
        if matches!(rhs, Ordinal::Finite(1)) {
            return self;
        }
        if matches!(self, Ordinal::Finite(0)) {
            return Ordinal::zero();
        }

        // Now we can match on owned values since base cases are handled
        match (self, rhs) {
            (Ordinal::Finite(m), Ordinal::Finite(n)) => Ordinal::new_finite(m.saturating_pow(n)),

            (lhs @ Ordinal::Transfinite(_), rhs) => {
                if rhs.is_limit() {
                    let Ordinal::Transfinite(terms_lhs) = lhs else {
                        unreachable!()
                    };
                    let (leading_exp, _) = terms_lhs
                        .into_iter()
                        .next()
                        .expect("transfinite ordinal has a leading term")
                        .into_parts();
                    let new_exponent = leading_exp * rhs;
                    Ordinal::transfinite_unchecked(vec![
                        CnfTerm::from_parts(new_exponent, 1).expect("positive multiplicity")
                    ])
                } else if let Ordinal::Finite(n) = rhs {
                    // Binary exponentiation for finite exponents. Valid because
                    // ordinal multiplication is associative: (a * b) * c = a * (b * c)
                    //
                    // Note: We CANNOT use binary exp for transfinite exponents because
                    // ordinal exponentiation is NOT associative: w^(1^w) != (w^1)^w
                    binary_pow(lhs, n)
                } else {
                    // rhs is Transfinite successor - distribute over CNF terms
                    let Ordinal::Transfinite(terms_rhs) = rhs else {
                        unreachable!()
                    };
                    let mut distributed = Ordinal::one();
                    for term in terms_rhs {
                        if term.is_finite() {
                            distributed =
                                distributed * binary_pow(lhs.clone(), term.multiplicity());
                        } else {
                            distributed = distributed
                                * lhs.clone().pow(Ordinal::transfinite_unchecked(vec![term]));
                        }
                    }
                    distributed
                }
            }

            (Ordinal::Finite(m), Ordinal::Transfinite(terms_rhs)) => {
                // n^(sum of CNF terms) = product of n^(each term)
                let mut distributed = Ordinal::one();
                for term in terms_rhs {
                    if term.is_finite() {
                        distributed = distributed
                            * Ordinal::new_finite(m.saturating_pow(term.multiplicity()));
                    } else {
                        let (e, k) = term.into_parts();

                        if e == Ordinal::one() {
                            // n^(ω · k) = ω^k
                            distributed = distributed
                                * Ordinal::transfinite_unchecked(vec![CnfTerm::from_parts(
                                    Ordinal::new_finite(k),
                                    1,
                                )
                                .expect("positive multiplicity for omega power")]);
                        } else if let Ordinal::Finite(e_val) = e {
                            // n^(ω^e · k) = ω^(ω^(e-1) · k) for finite e > 1
                            let inner_exp =
                                Ordinal::transfinite_unchecked(vec![CnfTerm::from_parts(
                                    Ordinal::new_finite(e_val - 1),
                                    k,
                                )
                                .expect("positive multiplicity for inner exponent")]);
                            distributed = distributed
                                * Ordinal::transfinite_unchecked(vec![CnfTerm::from_parts(
                                    inner_exp, 1,
                                )
                                .expect("positive multiplicity for outer term")]);
                        } else {
                            todo!("finite base with transfinite tower exponent (e.g., 2^(ω^ω·3))")
                        }
                    }
                }
                distributed
            }
        }
    }
}

/// Binary exponentiation with O(log n) multiplications.
///
/// Exploits associativity of ordinal multiplication for finite exponents.
/// Cloning within the loop is inherent to the algorithm: we need the base
/// for both the accumulator multiplication and the squaring step.
fn binary_pow(base: Ordinal, exp: u32) -> Ordinal {
    if exp == 0 {
        return Ordinal::one();
    }
    if exp == 1 {
        return base;
    }

    let mut base = base;
    let mut exp = exp;
    let mut result = Ordinal::one();

    while exp > 1 {
        if exp % 2 == 1 {
            result = result * base.clone();
        }
        exp /= 2;
        base = base.clone() * base;
    }
    // Final iteration: consume base by move, avoiding one clone.
    result * base
}

impl Pow<&Ordinal> for Ordinal {
    type Output = Self;

    fn pow(self, rhs: &Ordinal) -> Self::Output {
        self.pow(rhs.clone())
    }
}

impl Pow<Ordinal> for &Ordinal {
    type Output = Ordinal;

    fn pow(self, rhs: Ordinal) -> Self::Output {
        self.clone().pow(rhs)
    }
}

impl Pow<&Ordinal> for &Ordinal {
    type Output = Ordinal;

    fn pow(self, rhs: &Ordinal) -> Self::Output {
        self.clone().pow(rhs.clone())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_ordinal_constructor() {
        let zero = Ordinal::zero();
        assert_eq!(zero, Ordinal::new_finite(0));

        let one = Ordinal::one();
        assert_eq!(one, Ordinal::new_finite(1));

        let omega = Ordinal::omega();
        assert_eq!(
            omega,
            Ordinal::new_transfinite(&[CnfTerm::new(&Ordinal::one(), 1).unwrap()]).unwrap()
        );
    }

    #[test]
    fn test_ordinal_is_limit() {
        let zero = Ordinal::zero();
        assert!(zero.is_limit());

        let one = Ordinal::one();
        assert!(!one.is_limit());

        let omega = Ordinal::omega();
        assert!(omega.is_limit());
    }

    #[test]
    fn test_ordinal_is_successor() {
        let zero = Ordinal::zero();
        assert!(!zero.is_successor());

        let one = Ordinal::one();
        assert!(one.is_successor());

        let omega = Ordinal::omega();
        assert!(!omega.is_successor());
    }

    #[test]
    fn test_ordinal_successor() {
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        let omega = Ordinal::omega();

        assert_eq!(zero.successor(), one);
        assert_eq!(one.successor(), Ordinal::new_finite(2));

        let omega_successor = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),
            CnfTerm::new_finite(1),
        ])
        .unwrap();
        assert_eq!(omega.successor(), omega_successor);
    }

    #[test]
    fn test_ordinal_is_finite() {
        let zero = Ordinal::zero();
        assert!(zero.is_finite());

        let one = Ordinal::one();
        assert!(one.is_finite());

        let omega = Ordinal::omega();
        assert!(!omega.is_finite());
    }

    #[test]
    fn test_ordinal_eq() {
        let zero = Ordinal::zero();
        let another_zero = Ordinal::new_finite(0);
        assert_eq!(zero, another_zero);

        let one = Ordinal::one();
        let another_one = Ordinal::new_finite(1);
        assert_eq!(one, another_one);

        let omega = Ordinal::omega();
        let another_omega = Ordinal::builder().omega().build_unchecked();
        assert_eq!(omega, another_omega);
    }

    #[test]
    fn test_ordinal_pow() {
        // Test finite ordinal powers
        let two = Ordinal::new_finite(2);
        let three = Ordinal::new_finite(3);
        assert_eq!(two.clone().pow(three.clone()), Ordinal::new_finite(8));
        assert_eq!(three.pow(two.clone()), Ordinal::new_finite(9));

        // Test edge cases
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        assert_eq!(zero.clone().pow(one.clone()), Ordinal::zero());
        assert_eq!(one.clone().pow(zero.clone()), Ordinal::one());
        assert_eq!(one.clone().pow(one), Ordinal::one());
        assert_eq!(two.clone().pow(zero), Ordinal::one());

        // Test transfinite ordinal powers
        let omega = Ordinal::omega();
        let omega_squared = Ordinal::builder().omega_power(2).build_unchecked();
        assert_eq!(omega.clone().pow(two.clone()), omega_squared);

        // Test omega^omega
        let omega_omega = Ordinal::builder()
            .omega_exp(omega.clone())
            .build_unchecked();
        assert_eq!(omega.clone().pow(omega.clone()), omega_omega);

        // Test finite * transfinite power
        assert_eq!(two.pow(omega.clone()), omega);
    }

    #[test]
    fn test_binary_exponentiation_small_powers() {
        // Test that binary exponentiation produces same results as naive multiplication
        let omega = Ordinal::omega();

        // ω^2 = ω^1 · ω = ω²
        let omega_squared = Ordinal::builder().omega_power(2).build_unchecked();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(2)), omega_squared);

        // ω^3 = ω²·ω = ω³
        let omega_cubed = Ordinal::builder().omega_power(3).build_unchecked();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(3)), omega_cubed);

        // ω^4 = ω^4
        let omega_fourth = Ordinal::builder().omega_power(4).build_unchecked();
        assert_eq!(omega.pow(Ordinal::new_finite(4)), omega_fourth);
    }

    #[test]
    fn test_binary_exponentiation_powers_of_two() {
        // Test powers of 2 (exercises binary path most efficiently)
        let omega = Ordinal::omega();

        // ω^8
        let omega_8 = Ordinal::builder().omega_power(8).build_unchecked();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(8)), omega_8);

        // ω^16
        let omega_16 = Ordinal::builder().omega_power(16).build_unchecked();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(16)), omega_16);

        // ω^32
        let omega_32 = Ordinal::builder().omega_power(32).build_unchecked();
        assert_eq!(omega.pow(Ordinal::new_finite(32)), omega_32);
    }

    #[test]
    fn test_binary_exponentiation_large_exponents() {
        // Test larger exponents to verify O(log n) performance benefit
        let omega = Ordinal::omega();

        // ω^100
        let omega_100 = Ordinal::builder().omega_power(100).build_unchecked();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(100)), omega_100);

        // ω^255 (exercises all bits in binary representation)
        let omega_255 = Ordinal::builder().omega_power(255).build_unchecked();
        assert_eq!(omega.pow(Ordinal::new_finite(255)), omega_255);
    }

    #[test]
    fn test_binary_exponentiation_complex_base() {
        // Test binary exponentiation with more complex ordinals
        // (ω² + ω + 1)^4
        let complex_base = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω²
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω
            CnfTerm::new_finite(1),
        ])
        .unwrap();

        // When we compute (ω² + ω + 1)^4, we get a complex result
        // The key is that the leading term of the result is ω^8
        let result = complex_base.pow(Ordinal::new_finite(4));
        let leading_term = result.leading_cnf_term().unwrap();

        // Verify the leading exponent is 8 (from 2 * 4)
        assert_eq!(leading_term.exponent(), Ordinal::new_finite(8));
        assert_eq!(leading_term.multiplicity(), 1);

        // Verify it's transfinite
        assert!(result.is_transfinite());
    }

    #[test]
    fn test_binary_exponentiation_edge_cases() {
        let omega = Ordinal::omega();

        // ω^0 = 1 (handled in base cases, but verify it works)
        assert_eq!(omega.clone().pow(Ordinal::zero()), Ordinal::one());

        // ω^1 = ω
        assert_eq!(omega.clone().pow(Ordinal::one()), omega);

        // Verify odd exponents work correctly
        // ω^5
        let omega_5 = Ordinal::builder().omega_power(5).build_unchecked();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(5)), omega_5);

        // ω^7
        let omega_7 = Ordinal::builder().omega_power(7).build_unchecked();
        assert_eq!(omega.pow(Ordinal::new_finite(7)), omega_7);
    }

    #[test]
    fn test_ordinal_add() {
        // Test finite ordinal addition
        let two = Ordinal::new_finite(2);
        let three = Ordinal::new_finite(3);
        assert_eq!(two.clone() + three.clone(), Ordinal::new_finite(5));
        assert_eq!(three + two.clone(), Ordinal::new_finite(5));

        // Test edge cases
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        assert_eq!(zero.clone() + one.clone(), Ordinal::one());
        assert_eq!(one.clone() + zero.clone(), Ordinal::one());
        assert_eq!(zero.clone() + zero, Ordinal::zero());

        // Test transfinite ordinal addition
        let omega = Ordinal::omega();
        let omega_plus_one = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),
            CnfTerm::new_finite(1),
        ])
        .unwrap();
        assert_eq!(omega.clone() + one, omega_plus_one);

        // Test omega + omega
        let two_omega = Ordinal::builder().omega_times(2).build_unchecked();
        assert_eq!(omega.clone() + omega.clone(), two_omega);

        // Test finite + transfinite
        let omega_plus_two = omega.successor().successor();
        assert_eq!(two.clone() + omega.clone(), omega);
        assert_eq!(omega + two, omega_plus_two);
    }

    #[test]
    fn test_ordinal_mul() {
        // Test finite ordinal multiplication
        let two = Ordinal::new_finite(2);
        let three = Ordinal::new_finite(3);
        assert_eq!(two.clone() * three.clone(), Ordinal::new_finite(6));
        assert_eq!(three * two.clone(), Ordinal::new_finite(6));

        // Test edge cases
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        assert_eq!(zero.clone() * one.clone(), Ordinal::zero());
        assert_eq!(one.clone() * zero, Ordinal::zero());
        assert_eq!(one.clone() * one.clone(), Ordinal::one());
        assert_eq!(two.clone() * one.clone(), Ordinal::new_finite(2));
        assert_eq!(one * two.clone(), Ordinal::new_finite(2));

        // Test transfinite ordinal multiplication
        let omega = Ordinal::omega();
        let omega_times_two = Ordinal::builder().omega_times(2).build_unchecked();
        assert_eq!(omega.clone() * two.clone(), omega_times_two);

        // Test omega * omega
        let omega_squared = Ordinal::builder().omega_power(2).build_unchecked();
        assert_eq!(omega.clone() * omega.clone(), omega_squared);

        // Test finite * transfinite
        let two_omega = Ordinal::builder().omega_times(2).build_unchecked();
        assert_eq!(two.clone() * omega.clone(), omega);
        assert_eq!(omega * two, two_omega);
    }

    #[test]
    fn test_cnf_ordering_valid() {
        // Test valid strictly decreasing CNF terms
        // ω^2 + ω + 1 (exponents: 2 > 1 > 0)
        let ordinal = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω^1
            CnfTerm::new_finite(1),
        ]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_invalid_equal_exponents() {
        // Test invalid CNF with equal exponents
        // ω + ω should be rejected (should be ω*2 instead)
        let ordinal = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::one(), 1).unwrap(), // ω^1
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),
        ]);
        assert!(ordinal.is_err());
        assert!(matches!(
            ordinal.unwrap_err(),
            OrdinalError::TransfiniteConstructionError
        ));
    }

    #[test]
    fn test_cnf_ordering_invalid_increasing() {
        // Test invalid CNF with increasing exponents
        // ω + ω^2 should be rejected (wrong order)
        let ordinal = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::one(), 1).unwrap(), // ω^1
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
        ]);
        assert!(ordinal.is_err());
        assert!(matches!(
            ordinal.unwrap_err(),
            OrdinalError::TransfiniteConstructionError
        ));
    }

    #[test]
    fn test_cnf_ordering_complex_valid() {
        // Test complex valid CNF: ω^ω + ω^2 + ω + 5
        let omega = Ordinal::omega();
        let ordinal = Ordinal::new_transfinite(&[
            CnfTerm::new(&omega, 1).unwrap(),                  // ω^ω
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω^1
            CnfTerm::new_finite(5),
        ]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_two_terms_valid() {
        // Test valid two-term CNF: ω^2 + ω
        let ordinal = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),
        ]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_two_terms_invalid() {
        // Test invalid two-term CNF: ω + ω^2 (wrong order)
        let ordinal = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::one(), 1).unwrap(), // ω^1
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
        ]);
        assert!(ordinal.is_err());
    }

    #[test]
    fn test_cnf_ordering_single_term_valid() {
        // Test single term is always valid (no ordering to check)
        let ordinal = Ordinal::new_transfinite(&[CnfTerm::new(&Ordinal::one(), 1).unwrap()]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_finite_leading_invalid() {
        // Test that finite leading term is rejected
        let ordinal = Ordinal::new_transfinite(&[CnfTerm::new_finite(42)]);
        assert!(ordinal.is_err());
        assert!(matches!(
            ordinal.unwrap_err(),
            OrdinalError::TransfiniteConstructionError
        ));
    }

    #[test]
    fn test_is_zero() {
        assert!(Ordinal::zero().is_zero());
        assert!(!Ordinal::one().is_zero());
        assert!(!Ordinal::new_finite(42).is_zero());
        assert!(!Ordinal::omega().is_zero());
    }

    #[test]
    fn test_is_one() {
        assert!(Ordinal::one().is_one());
        assert!(!Ordinal::zero().is_one());
        assert!(!Ordinal::new_finite(42).is_one());
        assert!(!Ordinal::omega().is_one());
    }

    #[test]
    fn test_zero_one_are_const() {
        const Z: Ordinal = Ordinal::zero();
        const O: Ordinal = Ordinal::one();
        assert_eq!(Z, Ordinal::new_finite(0));
        assert_eq!(O, Ordinal::new_finite(1));
    }

    #[test]
    fn test_num_traits_zero_one() {
        use num_traits::{One, Zero};
        assert_eq!(<Ordinal as Zero>::zero(), Ordinal::zero());
        assert!(<Ordinal as Zero>::zero().is_zero());
        assert!(!<Ordinal as Zero>::is_zero(&Ordinal::one()));

        assert_eq!(<Ordinal as One>::one(), Ordinal::one());
        assert!(<Ordinal as One>::is_one(&Ordinal::one()));
        assert!(!<Ordinal as One>::is_one(&Ordinal::zero()));
    }

    #[test]
    fn test_leading_cnf_term_ref() {
        let omega = Ordinal::omega();
        let leading = omega
            .leading_cnf_term_ref()
            .expect("omega has a leading term");
        assert_eq!(leading.multiplicity(), 1);

        // Returned reference matches the cloning variant.
        assert_eq!(
            omega.leading_cnf_term_ref().cloned(),
            omega.leading_cnf_term()
        );

        // Finite ordinals have no terms.
        assert!(Ordinal::new_finite(5).leading_cnf_term_ref().is_none());
    }

    #[test]
    fn test_trailing_cnf_term_ref() {
        let ordinal = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
            CnfTerm::new_finite(7),
        ])
        .unwrap();
        let trailing = ordinal.trailing_cnf_term_ref().expect("has trailing term");
        assert_eq!(trailing.multiplicity(), 7);

        // Returned reference matches the cloning variant.
        assert_eq!(
            ordinal.trailing_cnf_term_ref().cloned(),
            ordinal.trailing_cnf_term()
        );

        // Finite ordinals have no terms.
        assert!(Ordinal::new_finite(5).trailing_cnf_term_ref().is_none());
    }

    #[test]
    fn test_cnf_terms_iter() {
        let omega = Ordinal::omega();
        assert_eq!(omega.cnf_terms_iter().count(), 1);

        // Finite ordinals iterate over zero terms.
        assert_eq!(Ordinal::new_finite(5).cnf_terms_iter().count(), 0);
        assert_eq!(Ordinal::zero().cnf_terms_iter().count(), 0);

        // Iterator order matches cnf_terms vector order.
        let three_term = Ordinal::builder()
            .omega_power(2)
            .omega_times(3)
            .plus(7)
            .build()
            .unwrap();
        let from_iter: Vec<CnfTerm> = three_term.cnf_terms_iter().cloned().collect();
        assert_eq!(Some(from_iter), three_term.cnf_terms());
    }
}
