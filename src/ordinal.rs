use num_traits::Pow;
use std::cmp::{Ord, PartialOrd};
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
/// - CNF terms must be in strictly decreasing order by exponent (currently not fully validated - see TODO)
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
#[derive(Debug, Clone)]
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
    pub fn new_transfinite(terms: &[CnfTerm]) -> Result<Self> {
        // Validate terms vector is non-empty
        match terms.first() {
            None => return Err(OrdinalError::TransfiniteConstructionError),
            Some(term) => {
                // Validate leading term is transfinite (has non-zero exponent)
                if term.is_finite() {
                    return Err(OrdinalError::TransfiniteConstructionError);
                }
            }
        }

        // Validate terms are in strictly decreasing order by exponent
        // In CNF: β₁ > β₂ > ... > βₙ (strictly decreasing)
        for i in 0..terms.len() - 1 {
            let current_exponent = terms[i].exponent();
            let next_exponent = terms[i + 1].exponent();

            // Terms must be in strictly decreasing order
            if current_exponent <= next_exponent {
                return Err(OrdinalError::TransfiniteConstructionError);
            }
        }

        Ok(Ordinal::Transfinite(terms.to_vec()))
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
            Ordinal::Transfinite(terms) => terms.last().unwrap().is_limit(),
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
                        new_terms.push(CnfTerm::new_finite(last_term.multiplicity().saturating_add(1)));
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
    pub fn zero() -> Self {
        Ordinal::new_finite(0)
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
    pub fn one() -> Self {
        Ordinal::new_finite(1)
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
        let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
        Ordinal::new_transfinite(&[omega_term]).unwrap()
    }
}

impl std::fmt::Display for Ordinal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ordinal::Finite(n) => write!(f, "{}", n),
            Ordinal::Transfinite(terms) => {
                let result = terms
                    .iter()
                    .map(|term| term.to_string())
                    .collect::<Vec<String>>()
                    .join(" + ");

                write!(f, "{}", result)
            }
        }
    }
}

impl PartialEq for Ordinal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ordinal::Finite(_), Ordinal::Transfinite(_)) => false,
            (Ordinal::Transfinite(_), Ordinal::Finite(_)) => false,
            (Ordinal::Finite(m), Ordinal::Finite(n)) => n == m,
            (Ordinal::Transfinite(xs), Ordinal::Transfinite(ys)) => xs == ys,
        }
    }
}

impl Eq for Ordinal {}

impl From<u32> for Ordinal {
    fn from(n: u32) -> Self {
        Ordinal::new_finite(n)
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
            (Ordinal::Transfinite(terms_lhs), Ordinal::Transfinite(mut terms_rhs)) => {
                let leading_exponent_lhs = terms_lhs[0].exponent();
                let leading_exponent_rhs = terms_rhs[0].exponent();
                let leading_mult_rhs = terms_rhs[0].multiplicity();

                if leading_exponent_lhs < leading_exponent_rhs {
                    // rhs dominates, return it (move rhs)
                    Ordinal::Transfinite(terms_rhs)
                } else {
                    let mut index_lhs = terms_lhs.len() - 1;
                    while index_lhs > 0 && terms_lhs[index_lhs].exponent() < leading_exponent_rhs {
                        index_lhs -= 1;
                    }

                    if terms_lhs[index_lhs].exponent() == leading_exponent_rhs {
                        // Exponents match - combine multiplicities
                        // Use saturating_add to prevent overflow
                        let mut new_terms = terms_lhs[..index_lhs].to_vec();
                        new_terms.push(
                            CnfTerm::new(
                                &leading_exponent_rhs,
                                terms_lhs[index_lhs].multiplicity().saturating_add(leading_mult_rhs),
                            )
                            .unwrap(),
                        );
                        // Move remaining terms from rhs
                        new_terms.extend_from_slice(&terms_rhs[1..]);
                        Ordinal::new_transfinite(&new_terms).unwrap()
                    } else {
                        // No matching exponent - concatenate
                        let mut new_terms = terms_lhs[..index_lhs + 1].to_vec();
                        // Move all terms from rhs
                        new_terms.append(&mut terms_rhs);
                        Ordinal::new_transfinite(&new_terms).unwrap()
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

impl Mul<Ordinal> for Ordinal {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            // Case 1: Any multiplication by zero is zero
            (Ordinal::Finite(0), _) | (_, Ordinal::Finite(0)) => Ordinal::zero(),

            // Case 2: Finite × Finite behaves like integer multiplication
            // Use saturating arithmetic to prevent overflow
            (Ordinal::Finite(m), Ordinal::Finite(n)) => Ordinal::new_finite(m.saturating_mul(n)),

            // Case 3: Finite × Transfinite - move terms_rhs instead of cloning
            (Ordinal::Finite(m), Ordinal::Transfinite(mut terms_rhs)) => {
                let last_term_rhs = terms_rhs.pop().unwrap();
                if last_term_rhs.is_finite() {
                    // Use saturating_mul to prevent overflow
                    terms_rhs.push(CnfTerm::new_finite(last_term_rhs.multiplicity().saturating_mul(m)));
                } else {
                    terms_rhs.push(last_term_rhs);
                }
                Ordinal::new_transfinite(&terms_rhs).unwrap()
            }

            // Case 4: Transfinite × Finite - move and modify terms_lhs in place
            (Ordinal::Transfinite(mut terms_lhs), Ordinal::Finite(n)) => {
                // Use saturating_mul to prevent overflow
                terms_lhs[0] =
                    CnfTerm::new(&terms_lhs[0].exponent(), terms_lhs[0].multiplicity().saturating_mul(n))
                        .unwrap();
                Ordinal::new_transfinite(&terms_lhs).unwrap()
            }

            // Case 5: Transfinite × Transfinite - complex CNF multiplication
            (ref lhs @ Ordinal::Transfinite(ref terms_lhs), ref rhs @ Ordinal::Transfinite(ref terms_rhs)) => {
                let mut new_terms: Vec<CnfTerm> = Vec::new();
                let leading_term_lhs_exponent = lhs.leading_cnf_term().unwrap().exponent();

                if rhs.is_limit() {
                    new_terms.extend(terms_rhs.iter().map(|term| {
                        CnfTerm::new(
                            &(&leading_term_lhs_exponent + term.exponent()),
                            term.multiplicity(),
                        )
                        .unwrap()
                    }));
                } else {
                    new_terms.extend(terms_rhs.iter().take(terms_rhs.len() - 1).map(|term| {
                        CnfTerm::new(
                            &(&leading_term_lhs_exponent + term.exponent()),
                            term.multiplicity(),
                        )
                        .unwrap()
                    }));
                    let leading_term_lhs_mult = lhs.leading_cnf_term().unwrap().multiplicity();
                    let trailing_term_rhs_mult = rhs.trailing_cnf_term().unwrap().multiplicity();
                    new_terms.push(
                        CnfTerm::new(
                            &leading_term_lhs_exponent,
                            leading_term_lhs_mult.saturating_mul(trailing_term_rhs_mult),
                        )
                        .unwrap(),
                    );

                    // Append non-leading terms from lhs (e.g., the "+3" in (w+3) * (w+5) = w^2 + w*5 + 3)
                    new_terms.extend(terms_lhs.iter().skip(1).cloned());
                }

                Ordinal::new_transfinite(&new_terms).unwrap()
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

impl Pow<Ordinal> for Ordinal {
    type Output = Self;

    fn pow(self, rhs: Self) -> Self::Output {
        match (&self, &rhs) {
            (_, Ordinal::Finite(0)) | (Ordinal::Finite(1), _) => Ordinal::one(),
            (_, Ordinal::Finite(1)) => self,
            (Ordinal::Finite(0), _) => Ordinal::zero(),
            (Ordinal::Finite(m), Ordinal::Finite(n)) => {
                // Use saturating_pow to prevent overflow
                Ordinal::new_finite(m.saturating_pow(*n))
            }

            (Ordinal::Transfinite(_), _) => {
                if rhs.is_limit() {
                    let leading_term_lhs = self.leading_cnf_term().unwrap();
                    let leading_exponent_lhs = leading_term_lhs.exponent();
                    let new_exponent = leading_exponent_lhs * rhs;
                    Ordinal::new_transfinite(&[CnfTerm::new(&new_exponent, 1).unwrap()])
                        .unwrap()
                } else if let Ordinal::Finite(n) = rhs {
                    // Binary exponentiation is VALID for finite exponents because
                    // ordinal multiplication is associative: (α · β) · γ = α · (β · γ)
                    // This allows us to compute α^(2n) = (α^2)^n safely.
                    //
                    // Note: We CANNOT use binary exponentiation for transfinite exponents
                    // because ordinal exponentiation is NOT associative:
                    // ω^(1^ω) = ω but (ω^1)^ω = ω^ω, and ω ≠ ω^ω
                    //
                    // Performance: O(log n) multiplications instead of O(n)
                    if n == 0 {
                        return Ordinal::one();
                    }

                    let mut base = self.clone();
                    let mut exp = n;
                    let mut result = Ordinal::one();

                    while exp > 0 {
                        if exp % 2 == 1 {
                            result = result * base.clone();
                        }
                        if exp > 1 {
                            base = base.clone() * base.clone();
                        }
                        exp /= 2;
                    }
                    result
                } else {
                    // rhs must be Transfinite and a successor at this point
                    let mut distributed = Ordinal::one();
                    if let Ordinal::Transfinite(terms_rhs) = &rhs {
                        for term in terms_rhs.iter() {
                            if term.is_finite() {
                                // Finite term: use binary exponentiation for the finite part
                                let finite_exp = term.multiplicity();
                                let mut base = self.clone();
                                let mut exp = finite_exp;
                                let mut result = Ordinal::one();
                                while exp > 0 {
                                    if exp % 2 == 1 {
                                        result = result * base.clone();
                                    }
                                    if exp > 1 {
                                        base = base.clone() * base.clone();
                                    }
                                    exp /= 2;
                                }
                                distributed = distributed * result;
                            } else {
                                distributed = distributed
                                    * self
                                        .clone()
                                        .pow(Ordinal::new_transfinite(&[term.clone()]).unwrap());
                            }
                        }
                    }
                    distributed
                }
            }

            (Ordinal::Finite(m), Ordinal::Transfinite(terms_rhs)) => {
                // n^(sum of CNF terms) = product of n^(each term)
                // For each term w^e * k:
                //   - If e = 0 (finite term): n^k
                //   - If e = 1: n^(w*k) = w^k
                //   - If e > 1: n^(w^e * k) = w^(w^(e-1) * k)
                let mut distributed = Ordinal::one();
                for term in terms_rhs {
                    if term.is_finite() {
                        // Finite term: n^k
                        distributed =
                            distributed * Ordinal::new_finite(m.saturating_pow(term.multiplicity()));
                    } else {
                        let e = term.exponent();
                        let k = term.multiplicity();

                        if e == Ordinal::one() {
                            // n^(w * k) = w^k
                            distributed = distributed
                                * Ordinal::new_transfinite(&[CnfTerm::new(
                                    &Ordinal::new_finite(k),
                                    1,
                                )
                                .unwrap()])
                                .unwrap();
                        } else if let Ordinal::Finite(e_val) = &e {
                            // n^(w^e * k) = w^(w^(e-1) * k) for finite e > 1
                            let inner_exp = Ordinal::new_transfinite(&[CnfTerm::new(
                                &Ordinal::new_finite(e_val - 1),
                                k,
                            )
                            .unwrap()])
                            .unwrap();
                            distributed = distributed
                                * Ordinal::new_transfinite(&[CnfTerm::new(&inner_exp, 1).unwrap()])
                                .unwrap();
                        } else {
                            // Transfinite exponent tower - not yet implemented
                            unimplemented!(
                                "Finite base with transfinite tower exponent not yet supported"
                            )
                        }
                    }
                }
                distributed
            }
        }
    }
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
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 1).unwrap()]).unwrap()
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

        let omega_successor = Ordinal::new_transfinite(&vec![
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
        let another_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 1).unwrap()]).unwrap();
        assert_eq!(omega, another_omega);
    }

    #[test]
    fn test_ordinal_pow() {
        // Test finite ordinal powers
        let two = Ordinal::new_finite(2);
        let three = Ordinal::new_finite(3);
        assert_eq!(two.clone().pow(three.clone()), Ordinal::new_finite(8));
        assert_eq!(three.clone().pow(two.clone()), Ordinal::new_finite(9));

        // Test edge cases
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        assert_eq!(zero.clone().pow(one.clone()), Ordinal::zero());
        assert_eq!(one.clone().pow(zero.clone()), Ordinal::one());
        assert_eq!(one.clone().pow(one.clone()), Ordinal::one());
        assert_eq!(two.clone().pow(zero.clone()), Ordinal::one());

        // Test transfinite ordinal powers
        let omega = Ordinal::omega();
        let omega_squared =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(two.clone()), omega_squared);

        // Test omega^omega
        let omega_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&omega.clone(), 1).unwrap()]).unwrap();
        assert_eq!(omega.clone().pow(omega.clone()), omega_omega);

        // Test finite * transfinite power
        assert_eq!(two.clone().pow(omega.clone()), omega);
    }

    #[test]
    fn test_binary_exponentiation_small_powers() {
        // Test that binary exponentiation produces same results as naive multiplication
        let omega = Ordinal::omega();

        // ω^2 = ω^1 · ω = ω²
        let omega_squared =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(2)), omega_squared);

        // ω^3 = ω²·ω = ω³
        let omega_cubed =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(3), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(3)), omega_cubed);

        // ω^4 = ω^4
        let omega_fourth =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(4), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(4)), omega_fourth);
    }

    #[test]
    fn test_binary_exponentiation_powers_of_two() {
        // Test powers of 2 (exercises binary path most efficiently)
        let omega = Ordinal::omega();

        // ω^8
        let omega_8 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(8), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(8)), omega_8);

        // ω^16
        let omega_16 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(16), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(16)), omega_16);

        // ω^32
        let omega_32 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(32), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(32)), omega_32);
    }

    #[test]
    fn test_binary_exponentiation_large_exponents() {
        // Test larger exponents to verify O(log n) performance benefit
        let omega = Ordinal::omega();

        // ω^100
        let omega_100 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(100), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(100)), omega_100);

        // ω^255 (exercises all bits in binary representation)
        let omega_255 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(255), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(255)), omega_255);
    }

    #[test]
    fn test_binary_exponentiation_complex_base() {
        // Test binary exponentiation with more complex ordinals
        // (ω² + ω + 1)^4
        let complex_base = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω²
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω
            CnfTerm::new_finite(1),                            // 1
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
        let omega_5 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(5), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(5)), omega_5);

        // ω^7
        let omega_7 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(7), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(7)), omega_7);
    }

    #[test]
    fn test_ordinal_add() {
        // Test finite ordinal addition
        let two = Ordinal::new_finite(2);
        let three = Ordinal::new_finite(3);
        assert_eq!(two.clone() + three.clone(), Ordinal::new_finite(5));
        assert_eq!(three.clone() + two.clone(), Ordinal::new_finite(5));

        // Test edge cases
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        assert_eq!(zero.clone() + one.clone(), Ordinal::one());
        assert_eq!(one.clone() + zero.clone(), Ordinal::one());
        assert_eq!(zero.clone() + zero.clone(), Ordinal::zero());

        // Test transfinite ordinal addition
        let omega = Ordinal::omega();
        let omega_plus_one = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),
            CnfTerm::new_finite(1),
        ])
        .unwrap();
        assert_eq!(omega.clone() + one.clone(), omega_plus_one);

        // Test omega + omega
        let two_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 2).unwrap()]).unwrap();
        assert_eq!(omega.clone() + omega.clone(), two_omega);

        // Test finite + transfinite
        let omega_plus_two = omega.successor().successor();
        assert_eq!(two.clone() + omega.clone(), omega);
        assert_eq!(omega.clone() + two.clone(), omega_plus_two);
    }

    #[test]
    fn test_ordinal_mul() {
        // Test finite ordinal multiplication
        let two = Ordinal::new_finite(2);
        let three = Ordinal::new_finite(3);
        assert_eq!(two.clone() * three.clone(), Ordinal::new_finite(6));
        assert_eq!(three.clone() * two.clone(), Ordinal::new_finite(6));

        // Test edge cases
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        assert_eq!(zero.clone() * one.clone(), Ordinal::zero());
        assert_eq!(one.clone() * zero.clone(), Ordinal::zero());
        assert_eq!(one.clone() * one.clone(), Ordinal::one());
        assert_eq!(two.clone() * one.clone(), Ordinal::new_finite(2));
        assert_eq!(one.clone() * two.clone(), Ordinal::new_finite(2));

        // Test transfinite ordinal multiplication
        let omega = Ordinal::omega();
        let omega_times_two =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 2).unwrap()]).unwrap();
        assert_eq!(omega.clone() * two.clone(), omega_times_two);

        // Test omega * omega
        let omega_squared =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone() * omega.clone(), omega_squared);

        // Test finite * transfinite
        let two_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 2).unwrap()]).unwrap();
        assert_eq!(two.clone() * omega.clone(), omega);
        assert_eq!(omega.clone() * two.clone(), two_omega);
    }

    #[test]
    fn test_cnf_ordering_valid() {
        // Test valid strictly decreasing CNF terms
        // ω^2 + ω + 1 (exponents: 2 > 1 > 0)
        let ordinal = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω^1
            CnfTerm::new_finite(1),                            // ω^0 = 1
        ]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_invalid_equal_exponents() {
        // Test invalid CNF with equal exponents
        // ω + ω should be rejected (should be ω*2 instead)
        let ordinal = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::one(), 1).unwrap(), // ω^1
            CnfTerm::new(&Ordinal::one(), 1).unwrap(), // ω^1 again - INVALID
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
        let ordinal = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω^1
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2 - INVALID (increasing)
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
        let ordinal = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&omega, 1).unwrap(),                  // ω^ω
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω^1
            CnfTerm::new_finite(5),                            // ω^0 = 5
        ]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_two_terms_valid() {
        // Test valid two-term CNF: ω^2 + ω
        let ordinal = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω^1
        ]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_two_terms_invalid() {
        // Test invalid two-term CNF: ω + ω^2 (wrong order)
        let ordinal = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),         // ω^1
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω^2 - INVALID
        ]);
        assert!(ordinal.is_err());
    }

    #[test]
    fn test_cnf_ordering_single_term_valid() {
        // Test single term is always valid (no ordering to check)
        let ordinal = Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 1).unwrap()]);
        assert!(ordinal.is_ok());
    }

    #[test]
    fn test_cnf_ordering_finite_leading_invalid() {
        // Test that finite leading term is rejected
        let ordinal = Ordinal::new_transfinite(&vec![CnfTerm::new_finite(42)]);
        assert!(ordinal.is_err());
        assert!(matches!(
            ordinal.unwrap_err(),
            OrdinalError::TransfiniteConstructionError
        ));
    }
}
