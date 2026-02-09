//! Fluent builder API for constructing ordinals in Cantor Normal Form.

use crate::{CnfTerm, Ordinal, OrdinalError, Result};

/// A fluent builder for constructing ordinals in Cantor Normal Form.
///
/// Provides a chainable API for building ordinals term-by-term, with validation
/// ensuring terms are added in strictly decreasing exponent order (as required
/// by CNF).
///
/// # Examples
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
///
/// assert!(ordinal.is_transfinite());
/// ```
#[derive(Debug, Clone)]
pub struct OrdinalBuilder {
    terms: Vec<CnfTerm>,
    last_exponent: Option<Ordinal>,
    error: Option<OrdinalError>,
}

impl Default for OrdinalBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl OrdinalBuilder {
    /// Creates a new empty builder.
    pub fn new() -> Self {
        OrdinalBuilder {
            terms: Vec::new(),
            last_exponent: None,
            error: None,
        }
    }

    /// Adds a CNF term with the given exponent and multiplicity.
    ///
    /// Terms must be added in strictly decreasing exponent order.
    /// If a term violates ordering or has zero multiplicity, an error is stored.
    pub fn term(mut self, exponent: Ordinal, multiplicity: u32) -> Self {
        if self.error.is_some() {
            return self;
        }

        if multiplicity == 0 {
            self.error = Some(OrdinalError::CnfTermConstructionError);
            return self;
        }

        if let Some(ref last) = self.last_exponent {
            if exponent >= *last {
                self.error = Some(OrdinalError::TransfiniteConstructionError);
                return self;
            }
        }

        let term = if exponent == Ordinal::zero() {
            CnfTerm::new_finite(multiplicity)
        } else {
            match CnfTerm::new(&exponent, multiplicity) {
                Ok(t) => t,
                Err(e) => {
                    self.error = Some(e);
                    return self;
                }
            }
        };

        self.last_exponent = Some(exponent);
        self.terms.push(term);
        self
    }

    /// Adds ω (omega) as a term with multiplicity 1.
    ///
    /// Equivalent to `.term(Ordinal::one(), 1)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega = Ordinal::builder().omega().build().unwrap();
    /// assert_eq!(omega, Ordinal::omega());
    /// ```
    pub fn omega(self) -> Self {
        self.term(Ordinal::one(), 1)
    }

    /// Adds ω · n (omega times n) as a term.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega_times_3 = Ordinal::builder().omega_times(3).build().unwrap();
    /// assert!(omega_times_3.is_transfinite());
    /// ```
    pub fn omega_times(self, multiplicity: u32) -> Self {
        self.term(Ordinal::one(), multiplicity)
    }

    /// Adds ω^n (omega to a finite power) as a term with multiplicity 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega_cubed = Ordinal::builder().omega_power(3).build().unwrap();
    /// assert!(omega_cubed.is_transfinite());
    /// ```
    pub fn omega_power(self, exponent: u32) -> Self {
        self.term(Ordinal::new_finite(exponent), 1)
    }

    /// Adds ω^n · m (omega to a finite power with multiplicity).
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// // ω² · 5
    /// let ordinal = Ordinal::builder().omega_power_times(2, 5).build().unwrap();
    /// assert!(ordinal.is_transfinite());
    /// ```
    pub fn omega_power_times(self, exponent: u32, multiplicity: u32) -> Self {
        self.term(Ordinal::new_finite(exponent), multiplicity)
    }

    /// Adds ω^exp as a term, where `exp` is a transfinite ordinal.
    ///
    /// Use this for ordinals like ω^ω or ω^(ω²).
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega = Ordinal::omega();
    /// let omega_to_omega = Ordinal::builder().omega_exp(omega).build().unwrap();
    /// assert!(omega_to_omega.is_transfinite());
    /// ```
    pub fn omega_exp(self, exponent: Ordinal) -> Self {
        self.term(exponent, 1)
    }

    /// Adds ω^exp · mult, where `exp` is a transfinite ordinal.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega = Ordinal::omega();
    /// let ordinal = Ordinal::builder().omega_exp_times(omega, 3).build().unwrap();
    /// assert!(ordinal.is_transfinite());
    /// ```
    pub fn omega_exp_times(self, exponent: Ordinal, multiplicity: u32) -> Self {
        self.term(exponent, multiplicity)
    }

    /// Adds a finite constant term (+n) to the ordinal.
    ///
    /// This is typically the last term in a CNF expression.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let seven = Ordinal::builder().plus(7).build().unwrap();
    /// assert_eq!(seven, Ordinal::new_finite(7));
    /// ```
    pub fn plus(self, n: u32) -> Self {
        self.term(Ordinal::zero(), n)
    }

    /// Builds the ordinal from accumulated terms.
    ///
    /// Returns `Ok(Ordinal::zero())` if no terms were added.
    ///
    /// # Errors
    ///
    /// Returns [`OrdinalError`] if:
    /// - A term was added with zero multiplicity
    /// - Terms were not added in strictly decreasing exponent order
    /// - The resulting CNF is otherwise invalid
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let ordinal = Ordinal::builder()
    ///     .omega_power(2)
    ///     .omega_times(3)
    ///     .plus(7)
    ///     .build()
    ///     .unwrap();
    ///
    /// assert!(ordinal.is_transfinite());
    /// ```
    pub fn build(self) -> Result<Ordinal> {
        if let Some(e) = self.error {
            return Err(e);
        }

        if self.terms.is_empty() {
            return Ok(Ordinal::zero());
        }

        if self.terms.len() == 1 && self.terms[0].is_finite() {
            return Ok(Ordinal::new_finite(self.terms[0].multiplicity()));
        }

        Ordinal::new_transfinite(&self.terms)
    }

    /// Builds the ordinal, panicking on any error.
    ///
    /// # Panics
    ///
    /// Panics if the accumulated terms form an invalid CNF expression.
    /// Prefer [`build`](Self::build) for fallible construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use transfinite::Ordinal;
    ///
    /// let omega = Ordinal::builder().omega().build_unchecked();
    /// assert_eq!(omega, Ordinal::omega());
    /// ```
    pub fn build_unchecked(self) -> Ordinal {
        self.build().expect("OrdinalBuilder: invalid construction")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_builder_returns_zero() {
        assert_eq!(OrdinalBuilder::new().build().unwrap(), Ordinal::zero());
    }

    #[test]
    fn test_single_omega() {
        assert_eq!(
            OrdinalBuilder::new().omega().build().unwrap(),
            Ordinal::omega()
        );
    }

    #[test]
    fn test_omega_squared() {
        let result = OrdinalBuilder::new().omega_power(2).build().unwrap();
        assert!(result.is_transfinite());
    }

    #[test]
    fn test_finite_only() {
        assert_eq!(
            OrdinalBuilder::new().plus(42).build().unwrap(),
            Ordinal::new_finite(42)
        );
    }

    #[test]
    fn test_compound_ordinal() {
        let result = OrdinalBuilder::new()
            .omega_power(2)
            .omega_times(3)
            .plus(7)
            .build()
            .unwrap();

        let expected = Ordinal::new_transfinite(&[
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
            CnfTerm::new(&Ordinal::one(), 3).unwrap(),
            CnfTerm::new_finite(7),
        ])
        .unwrap();

        assert_eq!(result, expected);
    }

    #[test]
    fn test_rejects_wrong_order() {
        assert!(OrdinalBuilder::new()
            .omega()
            .omega_power(2)
            .build()
            .is_err());
    }

    #[test]
    fn test_rejects_zero_multiplicity() {
        assert!(OrdinalBuilder::new().omega_times(0).build().is_err());
    }

    #[test]
    #[should_panic]
    fn test_build_unchecked_panics() {
        OrdinalBuilder::new()
            .omega()
            .omega_power(2)
            .build_unchecked();
    }
}
