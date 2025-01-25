use thiserror::Error;

#[derive(Debug, Clone)]
pub enum Ordinal {
    // TODO: Finite(T) should take any type T st T: Non-Negative Int
    Finite(u32),
    Transfinite {
        exponent: Box<Ordinal>,
        multiplier: u32,
        addend: Box<Ordinal>,
    },
}

#[derive(Debug, Error)]
pub enum OrdinalError {
    #[error("Transfinite ordinals must have a non-zero exponent and a multiplier greater than 0.")]
    InvalidTransfiniteOrdinal,
}

type Result<T> = std::result::Result<T, OrdinalError>;

impl Ordinal {
    pub fn new_transfinite(
        exponent: Box<Ordinal>,
        multiplier: u32,
        addend: Box<Ordinal>,
    ) -> Result<Self> {
        if multiplier == 0 || matches!(*exponent, Ordinal::Finite(0)) {
            Err(OrdinalError::InvalidTransfiniteOrdinal)
        } else {
            Ok(Ordinal::Transfinite {
                exponent,
                multiplier,
                addend,
            })
        }
    }

    pub fn is_finite(&self) -> bool {
        matches!(self, Ordinal::Finite(_))
    }

    pub fn is_transfinite(&self) -> bool {
        matches!(self, Ordinal::Transfinite { .. })
    }

    pub fn successor(&self) -> Self {
        match self {
            Ordinal::Finite(value) => Ordinal::Finite(value + 1),
            Ordinal::Transfinite {
                exponent,
                multiplier,
                addend,
            } => Ordinal::Transfinite {
                exponent: exponent.clone(),
                multiplier: *multiplier,
                addend: Box::new(addend.successor()),
            },
        }
    }

    pub fn is_limit(&self) -> bool {
        match self {
            Ordinal::Finite(_) => false,
            Ordinal::Transfinite { addend, .. } => matches!(**addend, Ordinal::Finite(0)),
        }
    }
}

impl std::fmt::Display for Ordinal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ordinal::Finite(n) => write!(f, "{}", n),
            Ordinal::Transfinite {
                exponent,
                multiplier,
                addend,
            } => write!(f, "ω^{} * {} + {}", exponent, multiplier, addend),
        }
    }
}

impl PartialEq for Ordinal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ordinal::Finite(a), Ordinal::Finite(b)) => a == b,
            (
                Ordinal::Transfinite {
                    exponent: e1,
                    multiplier: m1,
                    addend: a1,
                },
                Ordinal::Transfinite {
                    exponent: e2,
                    multiplier: m2,
                    addend: a2,
                },
            ) => e1 == e2 && m1 == m2 && a1 == a2,
            _ => false,
        }
    }
}

impl Eq for Ordinal {}

impl PartialOrd for Ordinal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Ordinal::Finite(a), Ordinal::Finite(b)) => a.partial_cmp(b),
            (Ordinal::Finite(_), Ordinal::Transfinite { .. }) => Some(std::cmp::Ordering::Less),
            (Ordinal::Transfinite { .. }, Ordinal::Finite(_)) => Some(std::cmp::Ordering::Greater),
            (
                Ordinal::Transfinite {
                    exponent: e1,
                    multiplier: m1,
                    addend: a1,
                },
                Ordinal::Transfinite {
                    exponent: e2,
                    multiplier: m2,
                    addend: a2,
                },
            ) => e1
                .partial_cmp(e2)
                .or_else(|| m1.partial_cmp(m2))
                .or_else(|| a1.partial_cmp(a2)),
        }
    }
}

impl Ord for Ordinal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_transfinite_valid() {
        let transfinite = Ordinal::new_transfinite(
            Box::new(Ordinal::Finite(1)),
            2,
            Box::new(Ordinal::Finite(0)),
        );
        assert!(transfinite.is_ok());
    }

    #[test]
    fn test_new_transfinite_invalid_exponent() {
        let transfinite = Ordinal::new_transfinite(
            Box::new(Ordinal::Finite(0)),
            2,
            Box::new(Ordinal::Finite(0)),
        );
        assert!(transfinite.is_err());
    }

    #[test]
    fn test_new_transfinite_invalid_multiplier() {
        let transfinite = Ordinal::new_transfinite(
            Box::new(Ordinal::Finite(1)),
            0,
            Box::new(Ordinal::Finite(0)),
        );
        assert!(transfinite.is_err());
    }

    #[test]
    fn test_is_finite() {
        assert!(Ordinal::Finite(42).is_finite());
        assert!(!Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(0)),
            multiplier: 1,
            addend: Box::new(Ordinal::Finite(0)),
        }
        .is_finite());
    }

    #[test]
    fn test_is_transfinite() {
        assert!(Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(0)),
            multiplier: 1,
            addend: Box::new(Ordinal::Finite(0)),
        }
        .is_transfinite());
        assert!(!Ordinal::Finite(42).is_transfinite());
    }

    #[test]
    fn test_is_limit() {
        assert!(!Ordinal::Finite(42).is_limit());

        let limit = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(1)),
            multiplier: 1,
            addend: Box::new(Ordinal::Finite(0)),
        };

        assert!(limit.is_limit());

        let non_limit = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(1)),
            multiplier: 1,
            addend: Box::new(Ordinal::Finite(1)),
        };

        assert!(!non_limit.is_limit());
    }

    #[test]
    fn test_successor() {
        assert_eq!(Ordinal::Finite(1).successor(), Ordinal::Finite(2));

        let transfinite = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(0)),
            multiplier: 2,
            addend: Box::new(Ordinal::Finite(0)),
        };

        let expected_successor = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(0)),
            multiplier: 2,
            addend: Box::new(Ordinal::Finite(1)),
        };

        assert_eq!(transfinite.successor(), expected_successor);
    }

    #[test]
    fn test_partial_eq() {
        assert_eq!(Ordinal::Finite(1), Ordinal::Finite(1));
        assert_ne!(Ordinal::Finite(1), Ordinal::Finite(2));

        let ord1 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(1)),
            multiplier: 2,
            addend: Box::new(Ordinal::Finite(0)),
        };
        let ord2 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(1)),
            multiplier: 2,
            addend: Box::new(Ordinal::Finite(0)),
        };

        assert_eq!(ord1, ord2);
    }

    #[test]
    fn test_partial_ord() {
        assert!(Ordinal::Finite(1) < Ordinal::Finite(2));
        assert!(
            Ordinal::Finite(2)
                < Ordinal::Transfinite {
                    exponent: Box::new(Ordinal::Finite(0)),
                    multiplier: 1,
                    addend: Box::new(Ordinal::Finite(0)),
                }
        );

        let ord1 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(1)),
            multiplier: 1,
            addend: Box::new(Ordinal::Finite(0)),
        };
        let ord2 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(2)),
            multiplier: 1,
            addend: Box::new(Ordinal::Finite(0)),
        };

        assert!(ord1 < ord2);
    }

    #[test]
    fn test_display() {
        assert_eq!(Ordinal::Finite(42).to_string(), "42");

        let transfinite = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(1)),
            multiplier: 3,
            addend: Box::new(Ordinal::Finite(2)),
        };

        assert_eq!(transfinite.to_string(), "ω^1 * 3 + 2");
    }
}
