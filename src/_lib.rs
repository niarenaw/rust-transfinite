use std::ops::{Add, Mul};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum OrdinalError {
    #[error("Transfinite ordinals must have a non-zero exponent and multiplier.")]
    TransfiniteOrdinalConstructionError,
}

// TODO: tweak visibility to force construction via constructor methods
#[derive(Debug, Clone)]
pub enum Ordinal {
    // TODO: Finite(T) should take any type T st T: Non-Negative Int
    Finite(u64),
    Transfinite {
        exponent: Box<Ordinal>,
        multiplier: Box<Ordinal>,
        addend: Box<Ordinal>,
    },
}

type Result<T> = std::result::Result<T, OrdinalError>;

impl Ordinal {
    pub fn new_finite(n: u64) -> Ordinal {
        Ordinal::Finite(n)
    }

    pub fn new_transfinite(
        exponent: &Ordinal,
        multiplier: &Ordinal,
        addend: &Ordinal,
    ) -> Result<Self> {
        if matches!(*exponent, Ordinal::Finite(0)) || matches!(*multiplier, Ordinal::Finite(0)) {
            return Err(OrdinalError::TransfiniteOrdinalConstructionError);
        }

        let leading_cnf_term = Ordinal::Transfinite {
            exponent: Box::new(exponent.clone()),
            multiplier: Box::new(multiplier.clone()),
            addend: Box::new(Self::zero()),
        };

        // validate that the addend is not larger than the first term to ensure CNF is realized
        if leading_cnf_term < *addend {
            Err(OrdinalError::TransfiniteOrdinalConstructionError)
        } else {
            Ok(leading_cnf_term + addend)
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
                multiplier: multiplier.clone(),
                addend: Box::new(addend.successor()),
            },
        }
    }

    pub fn is_limit(&self) -> bool {
        match self {
            Ordinal::Finite(0) => true,
            Ordinal::Finite(_) => false,
            Ordinal::Transfinite { addend, .. } => addend.is_limit(),
        }
    }

    pub fn zero() -> Self {
        Ordinal::Finite(0)
    }

    pub fn one() -> Self {
        Ordinal::Finite(1)
    }

    pub fn omega() -> Self {
        Ordinal::Transfinite {
            exponent: Box::new(Self::one()),
            multiplier: Box::new(Self::one()),
            addend: Box::new(Self::zero()),
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
            } => {
                let mut result = String::new();

                // Append ω (omega) with optional exponent
                result.push('ω');
                if **exponent != Self::one() {
                    result.push_str(&format!("^{}", exponent));
                }

                // Append multiplier if it's not 1
                if **multiplier != Self::one() {
                    result.push_str(&format!(" * {}", multiplier));
                }

                // Append addend if it's not 0
                if **addend != Self::zero() {
                    result.push_str(&format!(" + {}", addend));
                }

                write!(f, "{}", result)
            }
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
        Some(self.cmp(other))
    }
}

impl Ord for Ordinal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Ordinal::Finite(a), Ordinal::Finite(b)) => a.cmp(b),
            (Ordinal::Finite(_), Ordinal::Transfinite { .. }) => std::cmp::Ordering::Less,
            (Ordinal::Transfinite { .. }, Ordinal::Finite(_)) => std::cmp::Ordering::Greater,
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
            ) => e1.cmp(e2).then_with(|| m1.cmp(m2)).then_with(|| a1.cmp(a2)),
        }
    }
}

impl Add<Ordinal> for Ordinal {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs.clone()) {
            // Case 1: Finite + Finite behaves like regular addition
            (Ordinal::Finite(a), Ordinal::Finite(b)) => Ordinal::Finite(a + b),

            // Case 2: Finite + Transfinite returns the Transfinite ordinal
            (Ordinal::Finite(_), Ordinal::Transfinite { .. }) => rhs.clone(),

            // Case 3: Transfinite + Finite applies successor to the addend
            (
                Ordinal::Transfinite {
                    exponent,
                    multiplier,
                    addend,
                },
                Ordinal::Finite(n),
            ) => {
                let mut new_addend = *addend;
                for _ in 0..n {
                    new_addend = new_addend.successor();
                }
                Ordinal::Transfinite {
                    exponent,
                    multiplier,
                    addend: Box::new(new_addend),
                }
            }

            // Case 4: Transfinite + Transfinite - CNF cases
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
            ) => {
                if e1 > e2 {
                    Ordinal::Transfinite {
                        exponent: e1,
                        multiplier: m1,
                        addend: Box::new(a1.add(rhs)),
                    }
                } else if e1 < e2 {
                    rhs.clone()
                } else {
                    Ordinal::Transfinite {
                        exponent: e1,
                        multiplier: Box::new(*m1 + *m2),
                        addend: a2,
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

impl Mul for Ordinal {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self.clone(), rhs.clone()) {
            (Ordinal::Finite(0), _) | (_, Ordinal::Finite(0)) => Ordinal::zero(),
            (Ordinal::Finite(a), Ordinal::Finite(b)) => Ordinal::new_finite(a * b),
            (
                Ordinal::Finite(_),
                Ordinal::Transfinite {
                    exponent,
                    multiplier,
                    addend,
                },
            ) => Ordinal::Transfinite {
                exponent,
                multiplier,
                addend: Box::new(self * *addend),
            },
            (
                Ordinal::Transfinite {
                    exponent,
                    multiplier,
                    addend,
                },
                Ordinal::Finite(_),
            ) => Ordinal::Transfinite {
                exponent,
                multiplier: Box::new(*multiplier * rhs),
                addend,
            },
            (
                Ordinal::Transfinite {
                    exponent: e1,
                    multiplier: _,
                    addend: a1,
                },
                Ordinal::Transfinite {
                    exponent: e2,
                    multiplier: m2,
                    addend: a2,
                },
            ) => Ordinal::Transfinite {
                exponent: Box::new(*e1 + *e2),
                multiplier: m2,
                addend: Box::new(*a1 + *a2.clone() + self + *a2),
            },
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_transfinite_valid() {
        let transfinite =
            Ordinal::new_transfinite(&Ordinal::one(), &Ordinal::Finite(2), &Ordinal::zero());
        assert!(transfinite.is_ok());
    }

    #[test]
    fn test_new_transfinite_invalid_exponent() {
        let transfinite =
            Ordinal::new_transfinite(&Ordinal::zero(), &Ordinal::Finite(2), &Ordinal::zero());
        assert!(transfinite.is_err());
    }

    #[test]
    fn test_new_transfinite_invalid_multiplier() {
        let transfinite =
            Ordinal::new_transfinite(&Ordinal::one(), &Ordinal::zero(), &Ordinal::zero());
        assert!(transfinite.is_err());
    }

    #[test]
    fn test_is_finite() {
        assert!(Ordinal::new_finite(42).is_finite());
        assert!(!Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::one()),
            addend: Box::new(Ordinal::zero()),
        }
        .is_finite());
    }

    #[test]
    fn test_is_transfinite() {
        assert!(Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::one()),
            addend: Box::new(Ordinal::zero()),
        }
        .is_transfinite());
        assert!(!Ordinal::Finite(42).is_transfinite());
    }

    #[test]
    fn test_is_limit() {
        assert!(!Ordinal::Finite(42).is_limit());

        let limit = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::one()),
            addend: Box::new(Ordinal::zero()),
        };

        assert!(limit.is_limit());

        let non_limit = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::one()),
            addend: Box::new(Ordinal::one()),
        };

        assert!(!non_limit.is_limit());
    }

    #[test]
    fn test_successor() {
        assert_eq!(Ordinal::one().successor(), Ordinal::Finite(2));

        let transfinite = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::zero()),
        };

        let expected_successor = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::one()),
        };

        assert_eq!(transfinite.successor(), expected_successor);
    }

    #[test]
    fn test_partial_eq() {
        assert_eq!(Ordinal::one(), Ordinal::one());
        assert_ne!(Ordinal::one(), Ordinal::Finite(2));

        let ord1 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::zero()),
        };
        let ord2 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::zero()),
        };

        assert_eq!(ord1, ord2);
    }

    #[test]
    fn test_partial_ord() {
        assert!(Ordinal::one() < Ordinal::Finite(2));
        assert!(
            Ordinal::Finite(2)
                < Ordinal::Transfinite {
                    exponent: Box::new(Ordinal::zero()),
                    multiplier: Box::new(Ordinal::one()),
                    addend: Box::new(Ordinal::zero()),
                }
        );

        let ord1 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::one()),
            addend: Box::new(Ordinal::zero()),
        };
        let ord2 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(2)),
            multiplier: Box::new(Ordinal::one()),
            addend: Box::new(Ordinal::zero()),
        };

        assert!(ord1 < ord2);
    }

    #[test]
    fn test_display() {
        assert_eq!(Ordinal::Finite(42).to_string(), "42");

        let transfinite =
            Ordinal::new_transfinite(&Ordinal::one(), &Ordinal::Finite(3), &Ordinal::Finite(5))
                .unwrap();

        assert_eq!(transfinite.to_string(), "ω * 3 + 5");

        let transfinite_no_addend =
            Ordinal::new_transfinite(&Ordinal::Finite(2), &Ordinal::one(), &Ordinal::zero())
                .unwrap();

        assert_eq!(transfinite_no_addend.to_string(), "ω^2");

        let transfinite_simple =
            Ordinal::new_transfinite(&Ordinal::one(), &Ordinal::one(), &Ordinal::zero()).unwrap();

        assert_eq!(transfinite_simple.to_string(), "ω");
    }

    #[test]
    fn test_add_finite() {
        assert_eq!(Ordinal::Finite(2) + Ordinal::Finite(3), Ordinal::Finite(5));
        assert_eq!(&Ordinal::Finite(3) + Ordinal::Finite(4), Ordinal::Finite(7));
        assert_eq!(
            Ordinal::Finite(21) + &Ordinal::Finite(12),
            Ordinal::Finite(33)
        );
        assert_eq!(
            &Ordinal::Finite(2) + &Ordinal::Finite(1),
            Ordinal::Finite(3)
        );
    }

    #[test]
    fn test_add_finite_to_transfinite() {
        let transfinite = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::zero()),
        };

        assert_eq!(Ordinal::Finite(42) + transfinite.clone(), transfinite);
    }

    #[test]
    fn test_add_transfinite_to_finite() {
        let transfinite = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::zero()),
        };

        let expected = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::Finite(42)),
        };

        assert_eq!(transfinite + Ordinal::Finite(42), expected);
    }

    #[test]
    fn test_add_transfinite_to_transfinite() {
        let transfinite1 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::one()),
            multiplier: Box::new(Ordinal::new_finite(2)),
            addend: Box::new(Ordinal::zero()),
        };

        let transfinite2 = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(2)),
            multiplier: Box::new(Ordinal::Finite(3)),
            addend: Box::new(Ordinal::one()),
        };

        let result = transfinite1 + transfinite2;

        // This is just a placeholder for now
        assert!(matches!(result, Ordinal::Transfinite { .. }));
    }
}
