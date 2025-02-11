use std::cmp::{Ord, PartialOrd};
use std::ops::Add;

use crate::cnfterm::CnfTerm;
use crate::error::{OrdinalError, Result};

#[derive(Debug, Clone)]
pub enum Ordinal {
    Finite(u64),
    Transfinite(Vec<CnfTerm>),
}

impl Ordinal {
    pub fn new_finite(n: u64) -> Self {
        Ordinal::Finite(n)
    }

    pub fn new_transfinite(terms: &Vec<CnfTerm>) -> Result<Self> {
        // TODO: validate sorted order
        match terms.first() {
            None => Err(OrdinalError::TransfiniteConstructionError),
            Some(term) => {
                if term.is_finite() {
                    return Err(OrdinalError::TransfiniteConstructionError);
                }

                Ok(Ordinal::Transfinite(terms.clone()))
            }
        }
    }

    pub fn is_limit(&self) -> bool {
        match self {
            Ordinal::Finite(0) => true,
            Ordinal::Finite(_) => false,
            Ordinal::Transfinite(terms) => terms.last().unwrap().is_limit(),
        }
    }

    pub fn is_successor(&self) -> bool {
        !self.is_limit()
    }
    pub fn successor(&self) -> Self {
        match self {
            Ordinal::Finite(n) => Ordinal::new_finite(n + 1),
            Ordinal::Transfinite(terms) => {
                let mut new_terms = terms.clone();
                if let Some(last_term) = new_terms.pop() {
                    if last_term.is_finite() {
                        new_terms.push(CnfTerm::new_finite(last_term.multiplicity() + 1));
                    } else {
                        new_terms.push(last_term);
                        new_terms.push(CnfTerm::new_finite(1));
                    }
                }
                Ordinal::Transfinite(new_terms)
            }
        }
    }

    pub fn is_finite(&self) -> bool {
        matches!(self, Ordinal::Finite(_))
    }

    pub fn is_transfinite(&self) -> bool {
        matches!(self, Ordinal::Transfinite(_))
    }

    pub fn leading_cnf_term(&self) -> Option<CnfTerm> {
        match self.cnf_terms() {
            Some(terms) => terms.first().cloned(),
            None => None,
        }
    }

    pub fn trailing_cnf_term(&self) -> Option<CnfTerm> {
        match self.cnf_terms() {
            Some(terms) => terms.last().cloned(),
            None => None,
        }
    }

    pub fn cnf_terms(&self) -> Option<Vec<CnfTerm>> {
        match self {
            Ordinal::Finite(_) => None,
            Ordinal::Transfinite(terms) => Some(terms.clone()),
        }
    }

    pub fn zero() -> Self {
        Ordinal::new_finite(0)
    }

    pub fn one() -> Self {
        Ordinal::new_finite(1)
    }

    pub fn omega() -> Self {
        let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
        Ordinal::new_transfinite(&vec![omega_term]).unwrap()
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
        match (&self, &rhs) {
            // Case 1: Finite + Finite behaves like integer addition
            (Ordinal::Finite(m), Ordinal::Finite(n)) => Ordinal::new_finite(m + n),

            // Case 2: Finite + Transfinite returns the Transfinite ordinal
            (Ordinal::Finite(_), Ordinal::Transfinite(_)) => rhs,

            // Case 3: Transfinite + Finite adds finite to the trailing cnf term
            (Ordinal::Transfinite(terms), Ordinal::Finite(n)) => {
                let mut new_terms = terms.clone();
                if let Some(last_term) = new_terms.pop() {
                    if last_term.is_finite() {
                        let new_last_term = CnfTerm::new_finite(last_term.multiplicity() + n);
                        new_terms.push(new_last_term);
                    } else {
                        new_terms.push(last_term);
                        new_terms.push(CnfTerm::new_finite(*n));
                    }
                }
                Ordinal::new_transfinite(&new_terms).unwrap()
            }

            // Case 4: Transfinite + Transfinite - CNF cases
            (Ordinal::Transfinite(terms_lhs), Ordinal::Transfinite(terms_rhs)) => {
                let leading_exponent_lhs = self.leading_cnf_term().unwrap().exponent();

                let leading_term_rhs = rhs.leading_cnf_term().unwrap();
                let leading_exponent_rhs = leading_term_rhs.exponent();

                if leading_exponent_lhs < leading_exponent_rhs {
                    rhs
                } else {
                    let mut index_lhs = terms_lhs.len() - 1;
                    while index_lhs > 0 && terms_lhs[index_lhs].exponent() < leading_exponent_rhs {
                        index_lhs -= 1;
                    }

                    if terms_lhs[index_lhs].exponent() == leading_exponent_rhs {
                        let mut new_terms = terms_lhs[..index_lhs].to_vec();
                        new_terms.push(
                            CnfTerm::new(
                                &leading_exponent_rhs,
                                terms_lhs[index_lhs].multiplicity()
                                    + leading_term_rhs.multiplicity(),
                            )
                            .unwrap(),
                        );
                        new_terms.extend(terms_rhs[1..].to_vec());
                        Ordinal::new_transfinite(&new_terms).unwrap()
                    } else {
                        let mut new_terms = terms_lhs[..index_lhs + 1].to_vec();
                        new_terms.extend(terms_rhs.clone());
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
}
