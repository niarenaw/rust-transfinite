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
}
