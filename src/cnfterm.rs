use crate::error::{OrdinalError, Result};
use crate::ordinal::Ordinal;
use std::cmp::{Ord, PartialOrd};

#[derive(Debug, Clone)]
pub struct CnfTerm {
    exponent: Ordinal,
    multiplicity: u64,
}

impl CnfTerm {
    pub fn new(exponent: &Ordinal, multiplicity: u64) -> Result<Self> {
        if multiplicity == 0 {
            return Err(OrdinalError::CnfTermConstructionError);
        }

        Ok(CnfTerm {
            exponent: exponent.clone(),
            multiplicity,
        })
    }

    pub fn new_finite(n: u64) -> Self {
        CnfTerm::new(&Ordinal::Finite(0), n).unwrap()
    }

    pub fn exponent(&self) -> Ordinal {
        self.exponent.clone()
    }

    pub fn multiplicity(&self) -> u64 {
        self.multiplicity
    }

    pub fn is_limit(&self) -> bool {
        true
    }

    pub fn is_successor(&self) -> bool {
        !self.is_limit()
    }

    pub fn successor(&self) -> Self {
        CnfTerm::new(&self.exponent, self.multiplicity).unwrap()
    }

    pub fn is_finite(&self) -> bool {
        matches!(self.exponent, Ordinal::Finite(0))
    }
}

impl std::fmt::Display for CnfTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let exponent = self.exponent();
        let multiplicity = self.multiplicity();

        if matches!(exponent, Ordinal::Finite(0)) {
            return write!(f, "{}", multiplicity);
        }

        let mut result = String::new();
        result.push('ω');

        if !matches!(exponent, Ordinal::Finite(1)) {
            result.push_str(&format!("^{}", self.exponent()));
        }

        if multiplicity != 1 {
            result.push_str(&format!(" * {}", self.multiplicity()));
        }

        write!(f, "{}", result)
    }
}

impl PartialOrd for CnfTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CnfTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.exponent()
            .cmp(&other.exponent())
            .then_with(|| self.multiplicity().cmp(&other.multiplicity()))
    }
}

impl PartialEq for CnfTerm {
    fn eq(&self, other: &Self) -> bool {
        self.multiplicity() == other.multiplicity() && self.exponent() == other.exponent()
    }
}

impl Eq for CnfTerm {}

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
    fn test_cnf_term_successor() {
        let one = Ordinal::one();
        let cnf_term = CnfTerm::new(&one, 1).unwrap();
        let successor = cnf_term.successor();
        assert_eq!(successor, cnf_term);
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
}
