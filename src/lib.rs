use thiserror::Error;

#[derive(Debug, Clone)]
pub struct CnfTerm {
    exponent: Ordinal,
    multiplicity: u64,
}

#[derive(Debug, Clone)]
pub enum Ordinal {
    Finite(u64),
    Transfinite(Vec<CnfTerm>),
}

#[derive(Debug, Error)]
pub enum OrdinalError {
    #[error("CNF terms must have a non-zero multiplicity.")]
    CnfTermConstructionError,
    #[error("Terms in a CNF decomposition must be non-decreasing and the leading term must be transfinite.")]
    TransfiniteConstructionError,
}

type Result<T> = std::result::Result<T, OrdinalError>;

pub trait OrdinalTrait: Sized {
    fn is_limit(&self) -> bool;
    fn is_successor(&self) -> bool;
    fn successor(&self) -> Self;
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

    pub fn exponent(&self) -> Ordinal {
        self.exponent.clone()
    }

    pub fn multiplicity(&self) -> u64 {
        self.multiplicity
    }

    pub fn is_finite(&self) -> bool {
        matches!(self.exponent, Ordinal::Finite(0))
    }
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
}

impl OrdinalTrait for CnfTerm {
    fn is_limit(&self) -> bool {
        true
    }

    fn is_successor(&self) -> bool {
        !self.is_limit()
    }

    fn successor(&self) -> Self {
        CnfTerm::new(&self.exponent, self.multiplicity).unwrap()
    }
}

impl OrdinalTrait for Ordinal {
    fn is_limit(&self) -> bool {
        match self {
            Ordinal::Finite(0) => true,
            Ordinal::Finite(_) => false,
            Ordinal::Transfinite(terms) => terms.last().unwrap().is_limit(),
        }
    }

    fn is_successor(&self) -> bool {
        !self.is_limit()
    }

    fn successor(&self) -> Self {
        match self {
            Ordinal::Finite(n) => Ordinal::new_finite(n + 1),
            Ordinal::Transfinite(terms) => {
                let mut new_terms = terms.clone();
                let last_term = new_terms.pop().unwrap();
                let new_last_term = last_term.successor();
                new_terms.push(new_last_term);
                Ordinal::Transfinite(new_terms)
            }
        }
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

impl std::fmt::Display for Ordinal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ordinal::Finite(n) => write!(f, "{}", n),
            Ordinal::Transfinite(terms) => {
                // let mut result = String::new();
                // join the display of each cnf term to +
                let result = terms
                    .into_iter()
                    .map(|term| term.to_string())
                    .collect::<Vec<String>>()
                    .join(" + ");

                write!(f, "{}", result)
            }
        }
    }
}
