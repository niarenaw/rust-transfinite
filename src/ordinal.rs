#[derive(Debug, Clone)]
pub struct Finite(u64);

#[derive(Debug, Clone)]
pub struct CnfTerm {
    pub exponent: Box<Ordinal>,
    pub multiplier: Finite,
    pub addend: Box<Ordinal>,
}

#[derive(Debug, Clone)]
pub enum Ordinal {
    Finite(Finite),
    Transfinite(Vec<CnfTerm>),
}

type Result<T> = std::result::Result<T, OrdinalError>;

pub trait OrdinalTrait: Sized {
    fn is_limit(&self) -> bool;
    fn is_successor(&self) -> bool;
    fn successor(&self) -> Self;
}

impl OrdinalTrait for Finite {
    fn is_limit(&self) -> bool {
        self.0 == 0
    }

    fn is_successor(&self) -> bool {
        self.0 > 0
    }

    fn successor(&self) -> Self {
        Finite::new(self.0 + 1)
    }
}

impl OrdinalTrait for Transfinite {
    fn is_limit(&self) -> bool {
        self.addend.is_limit()
    }

    fn is_successor(&self) -> bool {
        !self.is_limit()
    }

    fn successor(&self) -> Self {
        Transfinite::new(&self.exponent, self.multiplier, *self.addend.successor())
    }
}
