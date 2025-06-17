use num_traits::Pow;
use ordinal::{CnfTerm, Ordinal};

fn main() {
    let base = Ordinal::new_transfinite(&vec![
        CnfTerm::new(&Ordinal::new_finite(3), 1).unwrap(),
        CnfTerm::new(&Ordinal::new_finite(1), 1).unwrap(),
    ])
    .unwrap();
    let expr = base.pow(Ordinal::new_finite(5));
    let expected = Ordinal::new_transfinite(&vec![
        CnfTerm::new(&Ordinal::new_finite(15), 1).unwrap(),
        CnfTerm::new(&Ordinal::new_finite(13), 1).unwrap(),
    ])
    .unwrap();

    println!("Got:      {}", expr);
    println!("Expected: {}", expected);
}
