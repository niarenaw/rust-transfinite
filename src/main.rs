use ordinal::Ordinal;

fn main() {
    let zero = Ordinal::new_finite(0);
    let omega = Ordinal::Transfinite {
        exponent: Box::new(Ordinal::Finite(1)),
        multiplier: 1,
        addend: Box::new(Ordinal::Finite(0)),
    };
    println!("{zero} < {}", omega.successor() + omega);
}
