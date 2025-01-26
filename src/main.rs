use ordinal::Ordinal;

fn main() {
    let zero = Ordinal::zero();
    let omega = Ordinal::Transfinite {
        exponent: Box::new(Ordinal::one()),
        multiplier: Box::new(Ordinal::one()),
        addend: Box::new(Ordinal::zero()),
    };

    let a = zero * &omega;
    let b = Ordinal::new_finite(2) * &omega;
    let c = (&omega * Ordinal::Finite(2)) * &b;

    println!("{a} < {b} < {c}");
}
