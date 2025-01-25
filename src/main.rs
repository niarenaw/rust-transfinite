use ordinal::Ordinal;

fn main() {
    for n in 1..=10 {
        let x = Ordinal::Transfinite {
            exponent: Box::new(Ordinal::Finite(n)),
            multiplier: n * 2,
            addend: Box::new(Ordinal::Finite(n + 1)),
        };
        println!("{x}");
    }
}
