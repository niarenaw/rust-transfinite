use ordinal::Ordinal;

fn main() {
    let zero = Ordinal::zero();
    let one = Ordinal::one();
    let omega = Ordinal::omega();

    println!("{zero} < {one}");
    println!("{omega} < {one}");
}
