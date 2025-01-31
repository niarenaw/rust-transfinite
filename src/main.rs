use ordinal::Ordinal;

fn main() {
    let zero = Ordinal::zero();
    let one = Ordinal::one();
    let omega = Ordinal::omega();

    let s = zero == one;
    let t = omega == omega;

    println!("{zero} == {one}: {s}");
    println!("{omega} == {one}: {t}");
}
