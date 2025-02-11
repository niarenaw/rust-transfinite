use ordinal::Ordinal;

fn main() {
    let zero = Ordinal::zero();
    let one = Ordinal::one();
    let omega = Ordinal::omega();

    let om1 = (one.clone() + one.clone()) * (omega + one.clone()) * (one.clone() + one.clone());
    println!("{}", om1);
}
