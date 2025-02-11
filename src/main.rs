use ordinal::Ordinal;

fn main() {
    let zero = Ordinal::zero();
    let one = Ordinal::one();
    let omega = Ordinal::omega();

    let om1 = &one + omega.clone() + one.clone() + zero + one.clone() + omega;
    println!("{}", om1);
}
