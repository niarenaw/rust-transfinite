// TODO: add examples from
// https://theory.stanford.edu/~tingz/talks/

#[cfg(test)]
mod tests {

    use num_traits::Pow;
    use ordinal::*;

    #[test]
    fn multiplication() {
        let one = Ordinal::one();
        let two = &one + &one;
        let three = &one + &two;
        let five = &two + &three;

        let omega = Ordinal::omega();
        let omega_2 = Ordinal::new_transfinite(&vec![CnfTerm::new(&two, 1).unwrap()]).unwrap();
        let omega_3 = Ordinal::new_transfinite(&vec![CnfTerm::new(&three, 1).unwrap()]).unwrap();

        let lhs = &omega_2 + &omega + one;
        let rhs = omega_3.clone() + omega;

        let expr = lhs * rhs;
        let expected_terms = vec![
            CnfTerm::new(&five, 1).unwrap(),
            CnfTerm::new(&three, 1).unwrap(),
        ];
        let expected = Ordinal::new_transfinite(&expected_terms).unwrap();

        assert_eq!(expr, expected)
    }

    #[test]
    fn exponentiation() {
        let base = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(5), 1).unwrap(),
            CnfTerm::new(&Ordinal::new_finite(3), 1).unwrap(),
        ])
        .unwrap();
        let expr = base.pow(Ordinal::new_finite(3));
        let expected = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(15), 1).unwrap(),
            CnfTerm::new(&Ordinal::new_finite(13), 1).unwrap(),
        ])
        .unwrap();

        assert_eq!(expr, expected)
    }
}
