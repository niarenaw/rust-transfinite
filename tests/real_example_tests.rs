#[cfg(test)]
mod tests {

    use num_traits::Pow;
    use transfinite::Ordinal;

    #[test]
    fn multiplication() {
        // Using builder for transfinite ordinals
        let omega = Ordinal::omega();
        let omega_2 = Ordinal::builder().omega_power(2).build().unwrap();
        let omega_3 = Ordinal::builder().omega_power(3).build().unwrap();

        // (ω² + ω + 1) * (ω³ + ω)
        let lhs = &omega_2 + &omega + Ordinal::one();
        let rhs = omega_3.clone() + omega;

        let expr = lhs * rhs;

        // Expected: ω⁵ + ω³
        let expected = Ordinal::builder()
            .omega_power(5)
            .omega_power(3)
            .build()
            .unwrap();

        assert_eq!(expr, expected);
    }

    #[test]
    fn exponentiation() {
        // (ω⁵ + ω³)³ using builder
        let base = Ordinal::builder()
            .omega_power(5)
            .omega_power(3)
            .build()
            .unwrap();

        let expr = base.pow(Ordinal::from(3));

        // Expected: ω¹⁵ + ω¹³
        let expected = Ordinal::builder()
            .omega_power(15)
            .omega_power(13)
            .build()
            .unwrap();

        assert_eq!(expr, expected);
    }
}
