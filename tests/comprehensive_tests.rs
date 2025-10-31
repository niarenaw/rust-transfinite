// Comprehensive test suite for ordinal arithmetic
// Tests edge cases, properties, and mathematical invariants

use num_traits::Pow;
use ordinal::*;

#[cfg(test)]
mod ordinal_properties {
    use super::*;

    // ========================================
    // CONSTRUCTION TESTS
    // ========================================

    #[test]
    fn test_finite_construction() {
        for n in 0..100 {
            let ord = Ordinal::new_finite(n);
            assert!(ord.is_finite());
            assert!(!ord.is_transfinite());
        }
    }

    #[test]
    fn test_omega_construction() {
        let omega = Ordinal::omega();
        assert!(omega.is_transfinite());
        assert!(!omega.is_finite());
        assert!(omega.is_limit());
        assert!(!omega.is_successor());
    }

    #[test]
    fn test_cnf_term_zero_multiplicity_fails() {
        let result = CnfTerm::new(&Ordinal::one(), 0);
        assert!(result.is_err());
    }

    #[test]
    fn test_transfinite_empty_terms_fails() {
        let result = Ordinal::new_transfinite(&vec![]);
        assert!(result.is_err());
    }

    #[test]
    fn test_transfinite_finite_leading_term_fails() {
        let finite_term = CnfTerm::new_finite(42);
        let result = Ordinal::new_transfinite(&vec![finite_term]);
        assert!(result.is_err());
    }

    // ========================================
    // COMPARISON TESTS
    // ========================================

    #[test]
    fn test_comparison_total_order() {
        let zero = Ordinal::zero();
        let one = Ordinal::one();
        let five = Ordinal::new_finite(5);
        let ten = Ordinal::new_finite(10);
        let omega = Ordinal::omega();
        let omega_plus_one = omega.clone() + Ordinal::one();

        // Reflexivity
        assert_eq!(zero, zero);
        assert_eq!(omega, omega);

        // Antisymmetry
        assert!(zero < one);
        assert!(one > zero);

        // Transitivity
        assert!(zero < five);
        assert!(five < ten);
        assert!(zero < ten);

        // All finite < all transfinite
        assert!(ten < omega);
        assert!(Ordinal::new_finite(u32::MAX) < omega);

        // Transfinite ordering
        assert!(omega < omega_plus_one);
    }

    #[test]
    fn test_equality() {
        let omega1 = Ordinal::omega();
        let omega2 =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 1).unwrap()]).unwrap();

        assert_eq!(omega1, omega2);

        // Different representations should not be equal
        let omega_plus_one = omega1.clone() + Ordinal::one();
        assert_ne!(omega1, omega_plus_one);
    }

    // ========================================
    // ADDITION PROPERTY TESTS
    // ========================================

    #[test]
    fn test_addition_identity() {
        let test_ordinals = vec![
            Ordinal::zero(),
            Ordinal::one(),
            Ordinal::new_finite(42),
            Ordinal::omega(),
        ];

        for ord in test_ordinals {
            // Right identity: α + 0 = α
            assert_eq!(ord.clone() + Ordinal::zero(), ord);

            // Left identity: 0 + α = α (always true)
            assert_eq!(Ordinal::zero() + ord.clone(), ord);
        }
    }

    #[test]
    fn test_addition_associativity() {
        // (α + β) + γ = α + (β + γ)
        let test_cases = vec![
            (
                Ordinal::one(),
                Ordinal::new_finite(2),
                Ordinal::new_finite(3),
            ),
            (Ordinal::omega(), Ordinal::one(), Ordinal::one()),
            (
                Ordinal::new_finite(5),
                Ordinal::omega(),
                Ordinal::new_finite(10),
            ),
        ];

        for (alpha, beta, gamma) in test_cases {
            let left = (alpha.clone() + beta.clone()) + gamma.clone();
            let right = alpha.clone() + (beta.clone() + gamma.clone());
            assert_eq!(
                left, right,
                "Associativity failed for ({}) + ({}) + ({})",
                alpha, beta, gamma
            );
        }
    }

    #[test]
    fn test_addition_non_commutative() {
        // Ordinal addition is NOT commutative
        let one = Ordinal::one();
        let omega = Ordinal::omega();

        // 1 + ω = ω (finite terms vanish before infinite)
        assert_eq!(one.clone() + omega.clone(), omega);

        // ω + 1 = ω + 1 (successor of omega)
        let omega_plus_one = omega.clone() + one.clone();
        assert_ne!(omega_plus_one, omega);
        assert_ne!(omega_plus_one, one.clone() + omega.clone());
    }

    #[test]
    fn test_addition_finite_cases() {
        // Finite + Finite should work like integers
        assert_eq!(
            Ordinal::new_finite(3) + Ordinal::new_finite(5),
            Ordinal::new_finite(8)
        );

        assert_eq!(
            Ordinal::new_finite(100) + Ordinal::new_finite(200),
            Ordinal::new_finite(300)
        );
    }

    #[test]
    fn test_addition_finite_transfinite() {
        let omega = Ordinal::omega();

        // Finite + Transfinite = Transfinite (finite vanishes)
        assert_eq!(Ordinal::new_finite(1000) + omega.clone(), omega);

        // Transfinite + Finite adds to constant term
        let omega_plus_five = omega.clone() + Ordinal::new_finite(5);
        assert!(omega_plus_five > omega);
        assert!(omega_plus_five.is_successor());
    }

    #[test]
    fn test_addition_omega_cases() {
        let omega = Ordinal::omega();
        let omega_squared =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap()])
                .unwrap();

        // ω + ω = ω·2
        let two_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 2).unwrap()]).unwrap();
        assert_eq!(omega.clone() + omega.clone(), two_omega);

        // ω + ω² = ω²
        assert_eq!(omega.clone() + omega_squared.clone(), omega_squared);

        // ω² + ω = ω² + ω (different from ω + ω²)
        let omega_squared_plus_omega = omega_squared.clone() + omega.clone();
        assert_ne!(omega_squared_plus_omega, omega_squared);
        assert!(omega_squared_plus_omega > omega_squared);
    }

    // ========================================
    // MULTIPLICATION PROPERTY TESTS
    // ========================================

    #[test]
    fn test_multiplication_zero() {
        let test_ordinals = vec![
            Ordinal::zero(),
            Ordinal::one(),
            Ordinal::new_finite(42),
            Ordinal::omega(),
        ];

        for ord in test_ordinals {
            // 0 · α = 0
            assert_eq!(Ordinal::zero() * ord.clone(), Ordinal::zero());

            // α · 0 = 0
            assert_eq!(ord.clone() * Ordinal::zero(), Ordinal::zero());
        }
    }

    #[test]
    fn test_multiplication_identity() {
        let test_ordinals = vec![
            Ordinal::zero(),
            Ordinal::one(),
            Ordinal::new_finite(42),
            Ordinal::omega(),
            Ordinal::omega() + Ordinal::one(),
        ];

        for ord in test_ordinals {
            // 1 · α = α
            assert_eq!(Ordinal::one() * ord.clone(), ord);

            // α · 1 = α
            assert_eq!(ord.clone() * Ordinal::one(), ord);
        }
    }

    #[test]
    fn test_multiplication_associativity() {
        // (α · β) · γ = α · (β · γ)
        let test_cases = vec![
            (
                Ordinal::new_finite(2),
                Ordinal::new_finite(3),
                Ordinal::new_finite(4),
            ),
            (
                Ordinal::omega(),
                Ordinal::new_finite(2),
                Ordinal::new_finite(3),
            ),
        ];

        for (alpha, beta, gamma) in test_cases {
            let left = (alpha.clone() * beta.clone()) * gamma.clone();
            let right = alpha.clone() * (beta.clone() * gamma.clone());
            assert_eq!(
                left, right,
                "Associativity failed for ({}) * ({}) * ({})",
                alpha, beta, gamma
            );
        }
    }

    #[test]
    fn test_multiplication_non_commutative() {
        // Ordinal multiplication is NOT commutative
        let two = Ordinal::new_finite(2);
        let omega = Ordinal::omega();

        // 2 · ω = ω (finite multiple absorbed)
        assert_eq!(two.clone() * omega.clone(), omega);

        // ω · 2 = ω + ω = ω·2
        let two_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 2).unwrap()]).unwrap();
        assert_eq!(omega.clone() * two.clone(), two_omega);

        // They're different!
        assert_ne!(two.clone() * omega.clone(), omega.clone() * two.clone());
    }

    #[test]
    fn test_multiplication_finite_cases() {
        assert_eq!(
            Ordinal::new_finite(3) * Ordinal::new_finite(4),
            Ordinal::new_finite(12)
        );

        assert_eq!(
            Ordinal::new_finite(7) * Ordinal::new_finite(6),
            Ordinal::new_finite(42)
        );
    }

    #[test]
    fn test_multiplication_omega_cases() {
        let omega = Ordinal::omega();

        // ω · ω = ω²
        let omega_squared =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone() * omega.clone(), omega_squared);

        // ω · 3 = ω + ω + ω
        let three_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::one(), 3).unwrap()]).unwrap();
        assert_eq!(omega.clone() * Ordinal::new_finite(3), three_omega);
    }

    #[test]
    fn test_left_distributivity() {
        // α · (β + γ) = α · β + α · γ (LEFT distributivity holds)
        let test_cases = vec![
            (
                Ordinal::new_finite(2),
                Ordinal::new_finite(3),
                Ordinal::new_finite(4),
            ),
            (
                Ordinal::new_finite(5),
                Ordinal::new_finite(1),
                Ordinal::new_finite(10),
            ),
        ];

        for (alpha, beta, gamma) in test_cases {
            let left = alpha.clone() * (beta.clone() + gamma.clone());
            let right = (alpha.clone() * beta.clone()) + (alpha.clone() * gamma.clone());
            assert_eq!(
                left, right,
                "Left distributivity failed for {} * ({} + {})",
                alpha, beta, gamma
            );
        }
    }

    #[test]
    fn test_right_distributivity_fails() {
        // (α + β) · γ ≠ α · γ + β · γ for ordinals in general
        // Example: (1 + 1) · ω = 2 · ω = ω, but 1 · ω + 1 · ω = ω + ω = ω·2
        let one = Ordinal::one();
        let omega = Ordinal::omega();

        let left = (one.clone() + one.clone()) * omega.clone(); // 2 · ω = ω
        let right = (one.clone() * omega.clone()) + (one.clone() * omega.clone()); // ω + ω = ω·2

        assert_ne!(
            left, right,
            "Right distributivity should NOT hold for ordinals"
        );
    }

    // ========================================
    // EXPONENTIATION PROPERTY TESTS
    // ========================================

    #[test]
    fn test_exponentiation_base_cases() {
        let test_ordinals = vec![
            Ordinal::zero(),
            Ordinal::one(),
            Ordinal::new_finite(5),
            Ordinal::omega(),
        ];

        for ord in test_ordinals {
            // α^0 = 1
            assert_eq!(ord.clone().pow(Ordinal::zero()), Ordinal::one());

            // α^1 = α
            assert_eq!(ord.clone().pow(Ordinal::one()), ord);

            // 1^α = 1
            assert_eq!(Ordinal::one().pow(ord.clone()), Ordinal::one());

            // 0^α = 0 (for α > 0)
            if ord != Ordinal::zero() {
                assert_eq!(Ordinal::zero().pow(ord.clone()), Ordinal::zero());
            }
        }
    }

    #[test]
    fn test_exponentiation_finite() {
        // Test finite exponentiation
        assert_eq!(
            Ordinal::new_finite(2).pow(Ordinal::new_finite(3)),
            Ordinal::new_finite(8)
        );

        assert_eq!(
            Ordinal::new_finite(3).pow(Ordinal::new_finite(4)),
            Ordinal::new_finite(81)
        );

        assert_eq!(
            Ordinal::new_finite(5).pow(Ordinal::new_finite(2)),
            Ordinal::new_finite(25)
        );
    }

    #[test]
    fn test_exponentiation_omega() {
        let omega = Ordinal::omega();

        // ω^2 = ω · ω
        let omega_squared =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap()])
                .unwrap();
        assert_eq!(omega.clone().pow(Ordinal::new_finite(2)), omega_squared);

        // ω^ω
        let omega_omega =
            Ordinal::new_transfinite(&vec![CnfTerm::new(&omega.clone(), 1).unwrap()]).unwrap();
        assert_eq!(omega.clone().pow(omega.clone()), omega_omega);

        // 2^ω = ω (any finite^ω = ω for finite ≥ 2)
        assert_eq!(Ordinal::new_finite(2).pow(omega.clone()), omega);
        assert_eq!(Ordinal::new_finite(10).pow(omega.clone()), omega);
    }

    #[test]
    fn test_exponentiation_laws() {
        let two = Ordinal::new_finite(2);
        let three = Ordinal::new_finite(3);

        // α^(β+γ) = α^β · α^γ for finite α, β, γ
        let base = Ordinal::new_finite(2);
        let exp_sum = two.clone() + three.clone();
        let left = base.clone().pow(exp_sum);
        let right = base.clone().pow(two.clone()) * base.clone().pow(three.clone());
        assert_eq!(left, right);

        // (α^β)^γ = α^(β·γ) for finite values
        let base = Ordinal::new_finite(2);
        let left = base.clone().pow(two.clone()).pow(three.clone());
        let right = base.clone().pow(two.clone() * three.clone());
        assert_eq!(left, right);
    }

    // ========================================
    // SUCCESSOR AND LIMIT TESTS
    // ========================================

    #[test]
    fn test_successor_properties() {
        let test_ordinals = vec![
            Ordinal::zero(),
            Ordinal::one(),
            Ordinal::new_finite(41),
            Ordinal::omega(),
            Ordinal::omega() + Ordinal::new_finite(5),
        ];

        for ord in test_ordinals {
            let succ = ord.successor();

            // Successor is always greater
            assert!(succ > ord);

            // Successor is never a limit
            assert!(!succ.is_limit());
            assert!(succ.is_successor());

            // α < α+1
            assert_eq!(succ.clone(), ord.clone() + Ordinal::one());
        }
    }

    #[test]
    fn test_limit_ordinals() {
        let limits = vec![
            Ordinal::zero(),
            Ordinal::omega(),
            Ordinal::omega() * Ordinal::new_finite(2),
            Ordinal::omega().pow(Ordinal::new_finite(2)),
            Ordinal::omega().pow(Ordinal::omega()),
        ];

        for limit in limits {
            assert!(limit.is_limit());
            assert!(!limit.is_successor());
        }
    }

    #[test]
    fn test_successor_ordinals() {
        let successors = vec![
            Ordinal::one(),
            Ordinal::new_finite(42),
            Ordinal::omega() + Ordinal::one(),
            Ordinal::omega() + Ordinal::new_finite(100),
            Ordinal::omega().pow(Ordinal::new_finite(2)) + Ordinal::one(),
        ];

        for succ in successors {
            assert!(succ.is_successor());
            assert!(!succ.is_limit());
        }
    }

    // ========================================
    // CNF TERM TESTS
    // ========================================

    #[test]
    fn test_cnf_term_ordering() {
        let one = Ordinal::one();
        let two = Ordinal::new_finite(2);

        let term1 = CnfTerm::new(&one, 1).unwrap();
        let term2 = CnfTerm::new(&one, 2).unwrap();
        let term3 = CnfTerm::new(&two, 1).unwrap();

        // Terms ordered first by exponent, then by multiplicity
        assert!(term1 < term2); // Same exponent, different multiplicity
        assert!(term1 < term3); // Different exponent
        assert!(term2 < term3); // Different exponent
    }

    #[test]
    fn test_cnf_term_display() {
        // Test display formatting
        let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();
        assert_eq!(format!("{}", omega_term), "ω");

        let omega_times_3 = CnfTerm::new(&Ordinal::one(), 3).unwrap();
        assert_eq!(format!("{}", omega_times_3), "ω * 3");

        let omega_squared = CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap();
        assert_eq!(format!("{}", omega_squared), "ω^2");

        let finite = CnfTerm::new_finite(42);
        assert_eq!(format!("{}", finite), "42");
    }

    #[test]
    fn test_cnf_term_accessors() {
        let term = CnfTerm::new(&Ordinal::new_finite(3), 5).unwrap();

        assert_eq!(term.exponent(), Ordinal::new_finite(3));
        assert_eq!(term.multiplicity(), 5);
        assert!(term.is_limit());
        assert!(!term.is_successor());
        assert!(!term.is_finite());
    }

    // ========================================
    // ORDINAL DISPLAY TESTS
    // ========================================

    #[test]
    fn test_ordinal_display() {
        assert_eq!(format!("{}", Ordinal::zero()), "0");
        assert_eq!(format!("{}", Ordinal::one()), "1");
        assert_eq!(format!("{}", Ordinal::new_finite(42)), "42");
        assert_eq!(format!("{}", Ordinal::omega()), "ω");

        let omega_plus_one = Ordinal::omega() + Ordinal::one();
        assert_eq!(format!("{}", omega_plus_one), "ω + 1");

        let omega_squared = Ordinal::omega().pow(Ordinal::new_finite(2));
        assert_eq!(format!("{}", omega_squared), "ω^2");
    }

    // ========================================
    // COMPLEX ORDINAL TESTS
    // ========================================

    #[test]
    fn test_complex_ordinal_construction() {
        // Build ω² + ω·3 + 7
        let complex = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(), // ω²
            CnfTerm::new(&Ordinal::one(), 3).unwrap(),         // ω·3
            CnfTerm::new_finite(7),                            // 7
        ])
        .unwrap();

        assert!(complex.is_transfinite());
        assert!(complex.is_successor()); // Ends in finite term
        assert_eq!(format!("{}", complex), "ω^2 + ω * 3 + 7");
    }

    #[test]
    fn test_complex_arithmetic() {
        // (ω² + ω + 1) + (ω² + 5) = ω²·2 + 5 (adds leading terms with same exponent)
        let ord1 = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
            CnfTerm::new(&Ordinal::one(), 1).unwrap(),
            CnfTerm::new_finite(1),
        ])
        .unwrap();

        let ord2 = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
            CnfTerm::new_finite(5),
        ])
        .unwrap();

        let sum = ord1 + ord2.clone();

        // Result should be ω²·2 + 5
        let expected = Ordinal::new_transfinite(&vec![
            CnfTerm::new(&Ordinal::new_finite(2), 2).unwrap(),
            CnfTerm::new_finite(5),
        ])
        .unwrap();

        assert_eq!(sum, expected);
    }

    #[test]
    fn test_epsilon_zero_representation() {
        // ε₀ = ω^ω^ω^... (fixed point)
        // We can't represent true ε₀, but we can represent ω^ω^ω
        let omega = Ordinal::omega();
        let omega_omega = omega.clone().pow(omega.clone());
        let omega_omega_omega = omega.clone().pow(omega_omega.clone());

        assert!(omega < omega_omega);
        assert!(omega_omega < omega_omega_omega);
    }

    // ========================================
    // EDGE CASE TESTS
    // ========================================

    #[test]
    fn test_large_finite_ordinals() {
        let large = Ordinal::new_finite(u32::MAX);
        let omega = Ordinal::omega();

        // Even u32::MAX is less than ω
        assert!(large < omega);

        // But it's still finite
        assert!(large.is_finite());
        assert!(large.is_successor());
    }

    #[test]
    fn test_repeated_operations() {
        let mut ord = Ordinal::one();

        // Add 1 ten times
        for _ in 0..10 {
            ord = ord + Ordinal::one();
        }
        assert_eq!(ord, Ordinal::new_finite(11));

        // Multiply by 2 repeatedly
        let mut ord = Ordinal::new_finite(2);
        for _ in 0..3 {
            ord = ord.clone() * Ordinal::new_finite(2);
        }
        assert_eq!(ord, Ordinal::new_finite(16)); // 2^4
    }
}

// ========================================
// INTEGRATION TESTS
// ========================================

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_goodstein_sequence_related() {
        // Goodstein sequences are related to ordinal arithmetic
        // Test that we can represent ordinals needed for Goodstein analysis
        let omega = Ordinal::omega();
        let omega_squared = omega.clone().pow(Ordinal::new_finite(2));
        let omega_cubed = omega.clone().pow(Ordinal::new_finite(3));

        assert!(omega < omega_squared);
        assert!(omega_squared < omega_cubed);
    }

    #[test]
    fn test_hydra_game_ordinals() {
        // Hydra game uses ordinals up to ε₀
        // Test some typical ordinals that appear
        let omega = Ordinal::omega();
        let omega_omega = omega.clone().pow(omega.clone());

        // Various ordinals that might appear
        let ord1 = omega.clone().pow(Ordinal::new_finite(2)) + omega.clone();
        let ord2 = omega_omega.clone() + Ordinal::one();

        assert!(ord1 < omega_omega);
        assert!(omega_omega < ord2);
    }
}
