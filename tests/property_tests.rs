// prop_assert_eq! moves its arguments, causing false redundant_clone positives from clippy.
#![allow(clippy::redundant_clone)]

use proptest::prelude::*;
use transfinite::{CnfTerm, Ordinal};

/// Strategy to generate arbitrary ordinals for property testing.
/// Generates a mix of finite and transfinite ordinals with varying complexity.
fn arb_ordinal() -> impl Strategy<Value = Ordinal> {
    prop_oneof![
        // Finite ordinals (0 to 1000)
        (0u32..1000).prop_map(Ordinal::new_finite),
        // Simple transfinite: w * n for n in 1..10
        (1u32..10).prop_map(|n| {
            Ordinal::new_transfinite(&[CnfTerm::new(&Ordinal::one(), n).unwrap()]).unwrap()
        }),
        // Successor transfinite: w * n + m
        ((1u32..5), (1u32..100)).prop_map(|(n, m)| {
            Ordinal::new_transfinite(&[
                CnfTerm::new(&Ordinal::one(), n).unwrap(),
                CnfTerm::new_finite(m),
            ])
            .unwrap()
        }),
        // w^2 * n
        (1u32..5).prop_map(|n| {
            Ordinal::new_transfinite(&[CnfTerm::new(&Ordinal::new_finite(2), n).unwrap()]).unwrap()
        }),
        // w^2 * n + w * m + k
        ((1u32..3), (1u32..5), (1u32..50)).prop_map(|(n, m, k)| {
            Ordinal::new_transfinite(&[
                CnfTerm::new(&Ordinal::new_finite(2), n).unwrap(),
                CnfTerm::new(&Ordinal::one(), m).unwrap(),
                CnfTerm::new_finite(k),
            ])
            .unwrap()
        }),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]

    #[test]
    fn addition_associativity(a in arb_ordinal(), b in arb_ordinal(), c in arb_ordinal()) {
        let left = (a.clone() + b.clone()) + c.clone();
        let right = a + (b + c);
        prop_assert_eq!(left, right);
    }

    #[test]
    fn multiplication_associativity(a in arb_ordinal(), b in arb_ordinal(), c in arb_ordinal()) {
        let left = (a.clone() * b.clone()) * c.clone();
        let right = a * (b * c);
        prop_assert_eq!(left, right);
    }

    #[test]
    fn addition_identity(a in arb_ordinal()) {
        let zero = Ordinal::zero();
        prop_assert_eq!(a.clone() + zero.clone(), a.clone());
        prop_assert_eq!(zero + a.clone(), a);
    }

    #[test]
    fn multiplication_identity(a in arb_ordinal()) {
        let one = Ordinal::one();
        prop_assert_eq!(a.clone() * one.clone(), a.clone());
        prop_assert_eq!(one * a.clone(), a);
    }

    #[test]
    fn multiplication_by_zero(a in arb_ordinal()) {
        let zero = Ordinal::zero();
        prop_assert_eq!(a.clone() * zero.clone(), zero.clone());
        prop_assert_eq!(zero * a, Ordinal::zero());
    }

    #[test]
    fn ordering_reflexive(a in arb_ordinal()) {
        prop_assert!(a <= a.clone());
        prop_assert!(a >= a.clone());
        prop_assert_eq!(a.clone(), a);
    }

    #[test]
    fn ordering_transitive(a in arb_ordinal(), b in arb_ordinal(), c in arb_ordinal()) {
        if a < b && b < c {
            prop_assert!(a < c);
        }
        if a <= b && b <= c {
            prop_assert!(a <= c);
        }
    }

    #[test]
    fn ordering_antisymmetric(a in arb_ordinal(), b in arb_ordinal()) {
        if a <= b && b <= a {
            prop_assert_eq!(a, b);
        }
    }

    #[test]
    fn ordering_total(a in arb_ordinal(), b in arb_ordinal()) {
        prop_assert!(a <= b || b <= a);
    }

    #[test]
    fn successor_is_greater(a in arb_ordinal()) {
        let succ = a.successor();
        prop_assert!(succ > a);
    }

    #[test]
    fn left_distributivity(a in arb_ordinal(), b in arb_ordinal(), c in arb_ordinal()) {
        // a * (b + c) = a * b + a * c
        let left = a.clone() * (b.clone() + c.clone());
        let right = (a.clone() * b) + (a * c);
        prop_assert_eq!(left, right);
    }

    #[test]
    fn finite_addition_commutative(a in 0u32..1000, b in 0u32..1000) {
        let ord_a = Ordinal::new_finite(a);
        let ord_b = Ordinal::new_finite(b);
        prop_assert_eq!(ord_a.clone() + ord_b.clone(), ord_b + ord_a);
    }

    #[test]
    fn finite_multiplication_commutative(a in 0u32..1000, b in 0u32..1000) {
        let ord_a = Ordinal::new_finite(a);
        let ord_b = Ordinal::new_finite(b);
        prop_assert_eq!(ord_a.clone() * ord_b.clone(), ord_b * ord_a);
    }
}
