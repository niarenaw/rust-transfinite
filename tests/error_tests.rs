//! Error Path and Edge Case Tests
//!
//! This module tests error handling, edge cases, and boundary conditions
//! for the ordinal arithmetic library.

use num_traits::Pow;
use transfinite::{CnfTerm, Ordinal, OrdinalError};

// ========================================
// CNF TERM CONSTRUCTION ERRORS
// ========================================

#[test]
fn test_cnf_term_zero_multiplicity_error() {
    // Multiplicity must be positive (> 0)
    let result = CnfTerm::new(&Ordinal::one(), 0);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        OrdinalError::CnfTermConstructionError
    ));
}

#[test]
fn test_cnf_term_max_multiplicity() {
    // Test with maximum u32 value
    let result = CnfTerm::new(&Ordinal::one(), u32::MAX);
    assert!(result.is_ok());
    let term = result.unwrap();
    assert_eq!(term.multiplicity(), u32::MAX);
}

// ========================================
// ORDINAL CONSTRUCTION ERRORS
// ========================================

#[test]
fn test_transfinite_empty_terms_error() {
    // Cannot create transfinite ordinal with empty terms
    let result = Ordinal::new_transfinite(&[]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        OrdinalError::TransfiniteConstructionError
    ));
}

#[test]
fn test_transfinite_unsorted_terms_error() {
    // Terms must be in strictly decreasing order by exponent
    let term1 = CnfTerm::new(&Ordinal::new_finite(1), 1).unwrap();
    let term2 = CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap();

    // term2 has larger exponent, so it should come first
    let result = Ordinal::new_transfinite(&[term1, term2]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        OrdinalError::TransfiniteConstructionError
    ));
}

#[test]
fn test_transfinite_equal_exponents_error() {
    // Terms with equal exponents should be rejected (not strictly decreasing)
    let term1 = CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap();
    let term2 = CnfTerm::new(&Ordinal::new_finite(2), 2).unwrap();

    let result = Ordinal::new_transfinite(&[term1, term2]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        OrdinalError::TransfiniteConstructionError
    ));
}

#[test]
fn test_transfinite_finite_leading_term_error() {
    // Leading term cannot have exponent 0 (that would be finite)
    let finite_term = CnfTerm::new_finite(5);
    let omega_term = CnfTerm::new(&Ordinal::one(), 1).unwrap();

    // finite_term has exponent 0, omega_term has exponent 1
    // This is increasing order, should fail
    let result = Ordinal::new_transfinite(&[finite_term, omega_term]);
    assert!(result.is_err());
}

// ========================================
// ARITHMETIC EDGE CASES
// ========================================

#[test]
fn test_addition_with_zero() {
    let zero = Ordinal::zero();
    let five = Ordinal::new_finite(5);
    let omega = Ordinal::omega();

    // 0 + n = n (left identity)
    assert_eq!(zero.clone() + five.clone(), five);
    assert_eq!(zero.clone() + omega.clone(), omega);

    // n + 0 = n (right identity)
    assert_eq!(five.clone() + zero.clone(), five);
    assert_eq!(omega.clone() + zero, omega);
}

#[test]
fn test_multiplication_with_zero() {
    let zero = Ordinal::zero();
    let five = Ordinal::new_finite(5);
    let omega = Ordinal::omega();

    // 0 · n = 0 (left absorbing)
    assert_eq!(zero.clone() * five.clone(), zero);
    assert_eq!(zero.clone() * omega.clone(), zero);

    // n · 0 = 0 (right absorbing)
    assert_eq!(five * zero.clone(), zero);
    assert_eq!(omega * zero.clone(), zero);
}

#[test]
fn test_multiplication_with_one() {
    let one = Ordinal::one();
    let five = Ordinal::new_finite(5);
    let omega = Ordinal::omega();

    // 1 · n = n (left identity)
    assert_eq!(one.clone() * five.clone(), five);
    assert_eq!(one.clone() * omega.clone(), omega);

    // n · 1 = n (right identity)
    assert_eq!(five.clone() * one.clone(), five);
    assert_eq!(omega.clone() * one, omega);
}

#[test]
fn test_exponentiation_zero_base() {
    let zero = Ordinal::zero();
    let one = Ordinal::one();
    let five = Ordinal::new_finite(5);
    let omega = Ordinal::omega();

    // 0^0 = 1 (by convention)
    assert_eq!(zero.clone().pow(zero.clone()), one);

    // 0^n = 0 for n > 0
    assert_eq!(zero.clone().pow(one), zero);
    assert_eq!(zero.clone().pow(five), zero);
    assert_eq!(zero.clone().pow(omega), zero);
}

#[test]
fn test_exponentiation_zero_exponent() {
    let zero = Ordinal::zero();
    let one = Ordinal::one();
    let five = Ordinal::new_finite(5);
    let omega = Ordinal::omega();

    // n^0 = 1 for all n
    assert_eq!(zero.clone().pow(zero.clone()), one);
    assert_eq!(one.clone().pow(zero.clone()), one);
    assert_eq!(five.pow(zero.clone()), one);
    assert_eq!(omega.pow(zero), one);
}

#[test]
fn test_exponentiation_one_base() {
    let one = Ordinal::one();
    let zero = Ordinal::zero();
    let five = Ordinal::new_finite(5);
    let omega = Ordinal::omega();

    // 1^n = 1 for all n
    assert_eq!(one.clone().pow(zero), one);
    assert_eq!(one.clone().pow(one.clone()), one);
    assert_eq!(one.clone().pow(five), one);
    assert_eq!(one.clone().pow(omega), one);
}

#[test]
fn test_exponentiation_one_exponent() {
    let one = Ordinal::one();
    let zero = Ordinal::zero();
    let five = Ordinal::new_finite(5);
    let omega = Ordinal::omega();

    // n^1 = n for all n
    assert_eq!(zero.clone().pow(one.clone()), zero);
    assert_eq!(one.clone().pow(one.clone()), one);
    assert_eq!(five.clone().pow(one.clone()), five);
    assert_eq!(omega.clone().pow(one), omega);
}

// ========================================
// LARGE VALUE EDGE CASES
// ========================================

#[test]
fn test_large_finite_addition() {
    let max_half = Ordinal::new_finite(u32::MAX / 2);
    let result = max_half.clone() + max_half;

    // Should not panic, but will wrap around due to u32 arithmetic
    assert!(result.is_finite());
}

#[test]
fn test_large_finite_multiplication() {
    let large = Ordinal::new_finite(u32::MAX / 2);
    let two = Ordinal::new_finite(2);
    let result = large * two;

    // Should not panic, but will wrap around due to u32 arithmetic
    assert!(result.is_finite());
}

#[test]
fn test_very_large_exponentiation() {
    // Test exponentiation with large but reasonable values
    let base = Ordinal::new_finite(2);
    let exp = Ordinal::new_finite(20);
    let result = base.pow(exp);

    // 2^20 = 1048576
    assert_eq!(result, Ordinal::new_finite(1048576));
}

// ========================================
// COMPARISON EDGE CASES
// ========================================

#[test]
fn test_self_equality() {
    let zero = Ordinal::zero();
    let omega = Ordinal::omega();
    let complex = Ordinal::new_transfinite(&[
        CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
        CnfTerm::new(&Ordinal::one(), 3).unwrap(),
    ])
    .unwrap();

    // Every ordinal equals itself
    assert_eq!(zero, zero);
    assert_eq!(omega, omega);
    assert_eq!(complex, complex);
}

#[test]
fn test_transitivity() {
    let one = Ordinal::one();
    let five = Ordinal::new_finite(5);
    let ten = Ordinal::new_finite(10);

    // If a < b and b < c, then a < c
    assert!(one < five);
    assert!(five < ten);
    assert!(one < ten);
}

#[test]
fn test_antisymmetry() {
    let five = Ordinal::new_finite(5);
    let ten = Ordinal::new_finite(10);

    // If a < b, then !(b < a)
    assert!(five < ten);
    assert!((ten >= five));
}

// ========================================
// SUCCESSOR AND LIMIT EDGE CASES
// ========================================

#[test]
fn test_zero_is_limit() {
    // 0 is considered a limit ordinal (has no predecessor)
    assert!(Ordinal::zero().is_limit());
    assert!(!Ordinal::zero().is_successor());
}

#[test]
fn test_successor_of_limit() {
    let omega = Ordinal::omega();
    let omega_plus_one = omega.successor();

    // ω is limit, ω+1 is successor
    assert!(omega.is_limit());
    assert!(omega_plus_one.is_successor());
}

#[test]
fn test_repeated_successor() {
    let mut ord = Ordinal::zero();

    // Applying successor repeatedly should maintain monotonicity
    for _ in 0..10 {
        let next = ord.successor();
        assert!(next > ord);
        ord = next;
    }
}

// ========================================
// REFERENCE TRAIT TESTS
// ========================================

#[test]
fn test_reference_arithmetic() {
    let five = Ordinal::new_finite(5);
    let three = Ordinal::new_finite(3);

    // Test all combinations of owned/borrowed operands
    assert_eq!(&five + &three, Ordinal::new_finite(8));
    assert_eq!(five.clone() + &three, Ordinal::new_finite(8));
    assert_eq!(&five + three.clone(), Ordinal::new_finite(8));
    assert_eq!(five + three, Ordinal::new_finite(8));
}

#[test]
fn test_reference_multiplication() {
    let five = Ordinal::new_finite(5);
    let three = Ordinal::new_finite(3);

    // Test all combinations of owned/borrowed operands
    assert_eq!(&five * &three, Ordinal::new_finite(15));
    assert_eq!(five.clone() * &three, Ordinal::new_finite(15));
    assert_eq!(&five * three.clone(), Ordinal::new_finite(15));
    assert_eq!(five * three, Ordinal::new_finite(15));
}

#[test]
fn test_reference_exponentiation() {
    let two = Ordinal::new_finite(2);
    let three = Ordinal::new_finite(3);

    // Test all combinations of owned/borrowed operands
    assert_eq!((&two).pow(&three), Ordinal::new_finite(8));
    assert_eq!(two.clone().pow(&three), Ordinal::new_finite(8));
    assert_eq!((&two).pow(three.clone()), Ordinal::new_finite(8));
    assert_eq!(two.pow(three), Ordinal::new_finite(8));
}
