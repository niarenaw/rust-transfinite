//! # Ordinal Exponentiation Example
//!
//! This example demonstrates ordinal exponentiation with a transfinite base.
//!
//! We compute (ω³ + ω)⁵ and verify the result matches the expected value
//! ω¹⁵ + ω¹³, following the rules of ordinal exponentiation.
//!
//! ## Mathematical Background
//!
//! For ordinal exponentiation with a transfinite base and finite exponent:
//! - (ω^α + ω^β)^n involves distributing the exponentiation
//! - The leading term dominates: ω^(α·n)
//! - This library uses binary exponentiation for O(log n) performance
//!
//! ## Running This Example
//!
//! ```bash
//! cargo run --example exponentiation
//! ```

use num_traits::Pow;
use ordinal::{CnfTerm, Ordinal};

fn main() {
    // Construct the base ordinal: ω³ + ω
    let base = Ordinal::new_transfinite(&[
        CnfTerm::new(&Ordinal::new_finite(3), 1).unwrap(), // ω³
        CnfTerm::new(&Ordinal::new_finite(1), 1).unwrap(), // ω
    ])
    .unwrap();

    println!("Base ordinal: {}", base);
    println!("Computing: ({})^5", base);
    println!();

    // Compute (ω³ + ω)⁵
    let result = base.pow(Ordinal::new_finite(5));

    // Expected result: ω¹⁵ + ω¹³
    let expected = Ordinal::new_transfinite(&[
        CnfTerm::new(&Ordinal::new_finite(15), 1).unwrap(), // ω¹⁵
        CnfTerm::new(&Ordinal::new_finite(13), 1).unwrap(), // ω¹³
    ])
    .unwrap();

    println!("Result:   {}", result);
    println!("Expected: {}", expected);
    println!();

    if result == expected {
        println!("✓ Exponentiation computed correctly!");
    } else {
        println!("✗ Unexpected result!");
    }
}
