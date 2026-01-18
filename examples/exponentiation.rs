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
use transfinite::Ordinal;

fn main() {
    // Construct the base ordinal: ω³ + ω using the builder API
    let base = Ordinal::builder()
        .omega_power(3) // ω³
        .omega() // + ω
        .build()
        .unwrap();

    println!("Base ordinal: {}", base);
    println!("Computing: ({})^5", base);
    println!();

    // Compute (ω³ + ω)⁵
    let result = base.pow(Ordinal::from(5));

    // Expected result: ω¹⁵ + ω¹³
    let expected = Ordinal::builder()
        .omega_power(15) // ω¹⁵
        .omega_power(13) // + ω¹³
        .build()
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
