//! # Approaching ε₀
//!
//! ε₀ (epsilon-zero) is the smallest ordinal `α` satisfying `ω^α = α`.
//! Equivalently, it is the limit of the tower
//!
//! ```text
//! ω, ω^ω, ω^(ω^ω), ω^(ω^(ω^ω)), ...
//! ```
//!
//! Each rung is finitely larger than the previous, but ε₀ itself is the
//! supremum of the entire infinite sequence.
//!
//! This crate represents ordinals **strictly below ε₀** in Cantor Normal
//! Form. ε₀ itself is not representable - by the fixed-point definition,
//! you would need ε₀ to appear inside its own CNF, which the data
//! structure does not allow.
//!
//! This example walks the tower for a few rungs, prints each one, and
//! confirms that the sequence is strictly increasing. It also demonstrates
//! the representation cap: how big the ordinals can get before allocation
//! becomes prohibitive.
//!
//! ## Running
//!
//! ```bash
//! cargo run --example epsilon_zero
//! ```

use num_traits::Pow;
use transfinite::Ordinal;

/// Compute the n-th rung of the tower ω, ω^ω, ω^(ω^ω), ω^(ω^(ω^ω)), ...
fn tower(n: u32) -> Ordinal {
    let mut current = Ordinal::omega();
    for _ in 1..n {
        current = Ordinal::omega().pow(current);
    }
    current
}

fn main() {
    println!("Approaching ε₀: the tower ω, ω^ω, ω^(ω^ω), ...\n");

    // The first few rungs are small enough to print.
    for n in 1..=4 {
        let rung = tower(n);
        println!("  rung {n}:  {rung}");
    }
    println!();

    println!("Each rung is strictly greater than the previous:");
    for n in 1..=4 {
        let here = tower(n);
        let next = tower(n + 1);
        let strictly_less = here < next;
        let marker = if strictly_less { "✓" } else { "✗" };
        println!("  {marker} rung {n} < rung {}", n + 1);
    }
    println!();

    // The supremum of all rungs is ε₀, which satisfies ω^ε₀ = ε₀.
    // No ordinal in this crate can express ε₀ directly: any attempt to
    // construct ω^ε₀ recursively would require ε₀ to appear inside its
    // own Cantor Normal Form, which the data structure forbids.
    println!("All rungs are strictly less than ε₀.");
    println!("ε₀ is defined as the smallest fixed point of ω^x = x, the");
    println!("supremum of this very sequence. No ordinal expressible in this");
    println!("crate equals ε₀: any attempt to construct ω^ε₀ via this API");
    println!("would require ε₀ to appear inside its own Cantor Normal Form,");
    println!("which the type system prevents (you would loop indefinitely).\n");

    // Demonstrate the representation cap: building deeper rungs.
    // The ordinal stays small to print but contains a deeply nested CNF tree.
    let rung_10 = tower(10);
    let formatted = format!("{}", rung_10);
    println!(
        "Rung 10 has a string representation of length {}.",
        formatted.len()
    );
    println!("Even at this depth, the underlying CNF data structure handles it");
    println!("comfortably: just a recursive Vec<CnfTerm> of depth 10. Going");
    println!("deeper is bounded by available memory rather than by any cap in");
    println!("the type itself.\n");

    println!("Summary: ε₀ is the upper boundary of what this crate represents.");
    println!("Every ordinal you can construct via Ordinal::builder, From<u32>,");
    println!("Add, Mul, or Pow lives strictly below it.");
}
