//! # Goodstein Sequences
//!
//! The Goodstein sequence starting at integer `n` is defined as:
//!
//! 1. Write `n` in **hereditary base-2** (every exponent is itself in base-2,
//!    recursively all the way down).
//! 2. Replace every occurrence of the base `2` with `3`. Subtract 1.
//! 3. Replace every `3` with `4`. Subtract 1. Continue.
//!
//! Goodstein's theorem (1944) proves the sequence eventually reaches 0,
//! but the integer values explode in size first. The proof goes through
//! ordinals: replace every base in the hereditary representation with `ω`.
//! The corresponding **ordinal** sequence strictly decreases at every step.
//! Because ordinals below ε₀ are well-ordered, the ordinal sequence must
//! terminate, and so the integer sequence does too.
//!
//! This example traces the (short) Goodstein sequence for `n = 3`,
//! showing the ordinal counterpart at each step. The ordinal sequence is
//! strictly decreasing, even when the integer sequence stays flat or
//! grows transiently.
//!
//! ## Running
//!
//! ```bash
//! cargo run --example goodstein
//! ```

use transfinite::Ordinal;

fn print_step(step: u32, base: u32, value: u32, ordinal: &Ordinal) {
    println!("  step {step:2}:  base {base},  integer = {value:5},  ordinal = {ordinal}");
}

fn main() {
    println!("Goodstein's theorem: the integer sequence terminates because the");
    println!("corresponding ordinal sequence strictly decreases, and ordinals");
    println!("below ε₀ are well-ordered.\n");

    println!("Sequence starting from n = 3:");
    println!("  (hereditary base-2: 3 = 2 + 1, so the starting ordinal is ω + 1)\n");

    // Precomputed Goodstein sequence for n = 3.
    // At each step we show: which base we just bumped to, the integer value,
    // and the ordinal you get by replacing every occurrence of the base with ω.
    let omega = Ordinal::omega();
    let steps: Vec<(u32, u32, u32, Ordinal)> = vec![
        // (step, base, integer, ordinal)
        (0, 2, 3, omega.clone() + Ordinal::one()), // 3 = 2 + 1     -> ω + 1
        (1, 3, 3, omega),                          // 3 = 3         -> ω
        (2, 4, 3, Ordinal::new_finite(3)),         // 3 = 3 (no 4)  -> 3
        (3, 5, 2, Ordinal::new_finite(2)),         // 2 = 2         -> 2
        (4, 6, 1, Ordinal::new_finite(1)),         // 1 = 1         -> 1
        (5, 7, 0, Ordinal::new_finite(0)),         // 0             -> 0  (terminates!)
    ];

    for (step, base, value, ordinal) in &steps {
        print_step(*step, *base, *value, ordinal);
    }

    println!("\nVerifying the ordinal sequence is strictly decreasing:");
    for window in steps.windows(2) {
        let (s_a, _, _, ord_a) = &window[0];
        let (s_b, _, _, ord_b) = &window[1];
        let strictly_less = ord_b < ord_a;
        let marker = if strictly_less { "✓" } else { "✗" };
        println!(
            "  {marker} step {s_a} ({ord_a}) > step {s_b} ({ord_b})  -  {}",
            if strictly_less { "ok" } else { "VIOLATION" }
        );
    }

    println!("\nThe ordinal sequence ω + 1 > ω > 3 > 2 > 1 > 0 has length 6.");
    println!("The integer sequence 3, 3, 3, 2, 1, 0 also has length 6 - they");
    println!("happen to coincide here because n is small. For n = 4 the integer");
    println!("sequence reaches 0 only after a number of steps that does not fit");
    println!("in any reasonable computer (Goodstein numbers grow VERY fast),");
    println!("yet the ordinal sequence stays bounded by ω^ω throughout.\n");

    println!("This is the headline use case for ordinals up to ε₀: certifying");
    println!("termination of processes that vastly exceed primitive recursive");
    println!("bounds.");
}
