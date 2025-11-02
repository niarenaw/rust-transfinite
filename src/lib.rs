//! Transfinite ordinal arithmetic library supporting ordinals up to ε₀.
//!
//! This library implements ordinal number arithmetic using [Cantor Normal Form](https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form) (CNF)
//! representation. Ordinals extend natural numbers to describe order types of
//! well-ordered sets, including infinite ordinals like ω (omega).
//!
//! # What Are Ordinals?
//!
//! Ordinal numbers measure "position" in a well-ordered sequence, extending
//! beyond finite numbers into the transfinite:
//!
//! - 0, 1, 2, ... (finite ordinals)
//! - ω (omega - first infinite ordinal)
//! - ω+1, ω+2, ... (successors of omega)
//! - ω·2, ω·3, ... (finite multiples of omega)
//! - ω², ω³, ... (powers of omega)
//! - ω^ω, ω^(ω^ω), ... (exponential towers)
//! - ε₀ (epsilon-zero - first fixed point of ω^x = x)
//!
//! # Quick Start
//!
//! ```
//! use transfinite::Ordinal;
//! use num_traits::Pow;
//!
//! // Create finite and transfinite ordinals
//! let five = Ordinal::new_finite(5);
//! let omega = Ordinal::omega();
//!
//! // Perform ordinal arithmetic
//! let sum = omega.clone() + five.clone();
//! let product = omega.clone() * Ordinal::new_finite(2);
//! let power = omega.clone().pow(Ordinal::new_finite(2));
//!
//! println!("ω + 5 = {}", sum);        // Prints: ω + 5
//! println!("ω · 2 = {}", product);    // Prints: ω * 2
//! println!("ω² = {}", power);         // Prints: ω^2
//! ```
//!
//! # Ordinal Arithmetic
//!
//! Ordinal arithmetic differs fundamentally from standard arithmetic:
//!
//! ## Non-Commutativity
//!
//! Addition and multiplication are **not commutative**:
//!
//! ```
//! use transfinite::Ordinal;
//!
//! let one = Ordinal::one();
//! let omega = Ordinal::omega();
//!
//! // Addition: 1 + ω = ω, but ω + 1 ≠ ω
//! assert_eq!(one.clone() + omega.clone(), omega);
//! assert_ne!(omega.clone() + one.clone(), omega);
//!
//! // Multiplication: 2 · ω = ω, but ω · 2 ≠ ω
//! let two = Ordinal::new_finite(2);
//! assert_eq!(two.clone() * omega.clone(), omega);
//! assert_ne!(omega.clone() * two.clone(), omega);
//! ```
//!
//! ## Associativity
//!
//! Addition and multiplication **are associative**:
//!
//! ```
//! use transfinite::Ordinal;
//!
//! let a = Ordinal::omega();
//! let b = Ordinal::new_finite(5);
//! let c = Ordinal::new_finite(3);
//!
//! // (a + b) + c = a + (b + c)
//! assert_eq!((a.clone() + b.clone()) + c.clone(), a.clone() + (b.clone() + c.clone()));
//!
//! // (a · b) · c = a · (b · c)
//! assert_eq!((a.clone() * b.clone()) * c.clone(), a.clone() * (b.clone() * c.clone()));
//! ```
//!
//! # Cantor Normal Form Representation
//!
//! Every ordinal α < ε₀ can be uniquely expressed in Cantor Normal Form:
//!
//! ```text
//! α = ω^β₁·c₁ + ω^β₂·c₂ + ... + ω^βₙ·cₙ
//! ```
//!
//! where β₁ > β₂ > ... > βₙ are ordinals and c₁, c₂, ..., cₙ are positive finite numbers.
//!
//! This library uses CNF internally for efficient arithmetic:
//!
//! ```
//! use transfinite::{Ordinal, CnfTerm};
//!
//! // Construct ω² + ω·3 + 7 using CNF terms
//! let ordinal = Ordinal::new_transfinite(&vec![
//!     CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),  // ω²
//!     CnfTerm::new(&Ordinal::one(), 3).unwrap(),          // ω·3
//!     CnfTerm::new_finite(7),                             // 7
//! ]).unwrap();
//!
//! println!("{}", ordinal);  // Prints: ω^2 + ω * 3 + 7
//! ```
//!
//! # Limit vs Successor Ordinals
//!
//! Ordinals are classified as either:
//!
//! - **Limit ordinals**: No immediate predecessor (e.g., 0, ω, ω², ω^ω)
//! - **Successor ordinals**: Form α+1 for some ordinal α (e.g., 1, 5, ω+1)
//!
//! ```
//! use transfinite::Ordinal;
//!
//! let zero = Ordinal::zero();
//! let omega = Ordinal::omega();
//!
//! assert!(zero.is_limit());      // 0 is a limit
//! assert!(omega.is_limit());     // ω is a limit
//!
//! let one = zero.successor();
//! assert!(one.is_successor());   // 1 = 0+1 is a successor
//!
//! let omega_plus_one = omega.successor();
//! assert!(omega_plus_one.is_successor());  // ω+1 is a successor
//! ```
//!
//! # Core Types
//!
//! - [`Ordinal`] - Main ordinal number type (finite or transfinite)
//! - [`CnfTerm`] - A term in Cantor Normal Form (ω^exponent · multiplicity)
//! - [`OrdinalError`] - Error type for construction failures
//! - [`Result<T>`] - Type alias for `Result<T, OrdinalError>`
//!
//! # Examples
//!
//! ## Basic Arithmetic
//!
//! ```
//! use transfinite::Ordinal;
//!
//! let two = Ordinal::new_finite(2);
//! let three = Ordinal::new_finite(3);
//! let omega = Ordinal::omega();
//!
//! // Finite arithmetic works as expected
//! assert_eq!(two.clone() + three.clone(), Ordinal::new_finite(5));
//! assert_eq!(two.clone() * three.clone(), Ordinal::new_finite(6));
//!
//! // Transfinite arithmetic follows ordinal rules
//! assert_eq!(omega.clone() + Ordinal::one(), omega.clone().successor());
//! ```
//!
//! ## Exponentiation
//!
//! ```
//! use transfinite::Ordinal;
//! use num_traits::Pow;
//!
//! let omega = Ordinal::omega();
//! let two = Ordinal::new_finite(2);
//!
//! // ω² = ω · ω
//! let omega_squared = omega.clone().pow(two.clone());
//!
//! // ω^ω (omega to the omega)
//! let omega_omega = omega.clone().pow(omega.clone());
//! ```
//!
//! ## Comparison
//!
//! ```
//! use transfinite::Ordinal;
//!
//! let five = Ordinal::new_finite(5);
//! let million = Ordinal::new_finite(1_000_000);
//! let omega = Ordinal::omega();
//!
//! // All finite ordinals are less than all transfinite ordinals
//! assert!(five < million);
//! assert!(million < omega);
//! assert!(five < omega);
//! ```
//!
//! # Performance Notes
//!
//! - Finite ordinals use native `u32` for efficient storage and arithmetic
//! - Transfinite ordinals store CNF terms in a vector (most have 1-3 terms)
//! - Arithmetic operations currently clone data; future optimizations planned
//! - Exponentiation uses repeated multiplication (O(n)); binary exponentiation (O(log n)) is planned
//!
//! # Mathematical Background
//!
//! For more information on ordinal arithmetic, see:
//!
//! - [Ordinal Arithmetic (Wikipedia)](https://en.wikipedia.org/wiki/Ordinal_arithmetic)
//! - [Cantor Normal Form (Wikipedia)](https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form)
//! - [Epsilon Numbers (Wikipedia)](https://en.wikipedia.org/wiki/Epsilon_number)

mod cnfterm;
mod error;
mod ordinal;

pub use crate::cnfterm::CnfTerm;
pub use crate::error::{OrdinalError, Result};
pub use crate::ordinal::Ordinal;
