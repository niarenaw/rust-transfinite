#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

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
//! // Create ordinals (From<u32> enables .into() for finite ordinals)
//! let omega = Ordinal::omega();
//!
//! // Perform ordinal arithmetic using references to avoid cloning
//! let sum = &omega + &Ordinal::from(5);
//! let product = &omega * &Ordinal::from(2);
//! let power = omega.pow(Ordinal::from(2));
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
//! let two: Ordinal = 2.into();
//! let omega = Ordinal::omega();
//!
//! // Addition: 1 + w = w, but w + 1 != w
//! assert_eq!(&one + &omega, omega);
//! assert_ne!(&omega + &one, omega);
//!
//! // Multiplication: 2 * w = w, but w * 2 != w
//! assert_eq!(&two * &omega, omega);
//! assert_ne!(&omega * &two, omega);
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
//! let b: Ordinal = 5.into();
//! let c: Ordinal = 3.into();
//!
//! // (a + b) + c = a + (b + c)
//! assert_eq!((&a + &b) + &c, &a + (&b + &c));
//!
//! // (a * b) * c = a * (b * c)
//! assert_eq!((&a * &b) * &c, &a * (&b * &c));
//! ```
//!
//! ## Properties Summary
//!
//! | Operation | Associative | Commutative | Identity | Absorbing |
//! |-----------|-------------|-------------|----------|-----------|
//! | Addition  | Yes         | **No**      | 0        | -         |
//! | Multiply  | Yes         | **No**      | 1        | 0         |
//! | Power     | **No**      | **No**      | -        | -         |
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
//! use transfinite::Ordinal;
//!
//! // Construct ω² + ω·3 + 7 using the builder API
//! let ordinal = Ordinal::builder()
//!     .omega_power(2)    // ω²
//!     .omega_times(3)    // ω·3
//!     .plus(7)           // 7
//!     .build()
//!     .unwrap();
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
//! - [`OrdinalBuilder`] - Fluent builder for constructing complex ordinals
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
//! let two: Ordinal = 2.into();
//! let three: Ordinal = 3.into();
//! let omega = Ordinal::omega();
//!
//! // Finite arithmetic works as expected
//! assert_eq!(&two + &three, 5.into());
//! assert_eq!(&two * &three, 6.into());
//!
//! // Transfinite arithmetic follows ordinal rules
//! assert_eq!(&omega + &Ordinal::one(), omega.successor());
//! ```
//!
//! ## Exponentiation
//!
//! ```
//! use transfinite::Ordinal;
//! use num_traits::Pow;
//!
//! let omega = Ordinal::omega();
//!
//! // w^2 = w * w
//! let omega_squared = omega.clone().pow(Ordinal::from(2));
//!
//! // w^w (omega to the omega)
//! let omega_omega = omega.clone().pow(omega);
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
//! - Arithmetic operations clone data when needed; use references (`&Ordinal`) to minimize cloning
//! - For CNF term inspection, use [`CnfTerm::exponent_ref()`] to avoid cloning the exponent
//! - Exponentiation with finite exponents uses O(log n) binary exponentiation
//!
//! # Mathematical Background
//!
//! For more information on ordinal arithmetic, see:
//!
//! - [Ordinal Arithmetic (Wikipedia)](https://en.wikipedia.org/wiki/Ordinal_arithmetic)
//! - [Cantor Normal Form (Wikipedia)](https://en.wikipedia.org/wiki/Ordinal_arithmetic#Cantor_normal_form)
//! - [Epsilon Numbers (Wikipedia)](https://en.wikipedia.org/wiki/Epsilon_number)

mod builder;
mod cnfterm;
mod error;
mod ordinal;

pub use crate::builder::OrdinalBuilder;
pub use crate::cnfterm::CnfTerm;
pub use crate::error::{OrdinalError, Result};
pub use crate::ordinal::Ordinal;
