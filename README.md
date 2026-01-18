# Transfinite Ordinal Arithmetic

A Rust library for performing arithmetic operations on [transfinite ordinal numbers](https://plato.stanford.edu/entries/set-theory/) up to ε₀ (epsilon-zero), using Cantor Normal Form representation.

[![Crates.io](https://img.shields.io/crates/v/transfinite.svg)](https://crates.io/crates/transfinite)
[![Documentation](https://docs.rs/transfinite/badge.svg)](https://docs.rs/transfinite)

## What Are Ordinal Numbers?

Ordinal numbers extend the natural numbers to describe the **order type** of well-ordered sets. While natural numbers (0, 1, 2, ...) work well for finite sequences, ordinals continue into the infinite:

- **ω** (omega) represents the order type of all natural numbers
- **ω + 1** comes after all natural numbers, then one more
- **ω · 2** represents two copies of the natural numbers placed end-to-end
- **ω²**, **ω^ω**, and beyond represent increasingly large infinite ordinals

Unlike cardinal numbers (which measure "how many"), ordinals measure "what position" and preserve order information. Ordinal arithmetic has unique properties:

**Addition and multiplication are NOT commutative:**
- `1 + ω = ω` (add one natural number to infinity, still get infinity)
- `ω + 1 > ω` (but infinity plus one is a distinct ordinal!)
- `2 · ω = ω` (two copies of infinity, each infinite, is still infinity)
- `ω · 2 = ω + ω` (infinity doubled is larger than infinity)

This library implements ordinals up to **ε₀** (epsilon-zero), the first ordinal that satisfies ω^ε₀ = ε₀, which is the limit of the finite sequence: ω, ω^ω, ω^(ω^ω), ...

## Features

- **Ordinal arithmetic**: addition, multiplication, exponentiation
- **Comparison and ordering** of ordinals
- **Cantor Normal Form** representation for efficient computation

## Quick Start

Add this to your `Cargo.toml`:

```toml
[dependencies]
transfinite = "0.2.1"
```

### Basic Example

```rust
use transfinite::Ordinal;
use num_traits::Pow;

// Create finite ordinals using From<u32>
let five: Ordinal = 5.into();
let two: Ordinal = 2.into();

// Create the first infinite ordinal
let omega = Ordinal::omega();

// Ordinal arithmetic using references (avoids cloning)
let omega_plus_five = &omega + &five;
let omega_times_two = &omega * &two;
let omega_squared = omega.clone().pow(two);

println!("ω + 5 = {}", omega_plus_five);     // Prints: ω + 5
println!("ω · 2 = {}", omega_times_two);     // Prints: ω * 2
println!("ω² = {}", omega_squared);          // Prints: ω^2
```

### Non-Commutativity Example

```rust
use transfinite::Ordinal;

let one = Ordinal::one();
let omega = Ordinal::omega();

// Addition is NOT commutative
let one_plus_omega = one.clone() + omega.clone();
let omega_plus_one = omega.clone() + one.clone();

assert_eq!(one_plus_omega, omega);  // 1 + ω = ω
assert_ne!(omega_plus_one, omega);  // ω + 1 ≠ ω

println!("1 + ω = {}", one_plus_omega);   // Prints: ω
println!("ω + 1 = {}", omega_plus_one);   // Prints: ω + 1
```

## Using the Builder API

For complex ordinals, the builder pattern is cleaner than manual CNF construction:

```rust
use transfinite::Ordinal;

// Build ω^ω + ω² + ω·5 + 3
let ordinal = Ordinal::builder()
    .omega_exp(Ordinal::omega())  // ω^ω (transfinite exponent)
    .omega_power(2)               // + ω²
    .omega_times(5)               // + ω·5
    .plus(3)                      // + 3
    .build()
    .unwrap();

println!("{}", ordinal);  // Prints: ω^ω + ω^2 + ω * 5 + 3
```

Builder methods:
- `omega()` - Add ω term
- `omega_times(n)` - Add ω·n term
- `omega_power(n)` - Add ω^n term
- `omega_power_times(exp, mult)` - Add ω^exp · mult term
- `omega_exp(ord)` - Add ω^ord term (transfinite exponent)
- `plus(n)` - Add finite constant

## Key Concepts

### Cantor Normal Form (CNF)

Every ordinal α < ε₀ can be uniquely written as:

```
α = ω^β₁·c₁ + ω^β₂·c₂ + ... + ω^βₙ·cₙ
```

where:
- β₁ > β₂ > ... > βₙ (exponents in strictly decreasing order)
- c₁, c₂, ..., cₙ are positive finite coefficients
- This is called the **Cantor Normal Form**

For example:
- `ω² + ω·3 + 7` is in CNF
- `42` = `ω⁰·42` is in CNF (finite ordinals are CNF with exponent 0)
- `ω^ω + ω² + 1` is in CNF

This library represents transfinite ordinals internally using CNF, enabling efficient arithmetic operations.

### Limit vs Successor Ordinals

- **Limit ordinal**: No immediate predecessor (e.g., ω, ω·2, ω²)
  - Informally: "comes from below" via an infinite sequence
- **Successor ordinal**: Has an immediate predecessor α+1 (e.g., 1, 5, ω+1)
  - Informally: "one step after" another ordinal

```rust
use transfinite::Ordinal;

let omega = Ordinal::omega();
assert!(omega.is_limit());          // ω is a limit
assert!(!omega.is_successor());

let omega_plus_one = omega.successor();
assert!(!omega_plus_one.is_limit());     // ω+1 is a successor
assert!(omega_plus_one.is_successor());
```

This distinction matters for multiplication and exponentiation algorithms.

### Ordinal Arithmetic Rules

| Operation | Property | Example |
|-----------|----------|---------|
| **Addition** | Not commutative | `1 + ω = ω`, but `ω + 1 ≠ ω` |
| **Addition** | Associative | `(α + β) + γ = α + (β + γ)` |
| **Multiplication** | Not commutative | `2 · ω = ω`, but `ω · 2 = ω + ω` |
| **Multiplication** | Associative | `(α · β) · γ = α · (β · γ)` |
| **Exponentiation** | Not commutative | `2^ω = ω`, but `ω^2 = ω · ω` |

## Examples

### Building Complex Ordinals

The builder API provides a fluent interface for constructing ordinals in Cantor Normal Form:

```rust
use transfinite::Ordinal;

// ω² (omega squared)
let omega_squared = Ordinal::builder()
    .omega_power(2)
    .build()
    .unwrap();

// ω² + ω·3 + 7
let complex = Ordinal::builder()
    .omega_power(2)    // ω²
    .omega_times(3)    // + ω·3
    .plus(7)           // + 7
    .build()
    .unwrap();

println!("{}", complex);  // Prints: ω^2 + ω * 3 + 7
```

### Exponentiation

```rust
use transfinite::Ordinal;
use num_traits::Pow;

let omega = Ordinal::omega();

// ω^ω (omega to the omega)
let omega_omega = omega.clone().pow(omega.clone());
println!("ω^ω = {}", omega_omega);  // Prints: ω^ω

// ω^(ω^ω) (tower of omegas)
let tower = omega.clone().pow(omega_omega);
println!("ω^(ω^ω) = {}", tower);
```

### Comparison and Ordering

```rust
use transfinite::Ordinal;

let five = Ordinal::new_finite(5);
let omega = Ordinal::omega();
let omega_plus_one = omega.successor();

// All finite ordinals are less than all transfinite ordinals
assert!(five < omega);
assert!(omega < omega_plus_one);

// Standard comparison operators work
assert!(Ordinal::zero() <= Ordinal::one());
assert!(omega.clone() >= omega.clone());
```

## API Overview

### Core Types

- **`Ordinal`** - Main ordinal number type (finite or transfinite)
- **`CnfTerm`** - A term in Cantor Normal Form (ω^exponent · multiplicity)
- **`OrdinalError`** - Error type for construction failures
- **`Result<T>`** - Type alias for `Result<T, OrdinalError>`

### Key Methods

**Constructors:**
- `Ordinal::zero()`, `Ordinal::one()`, `Ordinal::omega()`
- `Ordinal::new_finite(n)` - Create finite ordinal
- `Ordinal::builder()` - Fluent builder for complex ordinals
- `Ordinal::new_transfinite(terms)` - Create from CNF terms (low-level)

**Query Methods:**
- `is_finite()`, `is_transfinite()`
- `is_limit()`, `is_successor()`
- `successor()` - Get the next ordinal (α + 1)

**Arithmetic (trait implementations):**
- `Add` (`+`) - Ordinal addition
- `Mul` (`*`) - Ordinal multiplication
- `Pow` (`.pow()`) - Ordinal exponentiation

**Comparison:**
- `PartialOrd`, `Ord` - Standard Rust ordering

See the [API documentation](https://docs.rs/transfinite) for complete details.

## Limitations

- **Ordinals up to ε₀ only**: Cannot represent ε₁, ε₂, or larger ordinals
- **Finite coefficients**: CNF multiplicities are limited to `u32` (0 to 4,294,967,295)
- **No ordinal subtraction or division**: Ordinal subtraction and division are not well-defined for all ordinals

## Contributing

Contributions are welcome! See the [issue tracker](https://github.com/niarenaw/rust-transfinite/issues) for planned improvements or bug reporting.

## License

This project is licensed under either of:

- MIT License ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)

at your option.
