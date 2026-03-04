# transfinite

## Purpose

Rust library for transfinite ordinal arithmetic up to ε₀ (epsilon-zero) using Cantor Normal Form (CNF). Published to [crates.io](https://crates.io/crates/transfinite).

## What's Here

Single-crate Rust library. No workspace, no binary targets. MSRV is **1.81**, edition 2021.

---

## Project Structure

| Path | Purpose | Documentation |
|------|---------|---------------|
| `src/` | Library source (4 modules + lib.rs) | [→ CLAUDE.md](./src/CLAUDE.md) |
| `tests/` | Integration and property-based tests | [→ CLAUDE.md](./tests/CLAUDE.md) |
| `examples/` | Runnable examples (`cargo run --example`) | Single file: `exponentiation.rs` |
| `.github/workflows/` | CI pipeline (fmt, clippy, test, MSRV, audit) | `ci.yml` |

## Key Files

| File | Purpose |
|------|---------|
| `Cargo.toml` | Crate metadata, deps, `[lints]` section |
| `CHANGELOG.md` | Keep a Changelog format release history |
| `README.md` | Crates.io / GitHub landing page |

---

## Commands

```bash
cargo test                  # Run all 180+ tests (unit, integration, property, doc)
cargo clippy -- -D warnings # Lint (enforced in CI and pre-commit hook)
cargo fmt -- --check        # Format check
cargo doc --no-deps         # Generate docs
cargo run --example exponentiation  # Run example
```

Pre-commit hooks (`cargo-husky`) run `cargo fmt --check` and `cargo clippy` automatically.

---

## Architecture

```
                        Ordinal (enum)
                       /              \
              Finite(u32)     Transfinite(Vec<CnfTerm>)
                                        |
                              CnfTerm { exponent: Ordinal, multiplicity: u32 }
                                        |
                              (recursive: exponent is itself an Ordinal)
```

CNF representation: `α = ω^β₁·c₁ + ω^β₂·c₂ + ... + ω^βₙ·cₙ` where `β₁ > β₂ > ... > βₙ`.

Arithmetic is implemented via `Add`, `Mul`, and `Pow` traits on owned and borrowed `Ordinal` values.

---

## Key Conventions

### Performance

- Use `exponent_ref()` over `exponent()` to avoid cloning
- Use `into_parts()` when consuming a `CnfTerm`
- Internal arithmetic uses `CnfTerm::from_parts` (owned) and `Ordinal::transfinite_unchecked` (skips re-validation of already-valid vecs; `debug_assert` in dev builds)
- `new_transfinite()` is for public/untrusted construction only

### Error Handling

- Public constructors return `Result<T, OrdinalError>`
- Internal code uses `expect()` with invariant descriptions, never bare `unwrap()`
- `todo!()` with description for unimplemented paths (documented with `# Panics`)

### Documentation

- `#![deny(missing_docs)]` — every public item must have doc comments
- Doc comments include `# Examples`, `# Errors`, and `# Panics` sections where applicable
- Comments should be concise prose explaining *why*, not *what*

### Testing

- Unit tests live in `#[cfg(test)] mod tests` inside each source file
- Integration tests in `tests/` cover cross-module behavior
- Property-based tests use `proptest` for algebraic law verification
- All doc examples are tested (`cargo test --doc`)

### Lints

Configured in `Cargo.toml` `[lints]` section — `clippy::all` warn, `redundant_clone` warn, plus `#![deny(missing_docs)]` in `lib.rs`.

---

## Dependencies

| Crate | Purpose |
|-------|---------|
| `num-traits` | `Pow` trait for exponentiation |
| `thiserror` | Derive macro for `OrdinalError` |
| `proptest` (dev) | Property-based testing |
| `cargo-husky` (dev) | Pre-commit hooks |
