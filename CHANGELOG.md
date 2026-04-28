# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.0] - 2026-04-28

### Added

- `impl num_traits::Zero` and `impl num_traits::One` for `Ordinal`, enabling
  use in generic contexts that require those traits.
- Inherent `Ordinal::is_zero()`, callable without bringing `num_traits::Zero`
  into scope.
- `Ordinal::leading_cnf_term_ref()` and `Ordinal::trailing_cnf_term_ref()`
  for borrow-only inspection of CNF terms (avoid the clone in the existing
  `leading_cnf_term()` / `trailing_cnf_term()` accessors).
- `Ordinal::cnf_terms_iter()` returning a `slice::Iter<'_, CnfTerm>` so
  callers can iterate without allocating.
- `Ordinal::zero()` and `Ordinal::one()` are now `const fn`.
- `# Examples` section on `OrdinalBuilder::term` matching the style used by
  `omega_power` and `plus`.
- Keep-a-Changelog comparison links footer.
- Three runnable examples under `examples/`: `goodstein`, `hydra`, and
  `epsilon_zero`, each showing how ordinal well-ordering proves termination
  of a process whose integer behavior grows enormously.
- Criterion benchmark suite (`benches/ordinal_bench.rs`) covering binary
  exponentiation, multiplication chains, builder construction, addition,
  ordinal exponentiation, and successor on multi-term CNFs. Run with
  `cargo bench`.
- Test coverage for shared-leading-term comparison (recursive lex compare),
  deeply nested exponent display, and saturating finite arithmetic at
  `u32::MAX`.

### Changed

- Finite-base exponentiation with a transfinite-tower exponent
  (`n^(ω^β · k)` where `β` itself is transfinite, e.g. `2^(ω^ω · 3)`) is
  now fully implemented. Previously this path hit a `todo!()` panic. The
  rule applied is `n^(ω^β · k) = ω^(ω^β · k)` for transfinite `β`, drawn
  from Mario Carneiro's [math.stackexchange answer][carneiro] and David
  Madore's reference Haskell implementation.

[carneiro]: https://math.stackexchange.com/q/2588262

### Breaking

- `OrdinalError` is now `#[non_exhaustive]`. Exhaustive `match` arms over
  this enum will need a wildcard arm. This is a deliberate contract change
  so future error variants can be added without bumping the major version.

### Internal

- `cargo publish` in the release workflow now uses `--locked` to ensure the
  published artifact is built from the committed `Cargo.lock`.
- The publish workflow now uses crates.io trusted publishing (OIDC) instead
  of a long-lived `CARGO_REGISTRY_TOKEN` secret.
- The `Security Audit` CI job has explicit `checks: write` permission so its
  result-reporting step no longer fails on `release/*` push events.

## [0.2.2] - 2026-02-08

### Added

- `CnfTerm::into_parts()` consumes a term and returns `(Ordinal, u32)`.
- `OrdinalError` now implements `PartialEq` and `Eq`.
- Full doc comments with `# Examples`, `# Errors`, and `# Panics` sections on
  all `OrdinalBuilder` public methods.
- `[lints]` configuration section in `Cargo.toml` for consistent lint
  enforcement across the workspace.
- `#![deny(missing_docs)]` and `#![deny(rustdoc::broken_intra_doc_links)]`
  lint attributes.

### Changed

- `CnfTerm::new_finite()` now uses `assert!` with a descriptive message instead
  of `unwrap()` for clearer panic output on zero multiplicity.
- `Display` implementations for `Ordinal` and `CnfTerm` write directly to the
  formatter instead of building intermediate strings.
- `CnfTerm::Ord` implementation uses `exponent_ref()` to avoid cloning.
- CNF validation extracted to `validate_cnf_terms()` helper using `windows(2)`
  with `exponent_ref()` for idiomatic, allocation-free comparison.
- `binary_pow` optimizes the final iteration to avoid an unnecessary clone.
- All production `unwrap()` calls replaced with `expect()` and invariant
  documentation.
- `unimplemented!()` replaced with `todo!()` and description.
- `#[allow(clippy::suspicious_arithmetic_impl)]` replaced with `#[expect]` and
  justification comment.

### Removed

- Redundant `use std::cmp::{Ord, PartialOrd}` imports (already in prelude).
- Stale TODO comment in ordinal doc (validation is already implemented).

## [0.2.1] - 2026-02-07

### Changed

- Modernized docs and tests for initial public release.

## [0.2.0] - 2026-02-06

### Added

- Initial public release with ordinal arithmetic up to ε₀.

[Unreleased]: https://github.com/niarenaw/rust-transfinite/compare/v0.3.0...HEAD
[0.3.0]: https://github.com/niarenaw/rust-transfinite/compare/v0.2.2...v0.3.0
[0.2.2]: https://github.com/niarenaw/rust-transfinite/compare/v0.2.1...v0.2.2
[0.2.1]: https://github.com/niarenaw/rust-transfinite/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/niarenaw/rust-transfinite/releases/tag/v0.2.0
