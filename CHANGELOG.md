# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
