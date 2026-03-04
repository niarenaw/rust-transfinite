# src/

## Purpose

Library source code. Four modules re-exported through `lib.rs`.

---

## Modules

| File | Type | Purpose |
|------|------|---------|
| `lib.rs` | Entry point | Crate-level docs, lint attrs, `pub use` re-exports |
| `ordinal.rs` | Core type | `Ordinal` enum, `Add`/`Mul`/`Pow` impls, `binary_pow`, validation |
| `cnfterm.rs` | Core type | `CnfTerm` struct — a single ω^exp · mult term |
| `builder.rs` | API | `OrdinalBuilder` — fluent builder for CNF construction |
| `error.rs` | Error | `OrdinalError` enum and `Result` type alias |

---

## Data Flow

```
User input
    │
    ├─► Ordinal::new_finite(n)           → Ordinal::Finite(n)
    ├─► Ordinal::new_transfinite(&[...]) → validate_cnf_terms → Ordinal::Transfinite(vec)
    └─► Ordinal::builder().omega_power(2).plus(3).build()
            └─► validates incrementally → transfinite_unchecked(vec)

Arithmetic (Add/Mul/Pow)
    └─► pattern match on (lhs, rhs) variant pairs
        └─► construct result using from_parts / transfinite_unchecked
            (bypasses re-validation for internally-guaranteed-valid results)
```

## Key Internal APIs

These are `pub(crate)` and not part of the public interface:

| Function | Purpose |
|----------|---------|
| `CnfTerm::from_parts(exp, mult)` | Owned-exponent constructor (avoids clone) |
| `Ordinal::transfinite_unchecked(vec)` | Wraps valid vec without re-validation |
| `Ordinal::validate_cnf_terms(&[])` | CNF ordering check (used by public constructors) |
| `binary_pow(base, exp)` | O(log n) exponentiation for finite exponents |

---

## Related

- **Parent**: [→ ../CLAUDE.md](../CLAUDE.md)
- **Tests**: [→ ../tests/CLAUDE.md](../tests/CLAUDE.md)
