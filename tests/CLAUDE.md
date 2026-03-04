# tests/

## Purpose

Integration tests exercising the public API across modules. Unit tests live inside `src/` files.

---

## Test Files

| File | Strategy | What It Covers |
|------|----------|----------------|
| `comprehensive_tests.rs` | Deterministic | Ordinal properties, arithmetic laws, CNF construction, integration scenarios (Hydra game, Goodstein) |
| `error_tests.rs` | Deterministic | Error paths, edge cases (zero, overflow, invalid construction), reference arithmetic |
| `property_tests.rs` | Property-based (`proptest`) | Algebraic laws: associativity, commutativity (finite), distributivity, identity, ordering axioms |
| `real_example_tests.rs` | Deterministic | End-to-end arithmetic matching hand-computed mathematical results |

## Test Strategy

```
Unit tests (src/*.rs)          ← Module internals, private functions
    │
Integration tests (tests/)     ← Public API, cross-module behavior
    │
    ├─ Deterministic           ← Known inputs → known outputs
    └─ Property-based          ← Random finite ordinals, verify algebraic laws hold
```

Property tests use `proptest` with finite ordinals (0..1000) since transfinite ordinal generation would require custom strategies.

---

## Related

- **Parent**: [→ ../CLAUDE.md](../CLAUDE.md)
- **Source**: [→ ../src/CLAUDE.md](../src/CLAUDE.md)
