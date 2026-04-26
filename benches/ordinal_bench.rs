//! Performance baselines for `Ordinal` arithmetic.
//!
//! These benches exist primarily to detect regressions when refactoring the
//! arithmetic hot paths (clone reduction, trait impl restructuring, and the
//! eventual `finite^transfinite_tower` implementation). Run with:
//!
//! ```text
//! cargo bench --bench ordinal_bench
//! ```
//!
//! To establish a named baseline before a refactor:
//!
//! ```text
//! cargo bench --bench ordinal_bench -- --save-baseline pre-refactor
//! ```
//!
//! And to compare after:
//!
//! ```text
//! cargo bench --bench ordinal_bench -- --baseline pre-refactor
//! ```

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use num_traits::Pow;
use transfinite::{CnfTerm, Ordinal};

fn bench_pow_finite_exponent(c: &mut Criterion) {
    let mut group = c.benchmark_group("pow_omega_to_finite_exponent");
    let omega = Ordinal::omega();
    for exp in [10u32, 100, 1000] {
        group.bench_with_input(BenchmarkId::from_parameter(exp), &exp, |b, &exp| {
            b.iter(|| {
                let result = black_box(omega.clone()).pow(black_box(Ordinal::new_finite(exp)));
                black_box(result)
            });
        });
    }
    group.finish();
}

fn bench_pow_transfinite_exponent(c: &mut Criterion) {
    let omega = Ordinal::omega();
    let omega_plus_one = omega.successor();

    c.bench_function("pow_omega_to_omega", |b| {
        b.iter(|| black_box(omega.clone()).pow(black_box(omega.clone())))
    });

    c.bench_function("pow_omega_to_omega_plus_one", |b| {
        b.iter(|| black_box(omega.clone()).pow(black_box(omega_plus_one.clone())))
    });
}

fn bench_multiplication_chain(c: &mut Criterion) {
    // (ω + 1) chained 100 times via repeated multiplication.
    let omega_plus_one = Ordinal::omega().successor();

    c.bench_function("multiplication_chain_100", |b| {
        b.iter(|| {
            let mut acc = Ordinal::one();
            for _ in 0..100 {
                acc = acc * black_box(omega_plus_one.clone());
            }
            black_box(acc)
        });
    });
}

fn bench_addition(c: &mut Criterion) {
    // (ω² + ω + 1) + (ω² + ω + 1) - exercises the merge path.
    let lhs = Ordinal::builder()
        .omega_power(2)
        .omega_times(1)
        .plus(1)
        .build()
        .unwrap();
    let rhs = lhs.clone();

    c.bench_function("add_three_term_to_three_term", |b| {
        b.iter(|| black_box(lhs.clone()) + black_box(rhs.clone()))
    });
}

fn bench_construction_five_term(c: &mut Criterion) {
    // Construct ω⁴ + ω³ + ω² + ω + 42 via the builder.
    c.bench_function("build_five_term_cnf", |b| {
        b.iter(|| {
            Ordinal::builder()
                .omega_power(4)
                .omega_power(3)
                .omega_power(2)
                .omega_times(1)
                .plus(42)
                .build()
                .unwrap()
        });
    });
}

fn bench_successor_three_term(c: &mut Criterion) {
    // successor() on ω² + ω·3 + 7. Trailing term is finite, so this exercises
    // the in-place increment path (Wave 5c will optimize this).
    let three_term = Ordinal::new_transfinite(&[
        CnfTerm::new(&Ordinal::new_finite(2), 1).unwrap(),
        CnfTerm::new(&Ordinal::one(), 3).unwrap(),
        CnfTerm::new_finite(7),
    ])
    .unwrap();

    c.bench_function("successor_three_term_finite_trailing", |b| {
        b.iter(|| black_box(&three_term).successor())
    });
}

criterion_group!(
    benches,
    bench_pow_finite_exponent,
    bench_pow_transfinite_exponent,
    bench_multiplication_chain,
    bench_addition,
    bench_construction_five_term,
    bench_successor_three_term,
);
criterion_main!(benches);
