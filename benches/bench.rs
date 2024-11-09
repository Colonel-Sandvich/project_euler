use std::collections::HashSet;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use project_euler::forty;

fn problem_23(c: &mut Criterion) {
    let mut group = c.benchmark_group("problem 23");
    group.sample_size(10);
    group.bench_function("orig", |b| b.iter(|| black_box(forty::_23())));
    group.bench_function("new", |b| b.iter(|| black_box(forty::_23_2())));
    group.bench_function("pre sieve", |b| b.iter(|| black_box(pre_sieve())));
    group.bench_function("sieve", |b| b.iter(|| black_box(sieve())));
    group.finish();
}

fn sieve() -> usize {
    const N: usize = 28123;
    let mut sieve = [1; N];

    // Use a sieve to make the sum of divisors wholesale rather than on demand
    for d in 2..=N {
        for i in ((2 * d)..sieve.len()).step_by(d) {
            sieve[i] += d;
        }
    }

    let abundant: Vec<_> = sieve
        .iter()
        .enumerate()
        .filter(|&(i, x)| *x > i && i > 0)
        .map(|(i, _)| i)
        .collect();

    abundant.len()
}

fn pre_sieve() -> usize {
    let mut abundant = HashSet::<usize>::new();

    for n in 1..=28123 {
        let sum_of_divisors: usize = (1..n).filter(|d| n % d == 0).sum();
        if sum_of_divisors > n {
            abundant.insert(n);
        }
    }

    abundant.len()
}

fn problem_27(c: &mut Criterion) {
    c.bench_function("problem 27", |b| b.iter(|| forty::_27()));
}

fn problem_50(c: &mut Criterion) {
    let mut group = c.benchmark_group("problem 50");
    group.bench_function("backtracking with skips", |b| {
        b.iter(|| black_box(forty::_50_backtracking()))
    });
    group.bench_function("brute force", |b| {
        b.iter(|| black_box(forty::_50_brute_force()))
    });
    group.finish();
}

criterion_group!(benches, problem_50);
criterion_main!(benches);
