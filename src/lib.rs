#![feature(iter_map_windows)]

use std::iter::once;

pub mod forty;
pub mod sixty;
pub mod twenty;

// Attempt at compile time sieve
const fn sieve<const N: usize>() -> [bool; N] {
    assert!(N > 2);
    let mut sieve = [true; N];
    sieve[0] = false;
    sieve[1] = false;

    let mut p: usize = 2;
    while p <= isqrt(N) as usize {
        let mut i = p * p;
        while i < N {
            sieve[i] = false;
            i += p;
        }

        p += 1;
    }

    sieve
}

pub const fn isqrt(n: usize) -> usize {
    if n <= 1 {
        n
    } else {
        let mut x0 = usize::pow(2, n.ilog2() / 2 + 1);
        let mut x1 = (x0 + n / x0) / 2;
        while x1 < x0 {
            x0 = x1;
            x1 = (x0 + n / x0) / 2;
        }
        x0
    }
}

pub fn from_digits<T>(v: T) -> usize
where
    T: IntoIterator<Item = usize>,
    T::IntoIter: DoubleEndedIterator,
{
    let mut n = 0;
    let mut carry = 1;
    for d in v.into_iter().rev() {
        n += carry * d;
        carry *= 10;
    }
    n
}

pub fn to_digits(mut n: usize) -> Vec<usize> {
    let mut digits = vec![];
    while n > 0 {
        digits.push(n % 10);
        n /= 10;
    }
    digits.reverse();
    digits
}

pub fn to_digit_map(mut n: usize) -> [u8; 10] {
    let mut digits = [0u8; 10];
    while n > 0 {
        digits[n % 10] += 1;
        n /= 10;
    }
    digits
}

pub fn is_prime(n: usize) -> bool {
    if n == 1 {
        return false;
    }
    if n == 2 {
        return true;
    }
    once(2).chain((3..=isqrt(n)).step_by(2)).all(|d| n % d != 0)
}
