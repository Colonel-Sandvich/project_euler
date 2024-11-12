use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fs::{self},
    usize,
};

use itertools::Itertools;

use crate::{from_digits, is_prime, isqrt, sieve, to_digit_map, to_digits};

/// ```
/// assert_eq!(project_euler::forty::_41(), 7652413);
/// ```
pub fn _41() -> usize {
    let mut max = 0;

    for n in 1..=9 {
        let digits = (1..=n).collect_vec();

        for permutation in digits.into_iter().permutations(n) {
            let num = from_digits(permutation);
            if is_prime(num) {
                max = max.max(num);
            }
        }
    }

    max
}

/// ```
/// assert_eq!(project_euler::forty::_42(), 162);
/// ```
pub fn _42() -> usize {
    let triangle_nums: HashSet<_> = (1..100).map(|n| n * (n + 1) / 2).collect();

    let words_raw = fs::read_to_string("./assets/0042_words.txt").expect("File read error");
    let words = words_raw
        .split(",")
        .map(|str| &str[1..str.len() - 1])
        .collect::<Vec<_>>();

    words
        .into_iter()
        .filter(|word| {
            triangle_nums.contains(
                &word
                    .as_bytes()
                    .iter()
                    .map(|x| *x as usize - 64)
                    .sum::<usize>(),
            )
            // Convert to ascii value and take off 64 to get per letter score
        })
        .count()
}

/// ```
/// assert_eq!(project_euler::forty::_43(), 16695334890);
/// ```
pub fn _43() -> usize {
    let digits = (0..=9).collect_vec();
    let primes = [2, 3, 5, 7, 11, 13, 17];

    let mut sum = 0;

    for permutation in digits.into_iter().permutations(10) {
        let digit_windows = permutation.windows(3).skip(1);
        if digit_windows
            .zip(primes)
            .all(|(window, prime)| from_digits(window.iter().copied()) % prime == 0)
        {
            let number = from_digits(permutation);
            sum += number;
        }
    }

    sum
}

/// ```
/// assert_eq!(project_euler::forty::_44(), 5482660);
/// ```
/// This one is quite tricky as there's no given upper bound and we have no idea in what way to search
/// for a solution.
/// Let's say we have two pentagonal numbers A, B; A<B
/// Then D = B - A, C = A + B => B = A + D, C = 2A + D
/// This reformulation allows us to choose D and A and then check that B and C are pentagonal
/// this is useful as it allows us to start D small and grow it until we find a solution that we know will be minimal
///
/// Solving the inverse function of P(n) gives n = (1 + sqrt(24 * P_n + 1)) / 6
/// So we know if this gives n integer then P_n is actually a pentagonal number
/// We know this will be an integer if the numerator is a multiple of 6 <=> the sqrt is 1 less than a multiple
/// of 6
pub fn _44() -> usize {
    let p = |n: usize| n * (3 * n - 1) / 2;

    let is_pentagonal = |n| {
        let sqrt = (24.0 * n as f64 + 1.0).sqrt();
        sqrt.fract() == 0.0 && sqrt as usize % 6 == 5
    };

    let mut d_index = 0;
    let mut d;

    loop {
        d_index += 1;
        d = p(d_index);

        let mut a_index = 1;
        let mut a = p(a_index);

        // If the difference between A and the next pentagonal number is too big then
        // we know we haven't found a suitable B and C so bump D to the next pentagonal
        while p(a_index + 1) - a <= d {
            if is_pentagonal(a + d) && is_pentagonal(2 * a + d) {
                return d;
            }
            a_index += 1;
            a = p(a_index);
        }
    }
}

/// ```
/// assert_eq!(project_euler::forty::_45(), 1533776805);
/// ```
/// All hexagonal numbers are already triangular numbers!
/// T(n) = n(n+1)/2
/// H(n) = n(2n-1)
/// T(2k-1) = (2k-1)((2k-1) + 1) / 2 = (2k-1)k = H(k)
/// So let's just check if the number is pentagonal using the previous function and start from 144
/// since H_143 is used in the problem
pub fn _45() -> usize {
    let is_pentagonal = |n| {
        let sqrt = (24.0 * n as f64 + 1.0).sqrt();
        sqrt.fract() == 0.0 && sqrt as usize % 6 == 5
    };

    let to_hexagonal = |n: usize| n * (2 * n - 1);

    for h in (144..).map(to_hexagonal) {
        if is_pentagonal(h) {
            return h;
        }
    }

    unreachable!();
}

/// ```
/// assert_eq!(project_euler::forty::_46(), 5777);
/// ```
/// N Chosen by trial and error, I didn't get any insights on how big this one could be
pub fn _46() -> usize {
    const N: usize = 10_000;
    let primes: HashSet<usize> = sieve::<N>()
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x)
        .map(|(i, _)| i)
        .collect();

    for n in (1..).map(|k| 2 * k + 1) {
        if is_prime(n) {
            continue;
        }

        if primes.iter().filter(|&q| *q < n).any(|p| {
            let maybe_square = (n - p) / 2;
            let sqrt = isqrt(maybe_square);

            sqrt * sqrt == maybe_square
        }) {
            continue;
        }

        return n;
    }

    unreachable!();
}

/// ```
/// assert_eq!(project_euler::forty::_47(), 134043);
/// ```
pub fn _47() -> usize {
    let consecutives_with_prime_factors = (0..)
        .map(to_prime_factors)
        .enumerate()
        .tuple_windows::<(_, _, _, _)>()
        .map(|x| [x.0, x.1, x.2, x.3]);

    'a: for nums in consecutives_with_prime_factors {
        if nums.iter().any(|(_, factors)| factors.len() != 4) {
            continue;
        }

        let mut combined_factors: HashSet<(usize, usize)> = HashSet::new();

        for factors in nums.iter().map(|(_, factors)| factors) {
            for (&p, &pow) in factors {
                if combined_factors.contains(&(p, pow)) {
                    continue 'a;
                }

                combined_factors.insert((p, pow));
            }
        }

        return nums[0].0;
    }

    unreachable!();
}

fn to_prime_factors(mut n: usize) -> HashMap<usize, usize> {
    let mut map = HashMap::new();

    let mut p = 2;
    while p * p <= n {
        if n % p == 0 {
            let mut pow = 0;
            while n % p == 0 {
                pow += 1;
                n /= p;
            }
            map.insert(p, pow);
        }
        p += 1;
    }

    // If n is still greater than 1, then it is a prime number
    if n > 1 {
        map.insert(n, 1);
    }

    map
}

/// ```
/// assert_eq!(project_euler::forty::_48(), 9110846700);
/// ```
pub fn _48() -> usize {
    // Naive approach: just mod after every operation to keep it overflowing

    const N: usize = 10_000_000_000;
    let mut sum = 0;

    for a in 1..=1000 {
        let mut b = 1;
        for _ in 1..=a {
            b *= a;
            b %= N;
        }
        sum += b;
        sum %= N;
    }

    sum
}

/// ```
/// assert_eq!(project_euler::forty::_49(), "296962999629");
/// ```
pub fn _49() -> String {
    const N: usize = 10_000;
    let primes: HashSet<usize> = sieve::<N>()
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x)
        .map(|(i, _)| i)
        .filter(|&i| i >= 1000 && i != 1487) // 1487 Given
        .collect();

    for &p in primes.iter() {
        if p >= 3340 {
            // Then p + 2 * 3330 > 10_000
            continue;
        }

        let mut perms = p
            .to_string()
            .chars()
            .permutations(4)
            .unique()
            .map(|q| q.iter().collect::<String>().parse::<usize>().unwrap())
            .filter(|&q| q > 1000 && q != p)
            .collect::<Vec<_>>();

        perms.dedup();

        let q = p + 3330;
        let v = q + 3330;

        if perms.contains(&q) && perms.contains(&v) {
            if primes.contains(&q) && primes.contains(&v) {
                return format!("{}{}{}", p, q, v);
            }
        }
    }

    panic!("Failed to find other 4 digit number with this property");
}

/// ```
/// assert_eq!(project_euler::forty::_50_backtracking(), 997651);
/// ```
/// ~3ms
pub fn _50_backtracking() -> usize {
    const N: usize = 1_000_000;
    let prime_sieve = sieve::<N>();

    let primes: Vec<_> = prime_sieve
        .into_iter()
        .enumerate()
        .filter(|&(_, x)| x)
        .map(|(i, _)| i)
        .collect();

    let mut head = 0;
    let mut tail = 0;
    let mut carry_tail = 0;

    let mut sum = 0;
    let mut carry = 0;

    let mut max_sum = 0;
    let mut max_len = 0;

    loop {
        carry += primes[carry_tail];
        let new_sum = sum + carry;
        let len = carry_tail - head;
        if len > max_len && new_sum < N && prime_sieve[new_sum] {
            sum = new_sum;
            carry = 0;
            tail = carry_tail;

            max_len = len;
            max_sum = sum;
        }

        carry_tail += 1;

        if new_sum >= N || carry_tail >= primes.len() {
            sum = match sum.checked_sub(primes[head]) {
                Some(sum) => sum,
                None => break,
            };

            carry = 0;
            head += 1;
            carry_tail = tail + 1;

            if head + max_len >= primes.len() {
                break;
            }
        }
    }

    max_sum
}

/// ```
/// assert_eq!(project_euler::forty::_50_brute_force(), 997651);
/// ```
/// ~4ms
pub fn _50_brute_force() -> usize {
    const N: usize = 1_000_000;
    let prime_sieve = sieve::<N>();

    let primes: Vec<_> = prime_sieve
        .into_iter()
        .enumerate()
        .filter(|&(_, x)| x)
        .map(|(i, _)| i)
        .collect();

    let mut max_len = 0;
    let mut max_sum = 0;

    for (i, &p) in primes.iter().enumerate() {
        let mut sum = p;
        for (j, &q) in primes.iter().enumerate().skip(i + 1) {
            sum += q;
            if sum >= N {
                break;
            }
            if prime_sieve[sum] {
                let len = j - i;
                if len > max_len {
                    max_len = len;
                    max_sum = sum;
                }
            }
        }
    }

    max_sum
}

/// ```
/// assert_eq!(project_euler::forty::_51(), 121313);
/// ```
pub fn _51() -> usize {
    const N: usize = 1_000_000;
    let primes: BTreeSet<_> = sieve::<N>()
        .into_iter()
        .enumerate()
        .filter(|&(i, x)| i > 10_000 && x)
        .map(|(i, _)| i)
        .collect();

    let mut digits_to_change = 2;

    loop {
        for &p in primes.iter() {
            let digit_map = to_digit_map(p);

            let wildcard_digit = match digit_map
                .iter()
                .enumerate()
                .filter(|&(_, d)| *d >= digits_to_change)
                .next()
            {
                Some(x) => x.0,
                None => continue,
            };

            let generated_numbers = (0..=9)
                .map(|i| {
                    let mut digits = to_digits(p);
                    for d in &mut digits
                        .iter_mut()
                        .filter(|d| **d == wildcard_digit)
                        .take(digits_to_change as usize)
                    {
                        *d = i;
                    }

                    digits
                })
                .map(from_digits)
                .collect::<Vec<_>>();

            let generated_that_are_prime: Vec<_> = generated_numbers
                .iter()
                .filter(|&num| primes.contains(num))
                .collect();
            if generated_that_are_prime.len() == 8 {
                let [first, second] = generated_that_are_prime[0..=1].try_into().unwrap();
                // Just incase the first number generated change it's first digit to 0
                // e.g.     040609, 141619, 242629,...
                if to_digits(*first).len() == to_digits(*second).len() {
                    return *first;
                }
            }
        }

        digits_to_change += 1;
    }
}

/// ```
/// assert_eq!(project_euler::forty::_52(), 142857);
/// ```
/// Actually a beautiful result relating to how 1/7 has a recurring decimal of 142857
/// and 2/7 = 0.285714 ...
/// No idea how to prove this is the smallest number of its form tho
pub fn _52() -> usize {
    'a: for x in 1.. {
        let digit_map = to_digit_map(x);
        for i in 2..=6 {
            if digit_map != to_digit_map(i * x) {
                continue 'a;
            }
        }

        return x;
    }

    unreachable!();
}
