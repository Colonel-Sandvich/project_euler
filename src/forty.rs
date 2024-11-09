use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fs::{self},
    str::FromStr,
    usize,
};

use itertools::Itertools;

use crate::{from_digits, sieve, to_digit_map, to_digits};

/// ```
/// assert_eq!(project_euler::forty::_21(), 31626);
/// ```
pub fn _21() -> usize {
    let mut sum = 0;
    let mut map = HashMap::with_capacity(10_000);

    for n in 1..10_000 {
        let sum_of_proper_divisors: usize = (1..n).filter(|d| n % d == 0).sum();

        if let Some(possible_counterpart) = map.get(&n) {
            if sum_of_proper_divisors == *possible_counterpart {
                sum += *possible_counterpart + n;
            }
        }

        map.insert(sum_of_proper_divisors, n);
    }

    sum
}

/// ```
/// assert_eq!(project_euler::forty::_22(), 871198282);
/// ```
pub fn _22() -> usize {
    let names_raw = fs::read_to_string("./assets/0022_names.txt").expect("File read error");
    let mut names = names_raw
        .split(",")
        .map(|str| &str[1..str.len() - 1])
        .collect::<Vec<_>>();

    names.sort();

    names
        .into_iter()
        .enumerate()
        .map(|(i, name)| {
            (i + 1)
                * name
                    .as_bytes()
                    .iter()
                    .map(|x| *x as usize - 64)
                    .sum::<usize>()
            // Convert to ascii value and take off 64 to get per letter score
        })
        .sum()
}

/// ```
/// assert_eq!(project_euler::forty::_23(), 4179871);
/// ```
pub fn _23() -> usize {
    let mut abundant = HashSet::<usize>::new();

    for n in 1..=28123 {
        let sum_of_divisors: usize = (1..n).filter(|d| n % d == 0).sum();
        if sum_of_divisors > n {
            abundant.insert(n);
        }
    }

    let mut sum = 0;

    'a: for i in 1..=28123 {
        for &a in abundant.iter().filter(|&x| i - *x > 0) {
            // filter condition mirrors .contains
            if abundant.contains(&(i - a)) {
                continue 'a;
            }
        }
        sum += i;
    }

    sum
}

/// ```
/// assert_eq!(project_euler::forty::_23_2(), 4179871);
/// ```
/// _23 was pretty slow (~750ms) so I attempted to optimise
/// This is now usually ~16ms
pub fn _23_2() -> usize {
    const N: usize = 28123;
    // All numbers are divisible by one
    let mut sieve = [1; N];

    // Use a sieve to make the sum of divisors wholesale rather than on demand
    for d in 2..=N {
        for i in ((2 * d)..sieve.len()).step_by(d) {
            sieve[i] += d;
        }
    }

    let abundant: Vec<_> = sieve
        .into_iter()
        .enumerate()
        .filter(|&(i, x)| x > i && i > 0) // Don't include 0
        .map(|(i, _)| i)
        .collect();

    let mut numbers = Vec::from_iter(0..=N);

    // Compute all possible sums of abundant numbers and wipe them from numbers
    for &a in &abundant {
        for &b in &abundant {
            if a + b <= N {
                numbers[a + b] = 0;
            }
        }
    }

    numbers.iter().sum()
}

/// ```
/// assert_eq!(project_euler::forty::_24(), "2783915460");
/// ```
pub fn _24() -> String {
    // Starting with "0123456789"
    // After 9! permutations we know that the number 1 will have moved to the front since
    // there's 9 numbers after 0
    // Following this insight we can extract the first digit by counting how many 9!'s fit into
    // 999_999 (1 less than a million since the starting number is #1)
    // Then we use the number leftover to find out how many 8!'s fit into it to extract the 2nd digit
    // and so on.

    let mut available_digits = String::from_str("0123456789").unwrap();

    let mut permutations = 1_000_000 - 1;
    let mut digit_index;
    let mut factorial: usize = (1..=9).product();

    let mut number = String::new();

    for i in (0..=9).rev() {
        (digit_index, permutations) = (permutations / factorial, permutations % factorial);
        number.push(available_digits.remove(digit_index));
        if i != 0 {
            factorial /= i;
        }
    }

    number
}

/// ```
/// assert_eq!(project_euler::forty::_25(), 4782);
/// ```
pub fn _25() -> usize {
    // Rather than trying to compute fibonacci numbers with 1000 digits
    // We can use log_10 and Binet's formula to compute this directly
    // F_n > 10^999 (1000 digits)
    // log_10(F_n) > 999
    // log_10(phi^n - (1/phi)^n) - log_10(sqrt(5)) > 999
    // Notice that (1/phi^n) will be small for large n
    // ~~~ log_10(phi^n) > 999 + log_10(sqrt(5))
    // n > (999 + log_10(sqrt(5))))/log_10(phi)
    // n > 4781.85927
    // so n = 4782
    4782
}

/// ```
/// assert_eq!(project_euler::forty::_26(), 983);
/// ```
pub fn _26() -> usize {
    let mut div;
    let mut remainder;
    let mut max_cycle = 0;
    let mut max_d = 2;
    for d in 2..1000 {
        let mut digits = vec![];
        let mut carry = 10;

        let len = loop {
            (div, remainder) = (carry / d, carry % d);

            if digits.contains(&(div, remainder)) {
                break digits.len();
            }

            digits.push((div, remainder));
            carry = 10 * remainder;
        };

        if len > max_cycle {
            max_d = d;
        }

        max_cycle = max_cycle.max(len);
    }

    max_d
}

/// ```
/// assert_eq!(project_euler::forty::_27(), -59231);
/// ```
pub fn _27() -> i32 {
    const N: usize = 18_000;
    let primes: HashSet<usize> = sieve::<N>()
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x)
        .map(|(i, _)| i)
        .collect();

    let mut best_ab = (0, 0);
    let mut max_length = 0;

    // Since n starts at 0 b will always need to be a positive prime number
    for b in (2i32..1000).filter(|&p| primes.contains(&(p as usize))) {
        for a in -999i32..=999 {
            let mut length = 0;
            for n in 0.. {
                let p = n * n + a * n + b;
                // If this fails bump up N to make sure we have enough primes to quickly look up
                assert!(p < N as i32);
                if !primes.contains(&(p as usize)) {
                    break;
                }

                length += 1;
            }
            if length > max_length {
                best_ab = (a, b);
            }

            max_length = max_length.max(length);
        }
    }

    best_ab.0 * best_ab.1
}

/// ```
/// assert_eq!(project_euler::forty::_28(), 669171001);
/// ```
pub fn _28() -> usize {
    // We can observe that the values of the diagonals are given by starting at the top right
    // which is always a square, call this n^2
    // Then traversing anti-clockwise we take off (n-1) from n^2 for each diagonal
    // Therefore the sum of one level containing 4 diagonal numbers is given by
    // n^2 + n^2 - (n - 1) + n^2 - 2(n - 1) + n^2 - 3(n - 1)
    // = 4n^2 - 6(n - 1) = 4n^2 - 6n + 6
    // But this n is always odd, so really n = 2 * k + 1, where k is the current level
    // For a 1001x1001 square there's 500 levels
    //

    (1..=500)
        .map(|k| 2 * k + 1)
        .map(|n| 4 * n * n - 6 * n + 6)
        .sum::<usize>()
        + 1 // Don't forget the one in the centre
}

/// ```
/// assert_eq!(project_euler::forty::_29(), 9183);
/// ```
pub fn _29() -> usize {
    // A term may only be non unique if another power of the base can be in the list
    // e.g. 2^4 is copied by 4^2
    // So we need only consider the possible powers of a base and rule out duplicates
    // It's worth noting that different lowest term bases can never copy each other
    // e.g. 2^a != 3^b for any integers a,b
    // 2: 2,4,8,16,32,64,
    // 3: 3,9,27,81,
    // 4: covered by 2,
    // 5: 5,25,
    // 6: 6,36,
    // 7: 7,49,
    // 8: covered by 2,
    // 9: covered by 3,
    // 10: 10,100,
    // 11 and above: can never duplicate since 11^2 = 121 > 100

    let mut count = 99 * 99;

    for a in [2, 3, 5, 6, 7, 10] {
        let mut cache = HashSet::new();

        let number_of_powers_under_100 = (100 as f32).log(a as f32).floor() as usize;

        // This just iterates through the possible powers (excluding 1) and counts uniqueness
        // p^i:     2,3,4,5,..,100   | Looking at just two of these it can be observed that almost half of the 100
        // (p^2)^i: 4,6,8,10,..,200  | will be covered by the even terms of the lower. Just '2' is not covered giving a total of 49 duplicates
        //                           | And this was independent of the base so 5, 6, 7, and 10 all give 49 duplicates and I could optimise this away
        //
        //
        for i in 1..=number_of_powers_under_100 {
            for n in (2..=100).map(|x| x * i) {
                if cache.contains(&n) {
                    count -= 1;
                }
                cache.insert(n);
            }
        }
    }

    count as usize
}

/// ```
/// assert_eq!(project_euler::forty::_30(), 443839);
/// ```
pub fn _30() -> usize {
    // We're constricted to fifth powers of digits and so for a given length of number say l
    // The maximum possible fifth power digit sum is l*9^5
    // From experimenting with some values it can be seen that a length of 7 gives a 6 digit number
    // It's pretty clear that this outpaces the digit sum and so we place our upper search bound at 6 digits

    let mut total = 0;

    for i in 2..1_000_000 {
        let fifth_power_digit_sum = i
            .to_string()
            .chars()
            .map(|c| c.to_digit(10).unwrap().pow(5) as usize)
            .sum::<usize>();
        if fifth_power_digit_sum == i {
            total += i;
        }
    }

    total
}

/// ```
/// assert_eq!(project_euler::forty::_31(), 73682);
/// ```
pub fn _31() -> usize {
    // Classic dynamic programming problem.
    // If we start from 200p then subtract 20p then we know if we somehow had already made 180p
    // then we'd have an additional way to make 200p
    // Let's do this for every coin

    let coins = [1, 2, 5, 10, 20, 50, 100, 200];

    let mut num_of_ways = [0; 201];
    num_of_ways[0] = 1;

    for coin in coins {
        for i in coin..=200usize {
            num_of_ways[i] += num_of_ways[i - coin];
        }
    }

    num_of_ways[200]
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
/// No idea how to prove this is the smallest number of its from tho
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
