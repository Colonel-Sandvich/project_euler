use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs::{self},
    str::FromStr,
    usize,
};

use itertools::Itertools;

use crate::{from_digits, is_prime, sieve, to_digits};

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
    // The tricky part is iterating through the problem in the right order
    // to avoid a data dependency problem.

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
/// assert_eq!(project_euler::forty::_32(), 45228);
/// ```
pub fn _32() -> usize {
    let mut pandigital_products = HashSet::new();

    // Smallest valid a,b combo of both 3 digits is 123 * 456 giving 56088 a five digit number
    // This is too big so we can rule out both being 3 digit, so I cap a at 2 digits
    for a in 2..100 {
        for b in 2..10000 {
            let c = a * b;

            let combined = [a, b, c].iter().map(|n| n.to_string()).join("");

            if combined.len() != 9
                || combined.contains("0")
                || combined.as_bytes().iter().unique().count() != 9
            {
                continue;
            }

            pandigital_products.insert(c);
        }
    }

    pandigital_products.iter().sum()
}

/// ```
/// assert_eq!(project_euler::forty::_33(), 100);
/// ```
pub fn _33() -> usize {
    let mut matches = vec![];
    for num in 10..100 {
        for denum in (num + 1)..100 {
            let [a, b] = to_digits(num).try_into().unwrap();
            let [c, d] = to_digits(denum).try_into().unwrap();

            if b == 0 {
                continue;
            }

            let (p, q) = if a == c {
                (b, d)
            } else if b == c {
                (a, d)
            } else if a == d {
                (b, c)
            } else if b == d {
                (a, c)
            } else {
                continue;
            };

            if p as f32 / q as f32 == num as f32 / denum as f32 {
                matches.push((num, denum));
            }
        }
    }

    let num = matches.iter().map(|(p, _)| p).product();
    let denum = matches.iter().map(|(_, q)| q).product();
    let d = gcd(num, denum);

    denum / d
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        (a, b) = (b, a % b);
    }

    a
}

/// ```
/// assert_eq!(project_euler::forty::_34(), 40730);
/// ```
/// 9! = 362880 which is the maximum number you can get per digit
/// With some trial and error it can be observed that for an 8 digit number the max sum is
/// 9! * 8 = 2_903_040 which is a 7 digit number so we can place an upper bound to stop searching
/// at 9_999_999
pub fn _34() -> usize {
    (3..10_000_000)
        .filter(|&n| {
            n == to_digits(n)
                .into_iter()
                .map(|d| (1..=d).product::<usize>())
                .sum::<usize>()
        })
        .sum()
}

/// ```
/// assert_eq!(project_euler::forty::_35(), 55);
/// ```
pub fn _35() -> usize {
    const N: usize = 1_000_000;
    let prime_sieve = sieve::<N>();

    let primes: Vec<_> = prime_sieve
        .into_iter()
        .enumerate()
        .filter(|&(_, x)| x)
        .map(|(i, _)| i)
        .collect();

    let mut circular_primes = HashSet::new();

    for prime in primes {
        let mut digits = VecDeque::from(to_digits(prime));
        let rotations: Vec<_> = (0..digits.len())
            .map(|_| {
                let d = digits.pop_front().unwrap();
                digits.push_back(d);
                from_digits(digits.clone())
            })
            .collect();

        if rotations.iter().all(|p| prime_sieve[*p]) {
            for circular_prime in rotations {
                circular_primes.insert(circular_prime);
            }
        }
    }

    circular_primes.len()
}

/// ```
/// assert_eq!(project_euler::forty::_36(), 872187);
/// ```
pub fn _36() -> usize {
    (1..1_000_000)
        .filter(|&x| {
            let digits = to_digits(x);
            let mut reverse = digits.clone();
            reverse.reverse();
            if digits != reverse {
                return false;
            }

            let mut n = x;
            let mut binary_reverse = vec![];
            while n > 0 {
                binary_reverse.push(n % 2);
                n /= 2;
            }

            if binary_reverse[0] == 0 {
                // Trailing zero
                return false;
            }

            let binary = binary_reverse.clone();
            binary_reverse.reverse();

            if binary != binary_reverse {
                return false;
            }

            true
        })
        .sum()
}

/// ```
/// assert_eq!(project_euler::forty::_37(), 748317);
/// ```
pub fn _37() -> usize {
    let mut truncatable_primes = vec![];

    recursive_step(&mut VecDeque::new(), &mut truncatable_primes);

    truncatable_primes.iter().sum()
}

/// Here we try to grow the number as large as we can with digits at the front while keeping the
/// number prime any number we stop growing will be a left-truncatble prime because of this.
/// When we can no longer grow it we check if it's right-truncatable
fn recursive_step(digits: &mut VecDeque<usize>, truncatable_primes: &mut Vec<usize>) {
    for d in [1, 2, 3, 5, 7, 9] {
        digits.push_front(d);
        let number = from_digits(digits.clone());
        if !is_prime(number) {
            digits.pop_front();
            continue;
        }

        let mut candidate = true;
        let mut copy = number / 10;
        while copy > 0 {
            if !is_prime(copy) {
                candidate = false;
            }
            copy /= 10;
        }

        if candidate && number > 10 {
            truncatable_primes.push(number);
        }

        recursive_step(digits, truncatable_primes);
    }

    // We're done growing this number if we reached here, so backtrack a digit and continue the search.
    // e.g. digits = 113 has been explored so go to digits = 213
    digits.pop_front();
}

/// ```
/// assert_eq!(project_euler::forty::_38(), 932718654);
/// ```
pub fn _38() -> usize {
    let mut max = 0;

    for n in 1..10_000 {
        let mut digits = vec![];
        for i in 1.. {
            if digits.len() >= 9 {
                break;
            }

            digits.append(&mut to_digits(n * i));
        }

        if digits.len() > 9 {
            continue;
        }

        let number = from_digits(digits.clone());
        if number < max {
            continue;
        }

        if digits.contains(&0) || digits.iter().unique().count() != 9 {
            continue;
        }

        max = number;
    }

    max
}

/// ```
/// assert_eq!(project_euler::forty::_39(), 840);
/// ```
pub fn _39() -> usize {
    let mut maximising_p = 0;
    let mut max_count = 0;

    for p in (3 + 4 + 5)..=1000 {
        let mut count = 0;
        for a in 1..=p / 2 {
            for b in a..=p / 2 {
                let c = p - a - b;

                if a * a + b * b == c * c {
                    count += 1;
                }
            }
        }

        if count > max_count {
            max_count = count;
            maximising_p = p;
        }
    }

    maximising_p
}

/// ```
/// assert_eq!(project_euler::forty::_40(), 210);
/// ```
pub fn _40() -> usize {
    let mut digit = 1;
    let mut target = 1;

    let mut length_of_num = 1;
    let mut length_helper = 10;

    let mut product = 1;

    for num in 1..=1_000_000 {
        if num == length_helper {
            length_of_num += 1;
            length_helper *= 10;
        }

        if digit + length_of_num > target {
            let digits = to_digits(num);

            product *= digits[target - digit];

            target *= 10;
        }

        digit += length_of_num;
    }

    product
}
