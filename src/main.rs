#![feature(iter_map_windows)]

fn main() {
    _10();
}

fn _10() {
    const N: usize = 2_000_000;

    let mut sieve = vec![true; N];
    sieve[0] = false;
    sieve[1] = false;

    let mut p: usize = 2;
    while p <= N {
        for i in ((2 * p)..sieve.len()).step_by(p) {
            sieve[i] = false;
        }

        if p == 2 {
            p += 1;
        } else {
            p += 2;
        }
    }

    let sum_of_primes: usize = sieve
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x)
        .map(|(i, _)| i)
        .sum();

    println!("Sum of primes below {}: {}", N, sum_of_primes);
}

fn _9() {
    for a in (1..500).rev() {
        for b in (1..500).rev() {
            let c = 1000 - a - b;
            if c > a + b {
                break;
            }

            if a * a + b * b == c * c {
                println!("Product of pythagorean triple: {}", a * b * c);
                return;
            }
        }
    }
}

fn _8() {
    const NUM: &str = "73167176531330624919225119674426574742355349194934\
    96983520312774506326239578318016984801869478851843\
    85861560789112949495459501737958331952853208805511\
    12540698747158523863050715693290963295227443043557\
    66896648950445244523161731856403098711121722383113\
    62229893423380308135336276614282806444486645238749\
    30358907296290491560440772390713810515859307960866\
    70172427121883998797908792274921901699720888093776\
    65727333001053367881220235421809751254540594752243\
    52584907711670556013604839586446706324415722155397\
    53697817977846174064955149290862569321978468622482\
    83972241375657056057490261407972968652414535100474\
    82166370484403199890008895243450658541227588666881\
    16427171479924442928230863465674813919123162824586\
    17866458359124566529476545682848912883142607690042\
    24219022671055626321111109370544217506941658960408\
    07198403850962455444362981230987879927244284909188\
    84580156166097919133875499200524063689912560717606\
    05886116467109405077541002256983155200055935729725\
    71636269561882670428252483600823257530420752963450";

    println!(
        "Maximum sliding product of 13 digits: {}",
        NUM.chars()
            .map_windows(|window: &[_; 13]| {
                window
                    .iter()
                    .map(|x| x.to_digit(10).expect("Given non-digit") as u64)
                    .product::<u64>()
            })
            .max()
            .expect("No maximum??")
    );
}

fn _7() {
    const N: usize = 10_001;
    // https://en.wikipedia.org/wiki/Prime_number_theorem#Approximations_for_the_nth_prime_number
    let n: f32 = N as f32;
    let approximate_size_of_nth_prime: usize = (n * (n.ln() + n.ln().ln())).ceil() as usize;

    let mut sieve = vec![true; approximate_size_of_nth_prime];
    sieve[0] = false;
    sieve[1] = false;

    let mut p = 2;
    while p <= approximate_size_of_nth_prime {
        for i in ((2 * p)..sieve.len()).step_by(p) {
            sieve[i] = false;
        }

        if p == 2 {
            p += 1;
        } else {
            p += 2;
        }
    }

    let nth_prime = sieve
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x)
        .nth(N - 1)
        .expect("ruh roh")
        .0;

    println!("{}th prime: {}", N, nth_prime);
}

fn _6() {
    let n: i32 = 100;
    let sum_of_squares = n * (n + 1) * (2 * n + 1) / 6;
    let square_of_sum = (n * (n + 1) / 2).pow(2);

    println!("Difference: {}", square_of_sum - sum_of_squares);
}

fn _5() {
    const PRIMES: [i32; 8] = [2, 3, 5, 7, 11, 13, 17, 19]; // 1..=20
    let mut max_prime_factor_powers = [0; PRIMES.len()];

    for mut x in 2..=20 {
        for (p, t) in PRIMES.iter().zip(max_prime_factor_powers.iter_mut()) {
            let mut c = 0;
            while x % p == 0 {
                c += 1;
                x = x / p;
            }
            *t = (*t).max(c);
        }
    }

    let product: i32 = PRIMES
        .iter()
        .zip(max_prime_factor_powers)
        .map(|(p, power)| p.pow(power))
        .product();

    println!("Product: {}", product);
}

fn _4() {
    'a: for c in (100..1000).rev() {
        let candidate = c * 1000 + (c / 100) + 10 * ((c / 10) % 10) + 100 * (c % 10);

        for factor in 100..1000 {
            if candidate % factor != 0 {
                continue;
            }

            let other_factor = candidate / factor;

            if 100 <= other_factor && other_factor < 1000 {
                println!("Largest palindrome: {}", candidate);
                break 'a;
            }
        }
    }
}

fn _3() {
    let mut n: u64 = 600851475143;

    let mut factor = 3;
    let mut largest_prime_factor = factor;

    while factor <= n {
        if n % factor == 0 {
            largest_prime_factor = largest_prime_factor.max(factor);
            n /= factor;
            while n % factor == 0 {
                n /= factor;
            }
        }
        factor += 2;
    }

    println!("Largest prime factor: {}", largest_prime_factor);
}

fn _2() {
    let mut a = 0;
    let mut b = 1;
    let mut sum = 0;

    loop {
        let c = a + b;
        if c > 4000000 {
            break;
        }
        if c % 2 == 0 {
            sum += c;
        }
        a = b;
        b = c;
    }

    println!("Sum: {}", sum);
}

fn _1() {
    let multiples = [3, 5];

    let mut total = 0;

    for x in multiples {
        for i in (0..1000).step_by(x) {
            total += i;
        }
    }

    for i in (0..1000).step_by(multiples.iter().product()) {
        total -= i;
    }

    println!("Total: {}", total);
}
