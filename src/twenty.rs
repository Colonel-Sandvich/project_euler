/// ```
/// assert_eq!(project_euler::twenty::_20(), 648);
/// ```
pub fn _20() -> usize {
    // Same as 16 but instead of "* 2" do a factorial
    let mut num = vec![1];

    for factorial in 1..=100 {
        let mut carry = 0;
        for d in num.iter_mut() {
            *d = *d * factorial + carry;
            carry = *d / 10;
            *d %= 10;
        }
        while carry > 0 {
            num.push(carry % 10);
            carry /= 10;
        }
    }

    num.iter().sum()
}

/// ```
/// assert_eq!(project_euler::twenty::_18(), 1074);
/// ```
pub fn _18() -> usize {
    // We can start at the bottom and work our way up
    //    2
    //  8   5
    // At the bottom the way we maximise our total is by choosing 8 over 5 and this would
    // be the globally optimal choice since there's no more choices to make
    // I claim that we can propagate this optimal sum all the way to the top of the tree and get
    // the result needed.
    //  2 4 6             10 13 15         (10 = 2 + max(8,5), 13 = 4 + max(5,9), ...)
    // 8 5 9 3  Becomes  _  _  _  _
    // This reduces the tree depth by one and preserves our ability to choose the correct path.
    //
    // Index of the start of each line is given by triangle numbers: 0, 1, 3, 6, ...
    let tree_raw = "\
    75
    95 64
    17 47 82
    18 35 87 10
    20 04 82 47 65
    19 01 23 75 03 34
    88 02 77 73 07 63 67
    99 65 04 28 06 16 70 92
    41 41 26 56 83 40 80 70 33
    41 48 72 33 47 32 37 16 94 29
    53 71 44 65 25 43 91 52 97 51 14
    70 11 33 28 77 73 17 78 39 68 17 57
    91 71 52 38 17 14 91 43 58 50 27 29 48
    63 66 04 68 89 53 67 30 73 16 69 87 40 31
    04 62 98 27 23 09 70 98 73 93 38 53 60 04 23";

    let height = tree_raw.lines().count();

    let mut tree = tree_raw
        .split_whitespace()
        .map(|str| str.parse().unwrap())
        .collect::<Vec<usize>>();

    let t = |n: usize| -> usize { n * (n + 1) / 2 }; // Triangle number formula

    for level in (1..height).rev() {
        let start = t(level - 1);
        let end = t(level);
        for upper_level_index in start..end {
            // We can get the index of the number below us by going ahead by the length of this row
            let lower_level_index = upper_level_index + level;
            tree[upper_level_index] += tree[lower_level_index].max(tree[lower_level_index + 1]);
        }
    }

    tree[0]
}

/// ```
/// assert_eq!(project_euler::twenty::_17(), 21124);
/// ```
pub fn _17() -> usize {
    (1..=1000).map(number_to_word_length).sum()
}

#[allow(dead_code)]
pub fn number_to_word_length(x: usize) -> usize {
    match x {
        0 => 0,  //
        1 => 3,  // one
        2 => 3,  // two
        3 => 5,  // three
        4 => 4,  // four
        5 => 4,  // five
        6 => 3,  // six
        7 => 5,  // seven
        8 => 5,  // eight
        9 => 4,  // nine
        10 => 3, // ten
        11 => 6, // eleven
        12 => 6, // twelve
        13 => 8, // thirteen
        14 => 8, // fourteen
        15 => 7, // fifteen
        16 => 7, // sixteen
        17 => 9, // seventeen
        18 => 8, // eighteen
        19 => 8, // nineteen
        20 => 6, // twenty
        30 => 6, // thirty
        40 => 5, // forty
        50 => 5, // fifty
        60 => 5, // sixty
        70 => 7, // seventy
        80 => 6, // eighty
        90 => 6, // ninety
        21..100 => number_to_word_length(x - (x % 10)) + number_to_word_length(x % 10),
        100..1000 => {
            number_to_word_length(x / 100)
                + 7 // 7 -> hundred
                + if x % 100 == 0 { 0 } else { 3 } // Add "and" if not "x00".
                + number_to_word_length(x % 100)
        }
        1000 => 11,
        _ => unreachable!(),
    }
}

/// ```
/// assert_eq!(project_euler::twenty::_16(), 1366);
/// ```
pub fn _16() -> usize {
    // 2^1000 is ~300 digits long and far too big for even u128 for obvious reasons
    // Store the digits in a vec and implement naive multiply and carry over this vec
    let mut num = vec![1];

    for _ in 1..=1000 {
        let mut carry = 0;
        for d in num.iter_mut() {
            *d = *d * 2 + carry;
            carry = *d / 10;
            *d %= 10;
        }
        while carry > 0 {
            num.push(carry % 10);
            carry /= 10;
        }
    }

    num.iter().sum()
}

/// ```
/// assert_eq!(project_euler::twenty::_15(), 137846528820);
/// ```
pub fn _15() -> usize {
    // Just a combinatorics problem
    // There are a total of 20 moves to the right plus 20 moves down
    // And we're choosing 20 of them. So the answer is (20+20)C(20)
    // Using the formula in factorials it can be seen this is 40!/(20!*20!) or simply
    // 40 * 39 * ... * 21 / 20!

    // (21..=40).product::<usize>() / (1..=20).product::<usize>() <- This overflows
    (1..=20)
        .map(|x| (x + 20) as f64 / x as f64)
        .product::<f64>()
        .round() as usize
}

/// ```
/// assert_eq!(project_euler::twenty::_14(), 837799);
/// ```
pub fn _14() -> usize {
    let mut cache = vec![-1; 1_000_000];
    cache[1] = 0;
    let mut max = 0;

    for i in 1..1_000_000usize {
        let mut chain = 0;
        let mut n = i;

        loop {
            if n < 1_000_000 {
                match cache[n] {
                    -1 => {}
                    hit => {
                        chain += hit;
                        break;
                    }
                }
            }

            n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };

            chain += 1;
        }

        cache[i] = chain;

        max = max.max(chain);
    }

    cache
        .iter()
        .enumerate()
        .max_by(|x, y| x.1.cmp(y.1))
        .unwrap()
        .0
}

/// ```
/// assert_eq!(project_euler::twenty::_13(), "5537376230");
/// ```
pub fn _13() -> String {
    const NUMS: &str = "37107287533902102798797998220837590246510135740250
    46376937677490009712648124896970078050417018260538
    74324986199524741059474233309513058123726617309629
    91942213363574161572522430563301811072406154908250
    23067588207539346171171980310421047513778063246676
    89261670696623633820136378418383684178734361726757
    28112879812849979408065481931592621691275889832738
    44274228917432520321923589422876796487670272189318
    47451445736001306439091167216856844588711603153276
    70386486105843025439939619828917593665686757934951
    62176457141856560629502157223196586755079324193331
    64906352462741904929101432445813822663347944758178
    92575867718337217661963751590579239728245598838407
    58203565325359399008402633568948830189458628227828
    80181199384826282014278194139940567587151170094390
    35398664372827112653829987240784473053190104293586
    86515506006295864861532075273371959191420517255829
    71693888707715466499115593487603532921714970056938
    54370070576826684624621495650076471787294438377604
    53282654108756828443191190634694037855217779295145
    36123272525000296071075082563815656710885258350721
    45876576172410976447339110607218265236877223636045
    17423706905851860660448207621209813287860733969412
    81142660418086830619328460811191061556940512689692
    51934325451728388641918047049293215058642563049483
    62467221648435076201727918039944693004732956340691
    15732444386908125794514089057706229429197107928209
    55037687525678773091862540744969844508330393682126
    18336384825330154686196124348767681297534375946515
    80386287592878490201521685554828717201219257766954
    78182833757993103614740356856449095527097864797581
    16726320100436897842553539920931837441497806860984
    48403098129077791799088218795327364475675590848030
    87086987551392711854517078544161852424320693150332
    59959406895756536782107074926966537676326235447210
    69793950679652694742597709739166693763042633987085
    41052684708299085211399427365734116182760315001271
    65378607361501080857009149939512557028198746004375
    35829035317434717326932123578154982629742552737307
    94953759765105305946966067683156574377167401875275
    88902802571733229619176668713819931811048770190271
    25267680276078003013678680992525463401061632866526
    36270218540497705585629946580636237993140746255962
    24074486908231174977792365466257246923322810917141
    91430288197103288597806669760892938638285025333403
    34413065578016127815921815005561868836468420090470
    23053081172816430487623791969842487255036638784583
    11487696932154902810424020138335124462181441773470
    63783299490636259666498587618221225225512486764533
    67720186971698544312419572409913959008952310058822
    95548255300263520781532296796249481641953868218774
    76085327132285723110424803456124867697064507995236
    37774242535411291684276865538926205024910326572967
    23701913275725675285653248258265463092207058596522
    29798860272258331913126375147341994889534765745501
    18495701454879288984856827726077713721403798879715
    38298203783031473527721580348144513491373226651381
    34829543829199918180278916522431027392251122869539
    40957953066405232632538044100059654939159879593635
    29746152185502371307642255121183693803580388584903
    41698116222072977186158236678424689157993532961922
    62467957194401269043877107275048102390895523597457
    23189706772547915061505504953922979530901129967519
    86188088225875314529584099251203829009407770775672
    11306739708304724483816533873502340845647058077308
    82959174767140363198008187129011875491310547126581
    97623331044818386269515456334926366572897563400500
    42846280183517070527831839425882145521227251250327
    55121603546981200581762165212827652751691296897789
    32238195734329339946437501907836945765883352399886
    75506164965184775180738168837861091527357929701337
    62177842752192623401942399639168044983993173312731
    32924185707147349566916674687634660915035914677504
    99518671430235219628894890102423325116913619626622
    73267460800591547471830798392868535206946944540724
    76841822524674417161514036427982273348055556214818
    97142617910342598647204516893989422179826088076852
    87783646182799346313767754307809363333018982642090
    10848802521674670883215120185883543223812876952786
    71329612474782464538636993009049310363619763878039
    62184073572399794223406235393808339651327408011116
    66627891981488087797941876876144230030984490851411
    60661826293682836764744779239180335110989069790714
    85786944089552990653640447425576083659976645795096
    66024396409905389607120198219976047599490197230297
    64913982680032973156037120041377903785566085089252
    16730939319872750275468906903707539413042652315011
    94809377245048795150954100921645863754710598436791
    78639167021187492431995700641917969777599028300699
    15368713711936614952811305876380278410754449733078
    40789923115535562561142322423255033685442488917353
    44889911501440648020369068063960672322193204149535
    41503128880339536053299340368006977710650566631954
    81234880673210146739058568557934581403627822703280
    82616570773948327592232845941706525094512325230608
    22918802058777319719839450180888072429661980811197
    77158542502016545090413245809786882778948721859617
    72107838435069186155435662884062257473692284509516
    20849603980134001723930671666823555245252804609722
    53503534226472524250874054075591789781264330331690";

    NUMS.lines()
        .map(|line| {
            line.trim()
                .split_at(12)
                .0
                .parse::<u64>()
                .expect("Should be a number")
        }) // Only need the first 12 digits since there's 100 numbers. We would need 13 or more past 100 numbers
        .sum::<u64>()
        .to_string()
        .split_at(10)
        .0
        .to_owned()
}

/// ```
/// assert_eq!(project_euler::twenty::_12(), 76576500);
/// ```
pub fn _12() -> u32 {
    // Triangle numbers are given by: T(n) = n * (n + 1)/2
    // So the number of divisors can be more easily found by multiplying the number of divisors of n and n + 1, placing the /2 where necessary
    // Since n and n + 1 share no divisors

    let number_of_divisors = |n: u32| -> u32 {
        let mut num = 0;
        for d in 1..=n {
            if n % d == 0 {
                num += 1;
            }
        }
        num
    };

    for n in 1.. {
        let divisors = if n % 2 == 0 {
            number_of_divisors(n / 2) * number_of_divisors(n + 1)
        } else {
            number_of_divisors(n) * number_of_divisors((n + 1) / 2)
        };

        if divisors > 500 {
            return n * (n + 1) / 2;
        }
    }

    // Loop never exits unless we return. Surprised the compiler can't see this
    unreachable!();
}
/// ```
/// assert_eq!(project_euler::twenty::_11(), 70600674);
/// ```
pub fn _11() -> u32 {
    const GRID_RAW: &str = "08 02 22 97 38 15 00 40 00 75 04 05 07 78 52 12 50 77 91 08
49 49 99 40 17 81 18 57 60 87 17 40 98 43 69 48 04 56 62 00
81 49 31 73 55 79 14 29 93 71 40 67 53 88 30 03 49 13 36 65
52 70 95 23 04 60 11 42 69 24 68 56 01 32 56 71 37 02 36 91
22 31 16 71 51 67 63 89 41 92 36 54 22 40 40 28 66 33 13 80
24 47 32 60 99 03 45 02 44 75 33 53 78 36 84 20 35 17 12 50
32 98 81 28 64 23 67 10 26 38 40 67 59 54 70 66 18 38 64 70
67 26 20 68 02 62 12 20 95 63 94 39 63 08 40 91 66 49 94 21
24 55 58 05 66 73 99 26 97 17 78 78 96 83 14 88 34 89 63 72
21 36 23 09 75 00 76 44 20 45 35 14 00 61 33 97 34 31 33 95
78 17 53 28 22 75 31 67 15 94 03 80 04 62 16 14 09 53 56 92
16 39 05 42 96 35 31 47 55 58 88 24 00 17 54 24 36 29 85 57
86 56 00 48 35 71 89 07 05 44 44 37 44 60 21 58 51 54 17 58
19 80 81 68 05 94 47 69 28 73 92 13 86 52 17 77 04 89 55 40
04 52 08 83 97 35 99 16 07 97 57 32 16 26 26 79 33 27 98 66
88 36 68 87 57 62 20 72 03 46 33 67 46 55 12 32 63 93 53 69
04 42 16 73 38 25 39 11 24 94 72 18 08 46 29 32 40 62 76 36
20 69 36 41 72 30 23 88 34 62 99 69 82 67 59 85 74 04 36 16
20 73 35 29 78 31 90 01 74 31 49 71 48 86 81 16 23 57 05 54
01 70 54 71 83 51 54 69 16 92 33 48 61 43 52 01 89 19 67 48";

    let grid: Vec<Vec<u32>> = GRID_RAW
        .lines()
        .map(|line| {
            let temp = line
                .split_whitespace()
                .map(|str| {
                    assert_eq!(str.len(), 2);

                    str.parse().unwrap()
                })
                .collect::<Vec<_>>();

            assert_eq!(temp.len(), 20);

            temp
        })
        .collect();

    assert_eq!(grid.len(), 20);

    let mut max = 0;

    // It's sufficient to look to the right and down and both diagonals to the right (-,|,/,\)
    for (y, line) in grid.iter().enumerate() {
        for x in 0..line.len() {
            // Down
            if y + 4 <= grid.len() {
                max = max.max((0..4).map(|i| grid[y + i][x]).product());
            }

            // Right
            if x + 4 <= line.len() {
                max = max.max((0..4).map(|i| grid[y][x + i]).product());
            }

            // Diagonal-Right-Up
            if x + 4 <= line.len() && y > 4 {
                max = max.max((0..4).map(|i| grid[y - i][x + i]).product());
            }

            // Diagonal-Right-Down
            if x + 4 <= line.len() && y + 4 <= grid.len() {
                max = max.max((0..4).map(|i| grid[y + i][x + i]).product());
            }
        }
    }

    max
}

/// ```
/// assert_eq!(project_euler::twenty::_10(), 142913828922);
/// ```
pub fn _10() -> usize {
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

    sum_of_primes
}

/// ```
/// assert_eq!(project_euler::twenty::_9(), 31875000);
/// ```
pub fn _9() -> usize {
    for a in (1..500).rev() {
        for b in (1..500).rev() {
            let c = 1000 - a - b;
            if c > a + b {
                break;
            }

            if a * a + b * b == c * c {
                return a * b * c;
            }
        }
    }

    panic!("Failed to find pythagorean triple");
}

/// ```
/// assert_eq!(project_euler::twenty::_8(), 23514624000);
/// ```
pub fn _8() -> u64 {
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

    NUM.chars()
        .map_windows(|window: &[_; 13]| {
            window
                .iter()
                .map(|x| x.to_digit(10).expect("Given non-digit") as u64)
                .product::<u64>()
        })
        .max()
        .expect("No maximum??")
}

/// ```
/// assert_eq!(project_euler::twenty::_7(), 104743);
/// ```
pub fn _7() -> usize {
    const N: usize = 10_001;
    let n: f32 = N as f32;
    // https://en.wikipedia.org/wiki/Prime_number_theorem#Approximations_for_the_nth_prime_number
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

    sieve
        .into_iter()
        .enumerate()
        .filter(|(_, x)| *x)
        .nth(N - 1)
        .expect("ruh roh")
        .0
}

/// ```
/// assert_eq!(project_euler::twenty::_6(), 25164150);
/// ```
pub fn _6() -> i32 {
    let n: i32 = 100;
    let sum_of_squares = n * (n + 1) * (2 * n + 1) / 6;
    let square_of_sum = (n * (n + 1) / 2).pow(2);

    square_of_sum - sum_of_squares
}

/// ```
/// assert_eq!(project_euler::twenty::_5(), 232792560);
/// ```
pub fn _5() -> i32 {
    const PRIMES: [i32; 8] = [2, 3, 5, 7, 11, 13, 17, 19]; // 1..=20
    let mut max_prime_factor_powers = [0; PRIMES.len()];

    for mut x in 2..=20 {
        for (p, t) in PRIMES.iter().zip(max_prime_factor_powers.iter_mut()) {
            let mut c = 0;
            while x % p == 0 {
                c += 1;
                x /= p;
            }
            *t = (*t).max(c);
        }
    }

    PRIMES
        .iter()
        .zip(max_prime_factor_powers)
        .map(|(p, power)| p.pow(power))
        .product()
}

/// ```
/// assert_eq!(project_euler::twenty::_4(), 906609);
/// ```
pub fn _4() -> i32 {
    for c in (100..1000).rev() {
        // Modulus maths to create a 6 digit palindrome from a 3 digit number
        let candidate = c * 1000 + (c / 100) + 10 * ((c / 10) % 10) + 100 * (c % 10);

        for factor in 100..1000 {
            if candidate % factor != 0 {
                continue;
            }

            let other_factor = candidate / factor;

            if (100..1000).contains(&other_factor) {
                return candidate;
            }
        }
    }

    panic!("Failed to find ANY palindromes with two 3 digit factors");
}

/// ```
/// assert_eq!(project_euler::twenty::_3(), 6857);
/// ```
pub fn _3() -> u64 {
    let mut n = 600851475143;

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

    largest_prime_factor
}

/// ```
/// assert_eq!(project_euler::twenty::_2(), 4613732);
/// ```
pub fn _2() -> i32 {
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

    sum
}

/// ```
/// assert_eq!(project_euler::twenty::_1(), 233168);
/// ```
pub fn _1() -> i32 {
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

    total
}
