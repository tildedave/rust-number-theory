extern crate num;
extern crate rand;

use self::num::One;
use self::num::Signed;
use self::num::Zero;
use self::rand::distributions::{Distribution, Standard};
use self::rand::thread_rng;
use self::rand::Rng;
use std::cmp::PartialOrd;
use std::fmt::Display;
use std::ops::BitAnd;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
use std::ops::Shl;
use std::ops::Shr;
use std::ops::Sub;

fn leftmost_bit<T>(g: T) -> T
where
    T: Shr<Output = T> + PartialEq + Zero + One,
{
    let mut n = T::zero();
    let mut r = g;

    while r != T::zero() {
        r = r >> T::one();
        if r != T::zero() {
            n = n + T::one();
        }
    }
    return n;
}

fn mod_positive<T>(n: T, a: T) -> T
where
    T: Rem<Output = T> + Sub<Output = T> + PartialOrd + Signed + Copy,
{
    let m = n % a;
    if m < T::zero() {
        m + a
    } else {
        m
    }
}

// Return the individual prime factors associated with a number
fn prime_factor(n: i32) -> Vec<i32> {
    let mut factors = Vec::new();
    let mut x = n;

    for i in 2..isqrt(x) + 1 {
        while x % i == 0 {
            factors.push(i);
            x = x / i;
        }
    }

    // remainder was prime
    if x != 1 {
        factors.push(x);
    }

    return factors;
}

// Algorithm 1.2.1 (Right-Left Binary) pg 8
fn mod_exp<T>(g: T, n: T, p: T) -> T
where
    T: Zero
        + One
        + Sub<Output = T>
        + Copy
        + PartialEq
        + PartialOrd
        + std::ops::Neg<Output = T>
        + Rem<Output = T>
        + Mul<Output = T>
        + Div<Output = T>,
{
    let mut y = T::one();
    let mut z;
    let mut exp;
    if n == T::zero() {
        return y;
    } else if n < T::zero() {
        exp = -n;
        z = mod_inverse(g, p);
    } else {
        exp = n;
        z = g;
    }

    while exp > T::zero() {
        if is_odd(exp) {
            y = (y * z) % p;
        }
        z = (z * z) % p;
        exp = exp / (T::one() + T::one());
    }

    return y;
}

/// Algorithm 1.2.3 (Left-Right Binary; using bits) pg 9
fn mod_exp2(g: i32, n: i32, p: i32) -> i32 {
    let z;
    let exp;

    if n == 0 {
        return 1;
    } else if n < 0 {
        exp = -n;
        z = mod_inverse(g, p);
    } else {
        exp = n;
        z = g;
    }

    let mut y = z;
    let mut f = leftmost_bit(exp);

    while f > 0 {
        f -= 1;
        y = (y * y) % p;
        if exp & (1 << f) != 0 {
            y = (y * z) % p;
        }
    }

    return y;
}

fn mod_inverse<T>(m: T, p: T) -> T
where
    T: Zero
        + One
        + Sub<Output = T>
        + Copy
        + PartialEq
        + PartialOrd
        + std::ops::Neg<Output = T>
        + Rem<Output = T>
        + Mul<Output = T>
        + Div<Output = T>,
{
    return mod_exp(m, p - T::one() - T::one(), p);
}

// Algorithm 1.3.1 (Euclid GCD)
// TODO: probably don't need the Copy constraint here
fn gcd<T>(a: T, b: T) -> T
where
    T: Zero + Rem<Output = T> + Copy,
{
    if b.is_zero() {
        return a;
    }

    return gcd(b, a % b);
}

fn is_even<T>(x: T) -> bool
where
    T: Zero + One + Rem<Output = T> + PartialEq,
{
    x % (T::one() + T::one()) == T::zero()
}

fn is_odd<T>(x: T) -> bool
where
    T: Zero + One + Rem<Output = T> + PartialEq,
{
    !is_even(x)
}

// Algorithm 1.3.5 (Binary GCD)
fn gcd_binary<T>(a: T, b: T) -> T
where
    T: Zero
        + One
        + Rem<Output = T>
        + PartialEq
        + PartialOrd
        + Div<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Copy,
{
    let two = T::one() + T::one();
    if a < b {
        return gcd_binary(b, a);
    }

    let r = a % b;
    let mut a = b;
    let mut b = r;

    if b == T::zero() {
        return a;
    }

    let mut k = 0;
    while is_even(a) && is_even(b) {
        k += 1;
        a = a / two;
        b = b / two;
    }

    if is_even(a) {
        while is_even(a) {
            a = a / two;
        }
    } else {
        while is_even(b) {
            b = b / two;
        }
    }

    let mut t;
    loop {
        t = (a - b) / two;

        if t == T::zero() {
            // (1 << k) * a
            let mut result = T::one();
            for _ in 0..k {
                result = result * two;
            }
            return result * a;
        }
        while is_even(t) {
            t = t / two;
        }

        if t > T::zero() {
            a = t;
        } else {
            b = T::zero() - t;
        }
    }
}

// Algorithm 1.3.6 (Euclid Extended)
// Given a and b, algorithm determined u, v, d such that a*u + b*v = d
fn gcd_extended<T>(a: T, b: T) -> (T, T, T)
where
    T: Zero + One + Div<Output = T> + Rem<Output = T> + Mul<Output = T> + Sub<Output = T> + Copy,
{
    let mut u = T::one();
    let mut d = a;

    if b.is_zero() {
        return (u, T::zero(), d);
    }

    let mut v1 = T::zero();
    let mut v3 = b;

    loop {
        if v3.is_zero() {
            return (u, (d - a * u) / b, d);
        }

        let q = d / v3;
        let t3 = d % v3;
        let t1 = u - q * v1;

        u = v1;
        d = v3;
        v1 = t1;
        v3 = t3;
    }
}

// 1.3.11 (Chinese Remainder Theorem)
// Given pairwise coprime integers m_i and integers x_i find x such that x \equiv x_i mod m_i
fn chinese_remainder<T>(residues: Vec<(T, T)>) -> T
// TODO: can I alias this type expression somehow?
where
    T: Zero + One + Div<Output = T> + Rem<Output = T> + Mul<Output = T> + Sub<Output = T> + Copy,
{
    let mut residue_iter: std::slice::Iter<'_, (T, T)> = residues.iter();
    let mut m: T = T::zero();
    let mut x: T = T::zero();

    match residue_iter.next() {
        Some((x_, m_)) => {
            m = *m_;
            x = *x_;
        }
        None => (),
    };

    for (xi, mi) in residue_iter {
        let (u, v, _) = gcd_extended(m, *mi);

        x = u * m * *xi + v * *mi * x;
        m = m * *mi;
        x = x % m;
    }

    return x;
}

#[derive(Debug, PartialEq)]
struct Bound<T> {
    lower: Option<T>,
    upper: Option<T>,
}

// 1.3.13 (Lehmer)
fn continued_fraction<T>(lb: (T, T), ub: (T, T)) -> (Vec<T>, Bound<T>)
where
    T: Zero
        + One
        + Div<Output = T>
        + Rem<Output = T>
        + Mul<Output = T>
        + Sub<Output = T>
        + std::cmp::PartialOrd
        + Copy,
{
    let (mut a, mut b) = lb;
    let (mut a_, mut b_) = ub;
    let mut res = Vec::new();

    let mut q_inf = false;
    let mut qup_inf = false;
    let mut q: T;
    let mut q_ = T::zero();

    loop {
        let r = a % b;
        q = a / b;
        let r_ = a_ - b_ * q;
        if r_ < T::zero() || r_ >= b_ {
            // terminate
            q_ = a_ / b_;
            break;
        }

        res.push(q);
        a = b;
        b = r;
        a_ = b_;
        b_ = r_;

        match (b != T::zero(), b_ != T::zero()) {
            (false, false) => {
                // terminate the algo
                break;
            }
            (true, true) => {
                // return to step 2
            }
            (false, true) => {
                // q = infinity
                // q_ = a' / b'
                q_ = a_ / b_;
                q_inf = true;
                break;
            }
            (true, false) => {
                q_ = a / b;
                qup_inf = true;
                break;
            }
        }
    }

    // problem is that the bounds may be infinite; so we have three possibilities
    // to express in our return value:
    // bounded from above
    // bounded from below
    // bounded from both above and below
    match (q_inf, qup_inf) {
        (true, true) => panic!("Impossible"),
        (true, false) => (
            res,
            Bound {
                lower: Some(q_),
                upper: None,
            },
        ),
        (false, true) => (
            res,
            Bound {
                lower: Some(q),
                upper: None,
            },
        ),
        (false, false) => {
            if q < q_ {
                (
                    res,
                    Bound {
                        lower: Some(q),
                        upper: Some(q_),
                    },
                )
            } else {
                (
                    res,
                    Bound {
                        lower: Some(q_),
                        upper: Some(q),
                    },
                )
            }
        }
    }
}

// 1.7. Integer Square Root
fn isqrt<T>(n: T) -> T
where
    T: Zero + One + Div<Output = T> + PartialOrd + Copy,
{
    let mut x = n;
    loop {
        let y = (x + (n / x)) / (T::one() + T::one());
        if y >= x {
            return x;
        }

        x = y;
    }
}

// Algorithm 1.4.10 (Kronecker symbol) pg 29
pub fn kronecker_symbol<T>(a: T, b: T) -> i32
where
    T: Zero + One + Signed + BitAnd<Output = T> + PartialOrd + Copy + Display,
{
    let (zero, one, two, three) = (
        T::zero(),
        T::one(),
        T::one() + T::one(),
        T::one() + T::one() + T::one(),
    );
    let (four, five) = (two + two, three + two);
    let (six, seven) = (three + three, three + four);

    let kronecker_table = |x| {
        if x == zero {
            0
        } else if x == one {
            1
        } else if x == two {
            0
        } else if x == three {
            -1
        } else if x == four {
            0
        } else if x == five {
            -1
        } else if x == six {
            0
        } else if x == seven {
            1
        } else {
            panic!("impossible")
        }
    };

    if b == T::zero() {
        return if a.abs() == T::one() { 1 } else { 0 };
    }

    if is_even(a) && is_even(b) {
        return 0;
    }

    let mut v = T::zero();
    let mut a = a;
    let mut b = b;

    while is_even(b) {
        v = v + T::one();
        b = b / two;
    }

    // a&7 = (-1)^((a^2 - 1)/8)
    let mut k = if is_even(v) {
        1
    } else {
        kronecker_table(a & seven)
    };

    if b < T::zero() {
        b = -b;
        if a < T::zero() {
            k = -k;
        }
    }

    loop {
        assert!(is_odd(b));
        assert!(b > T::zero());

        if a == T::zero() {
            return if b > T::one() {
                0
            } else if b == T::one() {
                k
            } else {
                panic!("Impossible")
            };
        }

        v = T::zero();
        while is_even(a) {
            v = v + one;
            a = a / two;
        }
        if is_odd(v) {
            k = kronecker_table(b & seven) * k;
        }

        // reciprocity
        // (-1)^((a - 1)(b - 1)/4)k
        if (a & b & two) != T::zero() {
            k = -k;
        }

        let r = a.abs();
        a = b % r;
        b = r;
    }
}

// Tonelli/Shanks Algorithm for modular square root
// Adapted from an implementation I did in Python
// Algo 1.5.1
pub fn sqrt_mod_p<T>(a: T, p: T) -> Result<T, String>
where
    T: Zero
        + One
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + Copy
        + Signed
        + PartialOrd
        + BitAnd<Output = T>
        + Shl<Output = T>
        + Display, // remove me
    Standard: Distribution<T>,
{
    let mut rng = thread_rng();

    let two = T::one() + T::one();
    let mut e = T::zero();
    let mut q = p - T::one();

    while is_even(q) {
        e = e + T::one();
        q = q / two;
    }
    assert!(is_odd(q), "Reduced value should have been odd");

    // Step 1 - find generator
    let n: T = loop {
        let n: T = mod_positive(rng.gen(), p);
        if n == T::one() {
            continue;
        }
        if kronecker_symbol(n, p) == -1 {
            break n;
        }
    };

    // Step 2 - initialize
    let mut z = mod_exp(n, q, p);
    let mut y = z;
    let mut r = e;

    let x = mod_exp(a, (q - T::one()) / two, p);
    let mut b = mod_positive(a * x * x, p);
    let mut x = mod_positive(a * x, p);

    loop {
        // Step 3 - find exponent
        if b % p == T::one() {
            break Ok(x);
        }

        // find smallest m such that b^2^m = 1 (p)
        // if m = r output that a is a non-residue
        let mut m = T::one();
        while mod_exp(b, T::one() << m, p) != T::one() {
            m = m + T::one();
        }

        if m == r {
            break Err(format!("Not a quadratic residue mod {}", p));
        }

        // Step 4 - reduce exponent
        let t: T = mod_exp(y, T::one() << (r - m - T::one()), p);
        y = mod_positive((t * t), p);
        r = m;
        x = mod_positive(x * t, p);
        b = mod_positive(b * y, p);
    }
}

// 1.5.2
// Let p be a prime number and d an integer so that 0 < d < p.  This algorithm
// outputs either an integer solution (x, y) so that x^2 + dy^2 = p, or says
// that such a solution does not exist.
pub fn cornacchia_algorithm<T>(d: T, p: T) -> Result<(T, T), String>
where
    T: Zero
        + One
        + Sub<Output = T>
        + Rem<Output = T>
        + Div<Output = T>
        + PartialEq
        + Copy
        + Signed
        + PartialOrd
        + BitAnd<Output = T>
        + Shl<Output = T>
        + Display,
    Standard: Distribution<T>,
{
    let k = kronecker_symbol(-d, p);
    if k == -1 {
        Err("Equation has no solution".to_string())
    } else {
        let mut a = p;
        let mut b = match sqrt_mod_p(-d, p) {
            Err(_) => panic!("did not find square root despite ({}, {}) = {}", -d, p, k),
            Ok(mut x0) => {
                // so now x^0 \equiv -d mod p
                if x0 < T::zero() {
                    x0 = -x0;
                }
                if k == 1 {
                    x0 = x0 + p;
                }
                x0
            }
        };
        let l = isqrt(p);
        b = loop {
            if b <= l {
                break b;
            } else {
                let r = a % b;
                a = b;
                b = r;
            }
        };
        let num = p - b * b;
        if num % d != T::zero() {
            Err("Equation has no solution".to_string())
        } else {
            let c = (p - b * b) / d;
            let sqrt_c = isqrt(c);
            if sqrt_c * sqrt_c != c {
                Err("Equation has no solution".to_string())
            } else {
                Ok((b, sqrt_c))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mod_exp_powers_of_5_mod_7() {
        assert_eq!(1, mod_exp(5, 0, 7));
        assert_eq!(5, mod_exp(5, 1, 7));
        assert_eq!(4, mod_exp(5, 2, 7));
        assert_eq!(6, mod_exp(5, 3, 7));
        assert_eq!(2, mod_exp(5, 4, 7));
        assert_eq!(3, mod_exp(5, 5, 7));
        assert_eq!(1, mod_exp(5, 6, 7));
        assert_eq!(5, mod_exp(5, 7, 7));
    }

    #[test]
    fn test_mod_exp2_powers_of_5_mod_7() {
        assert_eq!(1, mod_exp2(5, 0, 7));
        assert_eq!(5, mod_exp2(5, 1, 7));
        assert_eq!(4, mod_exp2(5, 2, 7));
        assert_eq!(6, mod_exp2(5, 3, 7));
        assert_eq!(2, mod_exp2(5, 4, 7));
        assert_eq!(3, mod_exp2(5, 5, 7));
        assert_eq!(1, mod_exp2(5, 6, 7));
        assert_eq!(5, mod_exp2(5, 7, 7));
    }

    #[test]
    fn test_leftmost_bit() {
        assert_eq!(1, 1 << leftmost_bit(1));
        assert_eq!(2, 1 << leftmost_bit(2));
        assert_eq!(2, 1 << leftmost_bit(3));
        assert_eq!(4, 1 << leftmost_bit(4));
    }

    #[test]
    fn test_mod_inverse_for_7() {
        let a = [2, 3, 5, 7, 13, 19];

        for &p in a.iter() {
            for i in 1..p {
                assert_eq!(1, (mod_inverse(i, p) * i) % p);
            }
        }
    }

    #[test]
    fn test_gcd_simple() {
        assert_eq!(3, gcd(6, 3));
        assert_eq!(2, gcd(6, 4));
        assert_eq!(1, gcd(6, 5));
        assert_eq!(151, gcd(163231, 152057));
    }

    #[test]
    fn test_gcd_binary() {
        assert_eq!(3, gcd_binary(6, 3));
        assert_eq!(2, gcd_binary(6, 4));
        assert_eq!(1, gcd_binary(6, 5));
        assert_eq!(151, gcd_binary(163231, 152057));
    }

    #[test]
    fn test_gcd_extended() {
        let (u, v, d) = gcd_extended(163231, 152057);
        assert_eq!(d, 151);
        assert_eq!(163231 * u + 152057 * v, 151);
    }

    #[test]
    fn test_chinese_remainder() {
        assert_eq!(34, chinese_remainder(vec![(1, 3), (4, 5), (6, 7)]));
        assert_eq!(-26, chinese_remainder(vec![(4, 5), (2, 7)]));
    }

    #[test]
    fn test_isqrt() {
        assert_eq!(3, isqrt(9));
        assert_eq!(3, isqrt(12));
        assert_eq!(4, isqrt(16));
        assert_eq!(5, isqrt(28));
    }

    #[test]
    fn test_kronecker_symbol() {
        assert_eq!(-1, kronecker_symbol(-1, 7));
        assert_eq!(1, kronecker_symbol(-1, 13));
        assert_eq!(-1, kronecker_symbol(2, 3));
        assert_eq!(-1, kronecker_symbol(2, 5));
        assert_eq!(-1, kronecker_symbol(2, 11));
        assert_eq!(-1, kronecker_symbol(2, 13));
        assert_eq!(1, kronecker_symbol(2, 7));
        assert_eq!(1, kronecker_symbol(2, 17));
        assert_eq!(1, kronecker_symbol(2, 23));
        assert_eq!(-1, kronecker_symbol(23, 59));
        assert_eq!(1, kronecker_symbol(43, 97));
        // assert_eq!(1, kronecker_symbol(0, 97));
    }

    #[test]
    fn test_quadratic_residues() {
        // https://doc.sagemath.org/html/en/constructions/number_theory.html#quadratic-residues
        // Not clear why the kronecker symbol algo is returning 0 for (0 / 23).
        assert_eq!(
            vec![1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18],
            (1..23)
                .filter(|x| kronecker_symbol(*x, 23) == 1)
                .collect::<Vec<i32>>()
        );
        assert_eq!(
            vec![5, 7, 10, 11, 14, 15, 17, 19, 20, 21],
            (1..22)
                .filter(|x| kronecker_symbol(*x, 23) == -1)
                .collect::<Vec<i32>>()
        );
    }

    #[test]
    fn test_prime_factors() {
        assert_eq!(prime_factor(25), vec![5, 5]);
        assert_eq!(prime_factor(13), vec![13]);
        assert_eq!(prime_factor(540), vec![2, 2, 3, 3, 3, 5]);
    }

    #[test]
    fn test_real_approx() {
        // https://oeis.org/A001203
        assert_eq!(
            continued_fraction(
                (
                    31415926535897932384626433_i128,
                    10000000000000000000000000_i128
                ),
                (
                    31415926535897932384626434_i128,
                    10000000000000000000000000_i128
                )
            ),
            (
                vec![3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2, 2, 1, 84, 2],
                Bound {
                    lower: Some(1),
                    upper: Some(2)
                }
            )
        );
    }

    #[test]
    fn test_sqrt_mod_p() {
        let res = sqrt_mod_p(4, 7);
        assert!(res == Ok(2) || res == Ok(5));
        let res = sqrt_mod_p(2, 7);
        assert!(res == Ok(3) || res == Ok(4));
        let res: Result<i32, String> = sqrt_mod_p(58, 101);
        assert!(res == Ok(82) || res == Ok(19));
        let res: Result<i32, String> = sqrt_mod_p(-2, 97);
        assert!(res == Ok(17) || res == Ok(80));

        let res = sqrt_mod_p(5, 7);
        assert_eq!(res, Err("Not a quadratic residue mod 7".to_string()));
    }

    #[test]
    fn test_cornacchia() {
        println!("beep");
        assert_eq!(cornacchia_algorithm(2, 97), Ok((5, 6)));
    }
}
