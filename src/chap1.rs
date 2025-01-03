extern crate num;

use self::num::One;
use self::num::Signed;
use self::num::Zero;
use std::cmp::PartialOrd;
use std::ops::BitAnd;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
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
fn mod_exp(g: i32, n: i32, p: i32) -> i32 {
    let mut y = 1;
    let mut z;
    let mut exp;
    if n == 0 {
        return y;
    } else if n < 0 {
        exp = -n;
        z = mod_inverse(g, p);
    } else {
        exp = n;
        z = g;
    }

    while exp > 0 {
        if exp % 2 == 1 {
            y = (y * z) % p;
        }
        z = (z * z) % p;
        exp = exp / 2;
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

fn mod_inverse(m: i32, p: i32) -> i32 {
    return mod_exp(m, p - 2, p);
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

// Algorithm 1.3.5 (Binary GCD)
// TODO: switch to use generics (sort of annoying because it uses even/odd a bunch)
fn gcd_binary(a: i32, b: i32) -> i32 {
    if a < b {
        return gcd_binary(b, a);
    }

    let r = a % b;
    let mut a = b;
    let mut b = r;

    if b == 0 {
        return a;
    }

    let mut k = 0;
    while a % 2 == 0 && b % 2 == 0 {
        k += 1;
        a = a >> 1;
        b = b >> 1;
    }

    if a % 2 == 0 {
        while a % 2 == 0 {
            a = a >> 1;
        }
    } else {
        while b % 2 == 0 {
            b = b >> 1;
        }
    }

    let mut t;
    loop {
        t = (a - b) >> 1;

        if t == 0 {
            return (1 << k) * a;
        }
        while t % 2 == 0 {
            t = t >> 1;
        }

        if t > 0 {
            a = t;
        } else {
            b = -t;
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
    let mut i = 0;
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
        let mut r_ = a_ - b_ * q;
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
fn isqrt(n: i32) -> i32 {
    let mut x = n;
    loop {
        let y = (x + (n / x)) >> 1;
        if y >= x {
            return x;
        }

        x = y;
    }
}

fn is_even<T>(x: T) -> bool
where
    T: Zero + One + Rem<Output = T> + PartialEq,
{
    x % (T::one() + T::one()) == T::zero()
}

// Algorithm 1.4.10 (Kronecker symbol) pg 29
fn kroneker_symbol<T>(a: T, b: T) -> i32
where
    T: Zero + One + Signed + BitAnd<Output = T> + PartialOrd + Copy,
{
    let (zero, one, two, three) = (
        T::zero(),
        T::one(),
        T::one() + T::one(),
        T::one() + T::one() + T::one(),
    );
    let (four, five, six, seven) = (two + two, three + two, three + three, three + three + one);

    let kroneker_table = |x| {
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
    let mut k = if v % two == T::zero() {
        1
    } else {
        kroneker_table(a & seven)
    };

    if b < T::zero() {
        b = -b;
        if a < T::zero() {
            k = -k;
        }
    }

    loop {
        assert!(b % two != T::zero());
        assert!(b > T::zero());

        if a == T::zero() {
            return if b > T::one() { 0 } else { k };
        }

        v = T::zero();
        while is_even(a) {
            v = v + one;
            a = a / two;
        }
        if !is_even(v) {
            k = kroneker_table(b & seven);
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
        assert_eq!(-1, kroneker_symbol(-1, 7));
        assert_eq!(1, kroneker_symbol(-1, 13));
        assert_eq!(-1, kroneker_symbol(2, 3));
        assert_eq!(-1, kroneker_symbol(2, 5));
        assert_eq!(-1, kroneker_symbol(2, 11));
        assert_eq!(-1, kroneker_symbol(2, 13));
        assert_eq!(1, kroneker_symbol(2, 7));
        assert_eq!(1, kroneker_symbol(2, 17));
        assert_eq!(1, kroneker_symbol(2, 23));
        assert_eq!(-1, kroneker_symbol(23, 59));
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
}
