extern crate num;

use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
use std::ops::Shr;
use std::ops::Sub;
use self::num::Zero;
use self::num::One;

fn leftmost_bit<T>(g: T) -> T
where T: Shr<Output=T> + PartialEq + Zero + One
{
    let mut n = T::zero();
    let mut r = g;

    while r != T::zero() {
        r = r >> T::one();
        if r != T::zero() {
            n = n + T::one();
        }
    }
    return n
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
        if exp&(1 << f) != 0 {
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
where T: Zero + Rem<Output=T> + Copy
{
    if b.is_zero() {
        return a
    }

    return gcd(b, a % b)
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
where T: Zero + One + Div<Output=T> + Rem<Output=T> + Mul<Output=T> + Sub<Output=T> + Copy
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
fn chinese_remainder_theorem<T>(m_list: Vec<T>, xi_list: Vec<T>) -> T
// TODO: can I alias this type expression somehow?
where T : Zero + One + Div<Output=T> + Rem<Output=T> + Mul<Output=T> + Sub<Output=T> + Copy {
    assert!(m_list.len() == xi_list.len());
    unsafe {
        let k = m_list.len();

        let mut i = 0;
        let mut m = *m_list.get_unchecked(0);
        let mut x = *xi_list.get_unchecked(0);

        while i < k - 1 {
            i = i + 1;

            let mi = *m_list.get_unchecked(i);
            let xi = *xi_list.get_unchecked(i);
            let (u, v, _) = gcd_extended(m, mi);

            x = u * m * xi + v * mi * x;
            m = m * mi;
            x = x % m;
        }

        return x;
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
    fn test_chinese_remainder_theorem() {
        assert_eq!(34, chinese_remainder_theorem( vec![3, 5, 7], vec![1, 4, 6]));
        assert_eq!(-26, chinese_remainder_theorem( vec![5, 7], vec![4, 2]));
    }
}
