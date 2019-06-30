extern crate num;

use std::ops::Rem;
use std::ops::Shr;
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
    }
}
