extern crate num;

use crate::chap1::isqrt;

use self::num::{One, Signed, Zero};
use std::ops::{Rem, Shr, Sub};

pub fn mod_positive<T>(n: T, a: T) -> T
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

pub fn leftmost_bit<T>(g: T) -> T
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
pub fn prime_factor(n: i32) -> Vec<i32> {
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

#[cfg(test)]
mod tests {
    use super::prime_factor;

    #[test]
    fn test_prime_factors() {
        assert_eq!(prime_factor(25), vec![5, 5]);
        assert_eq!(prime_factor(13), vec![13]);
        assert_eq!(prime_factor(540), vec![2, 2, 3, 3, 3, 5]);
    }
}
