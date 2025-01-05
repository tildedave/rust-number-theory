extern crate num;

use crate::chap1::mod_inverse;

use self::num::Zero;
use crate::chap1::mod_exp;
use std::cmp::PartialEq;
use std::ops::{Add, Mul, Rem, Sub};

// finite field elements have both characteristic (char) and size of field (e.g. 2^256)
// assumption is that CHAR is prime; we won't be checking this.
// u32 is I guess fine
// For GF(2^n ) there are more efficient algorithms but we should implement those separately.
#[derive(Debug, PartialEq, Clone, Copy)]
struct FieldElement<const CHAR: u32, const EXP: usize> {
    num: [u32; EXP],
}

impl<const CHAR: u32, const EXP: usize> FieldElement<CHAR, EXP> {
    pub fn from_int(i: u32) -> FieldElement<CHAR, EXP> {
        let mut num = [0; EXP];
        num[0] = i;
        FieldElement::<CHAR, EXP> { num: num }
    }

    pub fn degree(&self) -> usize {
        // this is the highest element (starting from EXP - 1) that is non-zero
        let mut result = 0;
        for i in (0..EXP).rev() {
            if self.num[i] != 0 {
                result = i;
                break;
            }
        }
        result
    }

    pub fn divmod(&self, d: &Self) -> (Self, Self) {
        // the approach I implemented in golang is "synthetic division" which
        // requires computing modular inverses of the coefficients and
        // relatively smart division.
        // https://en.wikipedia.org/wiki/Polynomial_long_division
        assert!(!d.is_zero(), "Division by zero");

        let mut q = FieldElement::zero();
        let mut r: FieldElement<CHAR, EXP> = *self;
        let mut r_degree = r.degree();
        let d_degree = d.degree();
        let d_leading = d.num[d_degree];
        let d_inv = mod_inverse(d_leading, CHAR);

        while !r.is_zero() && r_degree >= d.degree() {
            // t is a x^3 or whatever.
            // it has degree equal to r_degree - d_degree
            let t = r.num[r_degree] * d_inv;
            let mut t_poly = Self::zero();
            t_poly.num[r_degree - d_degree] = t;

            q = q + t_poly;
            r = r - t_poly * *d;
            r_degree = r.degree();
        }
        (q, r)
    }
}

impl<const CHAR: u32, const EXP: usize> Zero for FieldElement<CHAR, EXP> {
    fn zero() -> Self {
        FieldElement::<CHAR, EXP> { num: [0; EXP] }
    }

    fn is_zero(&self) -> bool {
        *self == FieldElement::<CHAR, EXP>::zero()
    }
}

impl<const CHAR: u32, const EXP: usize> Add for FieldElement<CHAR, EXP> {
    type Output = FieldElement<CHAR, EXP>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result = [0; EXP];
        for (i, (a, b)) in self.num.iter().zip(rhs.num.iter()).enumerate() {
            result[i] = (a + b) % CHAR;
        }
        Self::Output { num: result }
    }
}

impl<const CHAR: u32, const EXP: usize> Mul for FieldElement<CHAR, EXP> {
    type Output = FieldElement<CHAR, EXP>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = [0; EXP];
        // (a p^0 + b p + ... + c p^{n-1})(a' p^0 + b' p + ... + c' p^{n-1}) =
        // combine i/j from both, add.
        // this isn't particularly efficient; I guess we need to look at all
        // these though.
        for (i, &a) in self.num.iter().enumerate() {
            for (j, &b) in rhs.num.iter().enumerate() {
                result[((i + j) % EXP) as usize] += (a * b) % CHAR;
            }
        }

        Self::Output { num: result }
    }
}

impl<const CHAR: u32, const EXP: usize> Sub for FieldElement<CHAR, EXP> {
    type Output = FieldElement<CHAR, EXP>;

    fn sub(self, rhs: Self) -> Self::Output {
        // same as add but in reverse.
        let mut result = [0; EXP];
        let mut result = [0; EXP];
        for (i, (a, b)) in self.num.iter().zip(rhs.num.iter()).enumerate() {
            result[i] = if b > a { CHAR - (b - a) } else { a - b };
        }
        Self::Output { num: result }
    }
}

#[derive(Debug, PartialEq)]
struct GF2nElem<const EXP: u32> {
    num: u128,
}

impl<const EXP: u32> Zero for GF2nElem<EXP> {
    fn zero() -> Self {
        GF2nElem { num: 0 }
    }

    fn is_zero(&self) -> bool {
        return self.num == 0;
    }
}

impl<const EXP: u32> Add for GF2nElem<EXP> {
    type Output = GF2nElem<EXP>;

    fn add(self, rhs: Self) -> Self::Output {
        Self::Output {
            num: self.num ^ rhs.num,
        }
    }
}

impl<const EXP: u32> Sub for GF2nElem<EXP> {
    type Output = GF2nElem<EXP>;

    fn sub(self, rhs: Self) -> Self::Output {
        // addition = subtraction
        return self + rhs;
    }
}

impl<const EXP: u32> Mul for GF2nElem<EXP> {
    type Output = GF2nElem<EXP>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut a = self.num;
        let mut b = rhs.num;
        let mut p = 0;

        while a > 0 {
            if (a & 1) == 1 {
                p = p ^ b
            }
            a = a >> 1;
            b = b << 1;
        }

        Self::Output { num: p }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basics() {
        type F7 = FieldElement<7, 1>;

        let e = F7 { num: [5; 1] };
        assert!(!e.is_zero());
        assert_eq!(e, F7::from_int(5));
    }

    #[test]
    fn test_divmod() {
        // tests from my finite field golang project
        type F5 = FieldElement<5, 5>;

        let (q, r) = F5 {
            num: [1, 4, 6, 4, 1],
        }
        .divmod(&F5 {
            num: [1, 2, 1, 0, 0],
        });
        assert_eq!(
            q,
            F5 {
                num: [1, 2, 1, 0, 0]
            }
        );
        assert!(r.is_zero());
    }

    #[test]
    fn test_gf2() {
        // copied from my cryptopals examples
        type GF2_128 = GF2nElem<128>;

        assert_eq!(GF2_128 { num: 7 } * GF2_128 { num: 3 }, GF2_128 { num: 9 });
        // unclear why 0x87 is the answer for my Python code, a^125 * a^3 = a^128 = 0
        assert_eq!(
            GF2_128 { num: 1 << 125 } * GF2_128 { num: 1 << 3 },
            GF2_128 { num: 0 }
        );
    }
}
