extern crate num;

use self::num::{One, Zero};
use std::ops::{Add, Mul};
use std::vec;

struct Poly<T, const CHAR: u16> {
    coeffs: Vec<T>,
}

impl<T, const CHAR: u16> Zero for Poly<T, CHAR>
where
    T: Zero,
{
    fn zero() -> Self {
        return Poly {
            coeffs: vec![T::zero()],
        };
    }

    fn is_zero(&self) -> bool {
        return self.coeffs.len() == 0;
    }
}

impl<T, const CHAR: u16> Add for Poly<T, CHAR> {
    type Output = Poly<T, CHAR>;

    fn add(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<T, const CHAR: u16> Mul for Poly<T, CHAR> {
    type Output = Poly<T, CHAR>;

    fn mul(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<T, const CHAR: u16> One for Poly<T, CHAR>
where
    T: One,
{
    fn one() -> Self {
        return Poly {
            coeffs: vec![T::one()],
        };
    }
}
