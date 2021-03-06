//! Additional number systems.

use super::diophantine::gcd;
use std::{
    fmt,
    ops::{Add, Div, Mul, Neg, Sub},
};

/// Rational number.
///
/// # Examples
///
/// ```
/// use ps::math::num::Q;
///
/// let three = Q::from(3);
/// let four = Q::from(4);
/// let six = Q::from(6);
///
/// let three_and_half = three + three / six;
/// let minus_three_and_half = six - three_and_half + three / (-three / six);
/// let zero = three_and_half + minus_three_and_half;
///
/// assert!(three_and_half > three);
/// assert!(three_and_half < four);
/// assert_eq!(three_and_half, -minus_three_and_half);
///
/// # assert_eq!(three_and_half.num, 7);
/// # assert_eq!(three_and_half.den, 2);
/// # assert_eq!(three_and_half, Q::new(-35, -10).unwrap());
/// # assert_eq!(minus_three_and_half.num, -7);
/// # assert_eq!(minus_three_and_half.den, 2);
/// # assert_eq!(zero.num, 0);
/// # assert_eq!(zero.den, 1);
/// ```
#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
pub struct Q {
    /// Numerator.
    pub num: i64,
    /// Denominator; should be positive.
    pub den: i64,
}
impl Q {
    /// Creates a new rational number if `dem != 0`, or gives `None` otherwise.
    ///
    /// # Arguments
    ///
    /// * `num`, `den` - Numerator and denominator.
    pub fn new(num: i64, den: i64) -> Option<Self> {
        if den == 0 {
            None
        } else {
            let g = gcd(num.abs() as u64, den.abs() as u64) as i64 * den.signum();
            Some(Self {
                num: num / g,
                den: den / g,
            })
        }
    }
    /// Computes the absolute value.
    pub fn abs(self) -> Self {
        Self {
            num: self.num.abs(),
            den: self.den,
        }
    }
    /// Takes the reciprocal (inverse) of a number.
    pub fn recip(self) -> Self {
        let g = self.num.signum();
        Self {
            num: self.den / g,
            den: self.num / g,
        }
    }
}
impl fmt::Display for Q {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.num, self.den)
    }
}
impl From<i64> for Q {
    fn from(num: i64) -> Self {
        Self { num, den: 1 }
    }
}
impl Neg for Q {
    type Output = Self;
    fn neg(self) -> Self {
        Self {
            num: -self.num,
            den: self.den,
        }
    }
}
#[allow(clippy::suspicious_arithmetic_impl)]
impl Add for Q {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self::new(self.num * other.den + self.den * other.num, self.den * other.den).unwrap()
    }
}
#[allow(clippy::suspicious_arithmetic_impl)]
impl Sub for Q {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self::new(self.num * other.den - self.den * other.num, self.den * other.den).unwrap()
    }
}
impl Mul for Q {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Self::new(self.num * other.num, self.den * other.den).unwrap()
    }
}
#[allow(clippy::suspicious_arithmetic_impl)]
impl Div for Q {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        self * other.recip()
    }
}
impl Ord for Q {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.num * other.den).cmp(&(self.den * other.num))
    }
}
impl PartialOrd for Q {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Complex number.
///
/// # Examples
///
/// ```
/// use std::f64::consts::PI;
/// use ps::math::num::C;
///
/// let four = C::from(4.0);
/// let two_i = C::new(0.0, 2.0);
///
/// assert_eq!(four / two_i, -two_i);
/// assert_eq!(two_i * -two_i, four);
/// assert_eq!(two_i - two_i, C::from(0.0));
///
/// # assert_eq!(four.abs(), 4.0);
/// # assert_eq!(two_i.abs(), 2.0);
///
/// # assert_eq!((-four).arg(), -PI);
/// # assert_eq!((-two_i).arg(), -PI / 2.0);
/// # assert_eq!(four.arg(), 0.0);
/// # assert_eq!(two_i.arg(), PI / 2.0);
/// ```
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct C {
    /// Real part.
    pub re: f64,
    /// Imaginary part.
    pub im: f64,
}
impl C {
    fn abssq(self) -> f64 {
        self.re * self.re + self.im * self.im
    }
    /// Creates a new complex number.
    ///
    /// # Arguments
    ///
    /// * `re`, `im` - Real and imaginary parts.
    pub fn new(re: f64, im: f64) -> Self {
        Self { re, im }
    }
    /// Creates a complex number from polar coordinate.
    ///
    /// # Arguments
    ///
    /// * `abs` - Absolute value.
    /// * `arg` - The angle between the number and the positive x axis.
    pub fn from_polar(abs: f64, arg: f64) -> Self {
        Self::new(abs * arg.cos(), abs * arg.sin())
    }
    /// Computes the absolute value.
    pub fn abs(self) -> f64 {
        self.abssq().sqrt()
    }
    /// Computes the angle between the number and the positive x axis.
    pub fn arg(self) -> f64 {
        self.im.atan2(self.re)
    }
    /// Takes the reciprocal (inverse) of a number.
    pub fn recip(self) -> Self {
        let denom = self.abssq();
        Self::new(self.re / denom, -self.im / denom)
    }
    /// Takes the conjugate of a number.
    pub fn conj(self) -> Self {
        Self::new(self.re, -self.im)
    }
}
impl From<f64> for C {
    fn from(re: f64) -> Self {
        Self::new(re, 0.0)
    }
}
impl Neg for C {
    type Output = Self;
    fn neg(self) -> Self {
        Self::new(-self.re, -self.im)
    }
}
impl Add for C {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self::new(self.re + other.re, self.im + other.im)
    }
}
impl Sub for C {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self::new(self.re - other.re, self.im - other.im)
    }
}
impl Mul for C {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        let re = self.re * other.re - self.im * other.im;
        let im = self.im * other.re + self.re * other.im;
        Self::new(re, im)
    }
}
#[allow(clippy::suspicious_arithmetic_impl)]
impl Div for C {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        self * other.recip()
    }
}
