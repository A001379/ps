//! Additional number systems.

use super::diophantine::gcd;
use std::{
    cmp::Ordering,
    fmt,
    ops::{Add, AddAssign, Div, Mul, Neg, Sub, SubAssign},
};

const DIV: u64 = 1_000_000_000_000_000;

/// Big integer.
///
/// # Examples
///
/// ```
/// use ps::math::num::Z;
///
/// let a = Z::parse("100000000000000000000000000000000");
/// let b = Z::from(1);
/// let c = Z::parse("100000000000000000000000000000001");
/// let d = Z::parse("99999999999999999999999999999999");
/// assert_eq!(a - d, b);
/// ```
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub struct Z {
    mem: Vec<u64>,
    sign: bool,
}
impl Z {
    pub fn parse(value: &str) -> Self {
        let sign = value.starts_with('-');
        let mem = value[(sign as usize)..]
            .as_bytes()
            .rchunks(15)
            .map(|chunk| std::str::from_utf8(chunk).unwrap().parse::<u64>().unwrap())
            .collect::<Vec<_>>();
        Self { mem, sign }
    }
    pub fn abs(self) -> Self {
        Self {
            mem: self.mem,
            sign: false,
        }
    }
}
impl fmt::Display for Z {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.sign {
            write!(f, "-")?
        }
        for (i, n) in self.mem.iter().rev().enumerate() {
            if i == 0 {
                write!(f, "{}", n)?
            } else {
                write!(f, "{:0>15}", n)?
            }
        }
        Ok(())
    }
}
impl From<u64> for Z {
    fn from(value: u64) -> Self {
        let mut mem = vec![value % DIV];
        if value >= DIV {
            mem.push(value / DIV);
        }
        Self { mem, sign: false }
    }
}
impl From<i64> for Z {
    fn from(value: i64) -> Self {
        let sign = value < 0;
        let value = value.abs() as u64;
        let mut mem = vec![value % DIV];
        if value >= DIV {
            mem.push(value / DIV);
        }
        Self { mem, sign }
    }
}
impl From<u32> for Z {
    fn from(value: u32) -> Self {
        Self::from(value as u64)
    }
}
impl From<i32> for Z {
    fn from(value: i32) -> Self {
        Self::from(value as i64)
    }
}
fn cmp_mem(lhs: &[u64], rhs: &[u64]) -> Ordering {
    let result = lhs.len().cmp(&rhs.len());
    if result != Ordering::Equal {
        return result;
    }
    for (l, r) in lhs.iter().rev().zip(rhs.iter().rev()) {
        let result = l.cmp(r);
        if result != Ordering::Equal {
            return result;
        }
    }
    Ordering::Equal
}
impl Ord for Z {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.sign {
            if other.sign {
                cmp_mem(&other.mem, &self.mem)
            } else {
                Ordering::Less
            }
        } else if other.sign {
            Ordering::Greater
        } else {
            cmp_mem(&self.mem, &other.mem)
        }
    }
}
impl PartialOrd for Z {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Neg for Z {
    type Output = Self;
    fn neg(self) -> Self {
        let sign = if self.mem == vec![0] { false } else { !self.sign };
        Self { mem: self.mem, sign }
    }
}

fn add_to_mem(this: &mut Vec<u64>, other: &[u64]) {
    let mut carry = 0;
    for (idx, rhs) in other.iter().enumerate() {
        if idx >= this.len() {
            this.push(0);
        }
        this[idx] += carry + rhs;
        carry = this[idx] / DIV;
        this[idx] %= DIV;
    }
    if carry > 0 {
        this.push(carry);
    }
}
impl AddAssign for Z {
    fn add_assign(&mut self, other: Self) {
        if self.sign != other.sign {
            self.sub_assign(other.neg());
        } else {
            add_to_mem(&mut self.mem, &other.mem);
        }
    }
}
impl Add for Z {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let mut result = self;
        result.add_assign(other);
        result
    }
}

fn sub_to_mem(this: &mut Vec<u64>, other: &[u64]) {
    let mut other = other.iter();
    let mut idx = 0;
    let mut carry = 0;
    loop {
        let peek = other.next();
        if carry == 0 && peek == None {
            break;
        }
        let rhs = peek.cloned().unwrap_or(0);
        if this[idx] >= rhs + carry {
            this[idx] -= rhs + carry;
            carry = 0;
        } else {
            this[idx] += DIV - rhs - carry;
            carry = 1;
        }
        idx += 1;
    }
    idx = this.len();
    while idx > 0 {
        idx -= 1;
        if this[idx] > 0 {
            break;
        }
    }
    this.resize(idx + 1, 0);
}
impl SubAssign for Z {
    fn sub_assign(&mut self, other: Self) {
        if self.sign != other.sign {
            self.add_assign(other.neg());
        } else {
            match cmp_mem(&self.mem, &other.mem) {
                Ordering::Equal => {
                    self.mem = vec![0];
                    self.sign = false;
                }
                Ordering::Less => {
                    let mut mem = other.mem.clone();
                    sub_to_mem(&mut mem, &self.mem);
                    self.mem = mem;
                    self.sign = true;
                }
                Ordering::Greater => {
                    sub_to_mem(&mut self.mem, &other.mem);
                    self.sign = false;
                }
            }
        }
    }
}
impl Sub for Z {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        let mut result = self;
        result.sub_assign(other);
        result
    }
}

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
impl fmt::Display for C {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}{}i", self.re, if self.im < 0.0 { "" } else { "+" }, self.im)
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
