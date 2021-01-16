//! Modular arithmetic systems.

use std::{
    fmt,
    marker::PhantomData,
    ops::{Add, Div, Mul, Neg, Sub},
};

/// Ring of integers modulo _p_ where _p_ is a prime number.
#[derive(Clone, Copy, Eq, PartialEq, Debug, Hash)]
pub struct Quotient<P> {
    pub value: u64,
    phantom: PhantomData<fn() -> P>,
}
impl<P: Modulo> Quotient<P> {
    fn raw(value: u64) -> Self {
        Self {
            value,
            phantom: PhantomData,
        }
    }

    /// Computes `self^exp`.
    pub fn pow(mut self, mut exp: u64) -> Self {
        let mut result = Self::raw(1);
        while exp > 0 {
            if exp % 2 == 1 {
                result = result * self;
            }
            self = self * self;
            exp /= 2;
        }
        result
    }
    /// Computes `self^-1`
    pub fn recip(self) -> Self {
        self.pow(P::VALUE - 2)
    }
    /// Generates reciprocals, starts from 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use ps::math::modular::{Quotient, Mod998244353};
    ///
    /// let invs: Vec<_> = Quotient::<Mod998244353>::recip_iter().take(20).collect();
    /// for i in 0..invs.len() {
    ///     assert_eq!(invs[i], Quotient::<Mod998244353>::from(1 + i as u64).recip());
    /// }
    /// ```
    pub fn recip_iter() -> impl Iterator<Item = Self> {
        let cache = vec![Self::raw(0), Self::raw(1)];
        cache.clone().into_iter().skip(1).chain(Reciprocal::<P> { cache })
    }
}
struct Reciprocal<P> {
    cache: Vec<Quotient<P>>,
}
impl<P: Modulo> Iterator for Reciprocal<P> {
    type Item = Quotient<P>;
    fn next(&mut self) -> Option<Self::Item> {
        let l = self.cache.len() as u64;
        if l >= P::VALUE {
            None
        } else {
            let (idx, value) = (P::VALUE % l, P::VALUE - P::VALUE / l);
            let inv = self.cache[idx as usize] * Self::Item::raw(value);
            self.cache.push(inv);
            Some(inv)
        }
    }
}
impl<P: Modulo> fmt::Display for Quotient<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} mod {}", self.value, P::VALUE)
    }
}
impl<P: Modulo> From<u64> for Quotient<P> {
    fn from(value: u64) -> Self {
        Self::raw(value.rem_euclid(P::VALUE))
    }
}
impl<P: Modulo> From<i64> for Quotient<P> {
    fn from(value: i64) -> Self {
        Self::raw((value as i128).rem_euclid(P::VALUE as i128) as _)
    }
}
impl<P: Modulo> From<u32> for Quotient<P> {
    fn from(value: u32) -> Self {
        Self::from(value as u64)
    }
}
impl<P: Modulo> From<i32> for Quotient<P> {
    fn from(value: i32) -> Self {
        Self::from(value as i64)
    }
}
impl<P: Modulo> Neg for Quotient<P> {
    type Output = Self;
    fn neg(self) -> Self {
        Self::raw(if self.value == 0 { 0 } else { P::VALUE - self.value })
    }
}
impl<P: Modulo> Add for Quotient<P> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let value = self.value + other.value;
        Self::raw(value - if value >= P::VALUE { P::VALUE } else { 0 })
    }
}
impl<P: Modulo> Sub for Quotient<P> {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        self.add(other.neg())
    }
}
impl<P: Modulo> Mul for Quotient<P> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Self::from(self.value * other.value)
    }
}
#[allow(clippy::suspicious_arithmetic_impl)]
impl<P: Modulo> Div for Quotient<P> {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        self * other.recip()
    }
}

/// Modulus trait used for [Quotient<P>].
///
/// Since const generics are unstable in Rust yet, we implement this special trait.
///
/// # Examples
///
/// To create custom modulus,
///
/// ```
/// use ps::math::modular::Modulo;
///
/// #[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
/// pub struct Mod29;
/// impl Modulo for Mod29 {
///     const VALUE: u64 = 29;
/// }
/// ```
pub trait Modulo: 'static + Copy + Eq {
    const VALUE: u64;
}
/// Special modulus value 998244353 = 2^23 * 7 * 17 + 1.
///
/// # Examples
///
/// ```
/// use ps::math::modular::{Quotient, Mod998244353};
/// let root1 = Quotient::<Mod998244353>::from(15_311_432);
/// let root2 = Quotient::<Mod998244353>::from(469_870_224);
///
/// assert_eq!(root1.recip(), root2);
/// assert_eq!(root2.recip(), root1);
/// assert_eq!((root1 * root2).value, 1);
/// ```
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum Mod998244353 {}
impl Modulo for Mod998244353 {
    const VALUE: u64 = 998_244_353;
}
/// Special modulus value 1000000007 = 10^9 + 7.
///
/// # Examples
///
/// ```
/// use ps::math::modular::{Quotient, Mod1000000007};
/// let onetwothree = Quotient::<Mod1000000007>::from(123);
/// let two = Quotient::<Mod1000000007>::from(2);
///
/// let zero = two - two;
/// assert_eq!(zero.value, 0);
///
/// let one = two / two;
/// assert_eq!(one.value, 1);
///
/// assert_eq!(one + one, two);
/// assert_eq!(one / onetwothree * (onetwothree * onetwothree) - onetwothree / one, zero);
/// ```
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub enum Mod1000000007 {}
impl Modulo for Mod1000000007 {
    const VALUE: u64 = 1_000_000_007;
}

/// Computes `a^b mod p`.
///
/// # Arguments
///
/// - `p`: a prime number used as modulus.
///
/// # Examples
///
/// ```
/// use ps::math::modular::pow_mod;
/// assert_eq!(pow_mod(356, 1234, 19), 5);
/// ```
pub fn pow_mod(mut a: u64, mut b: u64, p: u64) -> u64 {
    let mut result = 1;
    a %= p;
    while b > 0 {
        if b % 2 == 1 {
            result = mul_mod(result, a, p);
        }
        a = mul_mod(a, a, p);
        b /= 2;
    }
    result % p
}
/// Computes `a^-1 mod p`.
///
/// # Arguments
///
/// - `p`: a prime number used as modulus.
///
/// # Examples
///
/// ```
/// use ps::math::modular::recip_mod;
/// assert_eq!(recip_mod(356, 19), 15);
/// ```
pub fn recip_mod(a: u64, p: u64) -> u64 {
    pow_mod(a, p - 2, p)
}
/// Computes `-a mod p`.
///
/// # Arguments
///
/// - `p`: a prime number used as modulus.
///
/// # Examples
///
/// ```
/// use ps::math::modular::neg_mod;
/// assert_eq!(neg_mod(356, 19), 5);
/// ```
pub fn neg_mod(x: u64, p: u64) -> u64 {
    let tmp = x % p;
    if tmp == 0 {
        0
    } else {
        p - tmp
    }
}
/// Computes `a+b mod p`.
///
/// # Arguments
///
/// - `p`: a prime number used as modulus.
///
/// # Examples
///
/// ```
/// use ps::math::modular::add_mod;
/// assert_eq!(add_mod(356, 1234, 19), 13);
/// ```
pub fn add_mod(x: u64, y: u64, p: u64) -> u64 {
    ((x % p) + (y % p)) % p
}
/// Computes `a-b mod p`.
///
/// # Arguments
///
/// - `p`: a prime number used as modulus.
///
/// # Examples
///
/// ```
/// use ps::math::modular::sub_mod;
/// assert_eq!(sub_mod(356, 1234, 19), 15);
/// ```
pub fn sub_mod(x: u64, y: u64, p: u64) -> u64 {
    add_mod(x, neg_mod(y, p), p)
}
/// Computes `a*b mod p`.
///
/// # Arguments
///
/// - `p`: a prime number used as modulus.
///
/// # Examples
///
/// ```
/// use ps::math::modular::mul_mod;
/// assert_eq!(mul_mod(356, 1234, 19), 5);
/// ```
pub fn mul_mod(x: u64, y: u64, p: u64) -> u64 {
    (x as u128 * y as u128 % p as u128) as _
}
/// Find `x` such that `a = b*x mod p`.
///
/// # Arguments
///
/// - `p`: a prime number used as modulus.
///
/// # Examples
///
/// ```
/// use ps::math::modular::div_mod;
/// assert_eq!(div_mod(356, 1234, 19), 5);
/// ```
pub fn div_mod(x: u64, y: u64, p: u64) -> u64 {
    mul_mod(x, recip_mod(y, p), p)
}
