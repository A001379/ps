//! Various algorithms for Diophantine equations.

/// Computes greatest common divisor.
///
/// # Examples
///
/// ```
/// use ps::math::diophantine::gcd;
///
/// assert_eq!(gcd(12, 18), 6);
/// assert_eq!(gcd(1, 18), 1);
/// assert_eq!(gcd(0, 12), 12);
/// assert_eq!(gcd(0, 0), 0);
/// ```
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        a %= b;
        std::mem::swap(&mut a, &mut b);
    }
    a
}
