//! Convolution operator based on discrete Fourier transform.
use super::modular::{Mod998244353, Quotient};
use super::num::C;
use std::f64::consts::PI;

/// Computes convolution of two vectors.
///
/// Uses complex FFT if input type is f64, or modular NTT if input type is u64.
///
/// # Examples
///
/// Convolution on complex numbers:
/// ```
/// use ps::math::fourier::conv;
/// assert_eq!(conv(&vec![7.0, 1.0, 1.0], &vec![2.0, 4.0]), vec![14.0, 30.0, 6.0, 4.0]);
/// assert_eq!(conv(&vec![999.0], &vec![1e6]), vec![999e6]);
/// ```
///
/// Convolution on finite modular field:
/// ```
/// use ps::math::fourier::conv;
/// assert_eq!(conv(&vec![7, 1, 1], &vec![2, 4]), vec![14, 30, 6, 4]);
/// assert_eq!(conv(&vec![999], &vec![1_000_000]), vec![999_000_000 % 998_244_353]);
/// ```
pub fn conv<T: internal::FFT>(a: &[T], b: &[T]) -> Vec<T> {
    let l = a.len() + b.len() - 1;
    let a_on_freq = dft(a, l);
    let b_on_freq = dft(b, l);
    let ab_on_freq = a_on_freq
        .into_iter()
        .zip(b_on_freq.into_iter())
        .map(|(a, b)| a * b)
        .collect::<Vec<_>>();
    idft(&ab_on_freq, l)
}

mod internal {
    use std::ops::{Add, Div, Mul, Neg, Sub};
    pub trait FFT: Sized + Copy {
        type F: Sized
            + Copy
            + From<Self>
            + Neg
            + Add<Output = Self::F>
            + Div<Output = Self::F>
            + Mul<Output = Self::F>
            + Sub<Output = Self::F>;

        const ZERO: Self;

        /// A primitive nth root of one raised to the powers 0, 1, 2, ..., n/2 - 1
        fn get_roots(n: usize, inverse: bool) -> Vec<Self::F>;
        /// 1 for forward transform, 1/n for inverse transform
        fn get_factor(n: usize, inverse: bool) -> Self::F;
        /// The inverse of Self::F::from()
        fn extract(f: Self::F) -> Self;
    }
}
impl internal::FFT for f64 {
    type F = C;
    const ZERO: f64 = 0.0;
    fn get_roots(n: usize, inverse: bool) -> Vec<Self::F> {
        let step = if inverse { -2.0 } else { 2.0 } * PI / n as f64;
        (0..n / 2).map(|i| C::from_polar(1.0, step * i as f64)).collect()
    }
    fn get_factor(n: usize, inverse: bool) -> Self::F {
        Self::F::from(if inverse { n as f64 } else { 1.0 }).recip()
    }
    fn extract(f: Self::F) -> f64 {
        f.re
    }
}
impl internal::FFT for u64 {
    type F = Quotient<Mod998244353>;
    const ZERO: Self = 0;
    fn get_roots(n: usize, inverse: bool) -> Vec<Self::F> {
        assert!(n <= 1 << 23);
        // 15311432 and 469870224 are inverses and 2^23rd roots of 1
        let mut prim_root = Self::F::from(if inverse { 469_870_224 } else { 15_311_432 });
        for _ in (0..).take_while(|&i| n < 1 << (23 - i)) {
            prim_root = prim_root * prim_root;
        }
        let mut roots = Vec::with_capacity(n / 2);
        let mut root = Self::F::from(1);
        for _ in 0..roots.capacity() {
            roots.push(root);
            root = root * prim_root;
        }
        roots
    }
    fn get_factor(n: usize, inverse: bool) -> Self::F {
        Self::F::from(if inverse { n as Self } else { 1 }).recip()
    }
    fn extract(f: Self::F) -> Self {
        f.value
    }
}

fn dft<T: internal::FFT>(v: &[T], desired_len: usize) -> Vec<T::F> {
    assert!(v.len() <= desired_len);

    let complex_v = v
        .iter()
        .cloned()
        .chain(std::iter::repeat(T::ZERO))
        .take(desired_len.next_power_of_two())
        .map(T::F::from)
        .collect::<Vec<_>>();
    fftcore::<T>(&complex_v, false)
}
fn idft<T: internal::FFT>(dft_v: &[T::F], desired_len: usize) -> Vec<T> {
    assert!(dft_v.len() >= desired_len);
    let complex_v = fftcore::<T>(dft_v, true);
    complex_v.into_iter().take(desired_len).map(T::extract).collect()
}
fn fftcore<T: internal::FFT>(v: &[T::F], inverse: bool) -> Vec<T::F> {
    let n = v.len();
    assert!(n.is_power_of_two());
    let offset = (n.leading_zeros() + 1) % 0_usize.count_zeros();

    let factor = T::get_factor(n, inverse);
    let roots_of_unity = T::get_roots(n, inverse);
    let mut dft = (0..n)
        .map(|i| v[i.reverse_bits() >> offset] * factor)
        .collect::<Vec<_>>();

    for m in (0..).map(|s| 1 << s).take_while(|&m| m < n) {
        for k in (0..n).step_by(2 * m) {
            for j in 0..m {
                let u = dft[k + j];
                let t = dft[k + j + m] * roots_of_unity[n / 2 / m * j];
                dft[k + j] = u + t;
                dft[k + j + m] = u - t;
            }
        }
    }
    dft
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn complex() {
        let v = vec![7.0, 1.0, 1.0];
        let dft_v = dft(&v, v.len());
        let new_v: Vec<f64> = idft(&dft_v, v.len());

        let six = C::from(6.0);
        let seven = C::from(7.0);
        let nine = C::from(9.0);
        let i = C::new(0.0, 1.0);

        assert_eq!(dft_v, vec![nine, six + i, seven, six - i]);
        assert_eq!(new_v, v);
    }

    #[test]
    fn modular() {
        let v = vec![7, 1, 1];
        let dft_v = dft(&v, v.len());
        let new_v: Vec<u64> = idft(&dft_v, v.len());

        let eval0 = Quotient::<Mod998244353>::from(9);
        let eval1 = Quotient::<Mod998244353>::from(911660641);
        let eval2 = Quotient::<Mod998244353>::from(7);
        let eval3 = Quotient::<Mod998244353>::from(86583724);

        assert_eq!(dft_v, vec![eval0, eval1, eval2, eval3]);
        assert_eq!(new_v, v);
    }
}
