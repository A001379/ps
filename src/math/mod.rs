//! Mathematical algorithms.

pub mod num;

pub mod modular;

pub mod diophantine;
pub mod prime;

pub mod fourier;

/// Checks whether the number is palindrome or not.
///
/// # Examples
///
/// ```
/// use ps::math::is_palindrome;
///
/// assert!(is_palindrome(12321));
/// assert!(!is_palindrome(123456));
///
/// assert!(is_palindrome(0));
/// ```
pub fn is_palindrome(n: u64) -> bool {
    fn auxiliary(n: u64, m: &mut u64) -> bool {
        if n <= 10 {
            n == *m % 10
        } else if auxiliary(n / 10, m) {
            *m /= 10;
            n % 10 == *m % 10
        } else {
            false
        }
    }
    let mut ndup = n;
    auxiliary(n, &mut ndup)
}

/// Generates a Fibonacci sequence from given two terms.
///
/// # Arguments
///
/// * `first`, `second` - First and second terms.
///
/// # Examples
///
/// ```
/// use ps::math::fibonacci;
/// assert_eq!(fibonacci(1, 1).take(10).collect::<Vec<_>>(),
///            vec![1, 1, 2, 3, 5, 8, 13, 21, 34, 55])
/// ```
pub fn fibonacci(first: u64, second: u64) -> impl Iterator<Item = u64> {
    Fibo {
        curr: first,
        next: second,
    }
}
struct Fibo {
    curr: u64,
    next: u64,
}
impl Iterator for Fibo {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.curr;
        self.curr = self.next;
        self.next += curr;
        Some(curr)
    }
}
