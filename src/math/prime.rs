//! Prime numbers and related algorithms.

/// Generates primes from scratch using sieves of Eratosthenes.
///
/// # Examples
///
/// ```
/// use ps::math::prime::sieve;
/// assert_eq!(sieve().take_while(|&p| p <= 20).collect::<Vec<_>>(),
///            vec![2, 3, 5, 7, 11, 13, 17, 19])
/// ```
pub fn sieve() -> impl Iterator<Item = u64> {
    let cache = vec![2, 3];
    cache.clone().into_iter().chain(sieve_cont(cache))
}
/// Continues generating primes by applying sieves of Eratosthenes on cached primes.
///
/// # Arguments
///
/// * `cache` - A sorted vector of primes without any missing.
///
/// # Examples
///
/// ```
/// use ps::math::prime::sieve_cont;
/// assert_eq!(sieve_cont(vec![2, 3, 5, 7]).take(4).collect::<Vec<_>>(),
///            vec![11, 13, 17, 19])
/// ```
pub fn sieve_cont(cache: Vec<u64>) -> impl Iterator<Item = u64> {
    Primes { cache }
}
struct Primes {
    pub cache: Vec<u64>,
}
impl Iterator for Primes {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let mut curr = self.cache.last().cloned().unwrap();
        loop {
            if curr % 6 == 1 {
                curr += 4;
            } else {
                curr += 2;
            }
            if self
                .cache
                .iter()
                .take_while(|&p| p * p <= curr)
                .try_for_each(|&p| if curr % p == 0 { Err(()) } else { Ok(()) })
                .is_ok()
            {
                self.cache.push(curr);
                return Some(curr);
            }
        }
    }
}
