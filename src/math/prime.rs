//! Prime numbers and related algorithms.

use std::collections::HashMap;

fn next_prime(primes: &mut Vec<u64>) -> u64 {
    // primes should be sorted and at least contains 2 and 3.
    let mut curr = primes.last().cloned().unwrap();
    loop {
        if curr % 6 == 1 {
            curr += 4;
        } else {
            curr += 2;
        }
        if primes
            .iter()
            .take_while(|&p| p * p <= curr)
            .try_for_each(|&p| if curr % p == 0 { Err(()) } else { Ok(()) })
            .is_ok()
        {
            primes.push(curr);
            return curr;
        }
    }
}

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
    cache.clone().into_iter().chain(Primes { cache })
}
struct Primes {
    cache: Vec<u64>,
}
impl Iterator for Primes {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        Some(next_prime(&mut self.cache))
    }
}

/// Factorizes given series of integers into prime factors, as `HashMap`
/// format.
///
/// # Arguments
///
/// * `iter` - An integer iterator.
///
/// # Examples
///
/// ```
/// use std::collections::HashMap;
/// use ps::math::prime::factor;
///
/// let mut iter = factor(vec![28, 1].into_iter());
/// let prime_factor_of_twentyeight: HashMap<u64, u64> = [(2, 2), (7, 1)].iter().cloned().collect();
/// let prime_factor_of_one: HashMap<u64, u64> = [(1, 1)].iter().cloned().collect();
///
/// assert_eq!(iter.next(), Some(prime_factor_of_twentyeight));
/// assert_eq!(iter.next(), Some(prime_factor_of_one));
/// ```
pub fn factor(iter: impl Iterator<Item = u64>) -> impl Iterator<Item = HashMap<u64, u64>> {
    Factor {
        prime: Primes { cache: vec![2, 3] },
        iter,
    }
}
struct Factor<Iter: Iterator<Item = u64>> {
    prime: Primes,
    iter: Iter,
}
impl<Iter: Iterator<Item = u64>> Iterator for Factor<Iter> {
    type Item = HashMap<u64, u64>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(mut n) = self.iter.next() {
            if n <= 1 {
                return Some([(n, 1)].iter().cloned().collect());
            }
            loop {
                let p = next_prime(&mut self.prime.cache);
                if p >= n {
                    break;
                }
            }
            Some(
                self.prime
                    .cache
                    .iter()
                    .filter_map(|&p| {
                        let mut nfac = 0;
                        while n % p == 0 {
                            nfac += 1;
                            n /= p;
                        }
                        if nfac > 0 {
                            Some((p, nfac))
                        } else {
                            None
                        }
                    })
                    .collect(),
            )
        } else {
            None
        }
    }
}
