/* The sum of the primes below 10 is 2 + 3 + 5 + 7 = 17.
 *
 * Find the sum of all the primes below two million.
 */

use ps::math::prime::sieve;
fn solve(n: u64) -> u64 {
    sieve().take_while(|&p| p < n).sum()
}

#[cfg(test)]
mod tests {
    use super::solve;
    #[test]
    fn hint_p0010() {
        assert_eq!(solve(10), 17);
    }
}

fn main() {
    euler::bench(|| solve(2_000_000));
}
