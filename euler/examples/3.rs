/* The prime factors of 13195 are 5, 7, 13 and 29.
 *
 * What is the largest prime factor of the number 600851475143 ?
 */

use ps::math::prime::sieve;
fn solve(n: u64) -> Vec<u64> {
    sieve()
        .take_while(|&p| p * p <= n)
        .filter(|&p| &n % p == 0)
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use super::solve;
    #[test]
    fn hint_p0003() {
        assert_eq!(solve(13195), vec![5, 7, 13, 29]);
    }
}

fn main() {
    euler::bench(|| *solve(600851475143).last().unwrap());
}
