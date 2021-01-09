/* By listing the first six prime numbers: 2, 3, 5, 7, 11, and 13, we can see
 * that the 6th prime is 13.
 *
 * What is the 10001st prime number?
 */

use ps::math::prime::sieve;
fn solve(n: u64) -> u64 {
    sieve().nth((n - 1) as usize).unwrap()
}

#[cfg(test)]
mod tests {
    use super::solve;
    #[test]
    fn hint_p0007() {
        assert_eq!(solve(6), 13);
    }
}

fn main() {
    euler::bench(|| solve(10_001));
}
