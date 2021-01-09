/* 2520 is the smallest number that can be divided by each of the numbers from
 * 1 to 10 without any remainder.
 *
 * What is the smallest positive number that is evenly divisible by all of the
 * numbers from 1 to 20?
 */

use ps::math::diophantine::gcd;
fn solve(n: u64) -> u64 {
    (2..n).fold(1, |acc, x| acc / gcd(acc, x) * x)
}

#[cfg(test)]
mod tests {
    use super::solve;
    #[test]
    fn hint_p0005() {
        assert_eq!(solve(10), 2520);
    }
}

fn main() {
    euler::bench(|| solve(20));
}
