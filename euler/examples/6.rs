/* The sum of the squares of the first ten natural numbers is,
 *
 *   1^2 + 2^2 + ... + 10^2 = 385.
 *
 * The square of the sum of the first ten natural numbers is,
 *
 *   (1 + 2 + ... + 10)^2 = 55^2 = 3025.
 *
 * Hence the difference between the sum of the squares of the first ten natural
 * numbers and the square of the sum is 3025 - 385 = 2640.
 *
 * Find the difference between the sum of the squares of the first one hundred
 * natural numbers and the square of the sum.
 */

fn solve(n: u64) -> u64 {
    (1..n + 1).flat_map(|x| (x + 1..n + 1).map(move |y| 2 * x * y)).sum()
}

#[cfg(test)]
mod tests {
    use super::solve;
    #[test]
    fn hint_p0006() {
        assert_eq!(solve(10), 2640);
    }
}

fn main() {
    euler::bench(|| solve(100));
}
