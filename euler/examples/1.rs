/* If we list all the natural numbers below 10 that are multiples of 3 or 5,
 * we get 3, 5, 6 and 9. The sum of these multiples is 23.
 *
 * Find the sum of all the multiples of 3 or 5 below 1000.
 */

fn solve(n: u64) -> u64 {
    (1..n).filter(|x| x % 3 == 0 || x % 5 == 0).sum()
}

#[cfg(test)]
mod tests {
    use super::solve;
    #[test]
    fn hint_p0001() {
        assert_eq!(solve(10), 23);
    }
}

fn main() {
    euler::bench(|| solve(1_000));
}
