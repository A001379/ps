/* A palindromic number reads the same both ways. The largest palindrome made
 * from the product of two 2-digit numbers is 9009 = 91 x 99.
 *
 * Find the largest palindrome made from the product of two 3-digit numbers.
 */

use ps::math::is_palindrome;
fn solve(n: u32) -> u64 {
    let (l, u) = (10_u64.pow(n - 1), 10_u64.pow(n));
    (l..u)
        .flat_map(|x| (x..u).map(move |y| x * y))
        .filter(|&x| is_palindrome(x))
        .max()
        .unwrap()
}

#[cfg(test)]
mod tests {
    use super::solve;
    #[test]
    fn hint_p0004() {
        assert_eq!(solve(2), 9009);
    }
}

fn main() {
    euler::bench(|| solve(3));
}
