/* Each new term in the Fibonacci sequence is generated by adding the previous
 * two terms. By starting with 1 and 2, the first 10 terms will be:
 *
 *   1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ...
 *
 * By considering the terms in the Fibonacci sequence whose values do not
 * exceed four million, find the sum of the even-valued terms.
 */

use ps::math::fibonacci;
fn solve(n: u64) -> u64 {
    fibonacci(1, 2).filter(|x| x % 2 == 0).take_while(|x| x < &n).sum()
}

fn main() {
    euler::bench(|| solve(4_000_000));
}