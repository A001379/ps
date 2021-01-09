/* A Pythagorean triplet is a set of three natural numbers, a < b < c, for
 * which,
 *
 *   a^2 + b^2 = c^2.
 *
 * For example, 3^2 + 4^2 = 9 + 16 = 25 = 5^2.
 *
 * There exists exactly one Pythagorean triplet for which a + b + c = 1000.
 * Find the product abc.
 */

fn solve(n: u64) -> u64 {
    let (ab, a_b) = (1..n)
        .flat_map(|a| (a + 1..n).map(move |b| (a * b, a + b)))
        .filter(|(ab, a_b)| n * n + 2 * ab == 2 * n * a_b)
        .next()
        .unwrap();
    ab * (n - a_b)
}

fn main() {
    euler::bench(|| solve(1000));
}
