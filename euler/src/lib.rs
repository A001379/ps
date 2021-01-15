use std::time::Instant;

pub fn bench<F: FnOnce() -> u64>(solve: F) {
    let now = Instant::now();
    let ans = solve();
    let nanosec = now.elapsed().as_nanos();
    let elapsed = if nanosec < 1_000 {
        format!("{}ns", nanosec)
    } else if nanosec < 1_000_000 {
        format!("{}us", nanosec / 1_000)
    } else if nanosec < 1_000_000_000 {
        format!("{}ms", nanosec / 1_000_000)
    } else {
        format!("{}s", nanosec / 1_000_000_000)
    };
    println!("answer: {} (elapsed time: {})", ans, elapsed);
}
