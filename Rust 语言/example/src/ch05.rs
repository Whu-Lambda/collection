fn fib(n: u32) -> u32 {
    if n < 1 {
        return 0;
    } else {
        return n + fib(n - 1);
    }
}

fn add(x: i32, y: i32) -> i32 {
    x + y
}

fn hello(name: &str) {
    println!("Hello, {}", name);
}

#[cfg(test)]
mod tests {
    use self::super::*;

    #[test]
    fn test_fib() {
        assert_eq!(fib(0), 0);
        assert_eq!(fib(1), 1);
    }
    #[test]
    fn test_add() {
        assert_eq!(add(1, 1), 2);
    }

    #[test]
    fn test_hello() {
        hello("Rust");
    }
}
