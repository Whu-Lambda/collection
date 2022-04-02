#[cfg(test)]
mod tests {
    use self::super::*;

    #[test]
    fn test_loop() {
        let mut n = 0;
        while true {
            if n > 10 {
                break;
            }
            println!("{}", n);
            n += 1;
        }
    }

    #[test]
    fn test_if() {
        let n = 9;
        let result = if n < 0 {
            -1
        } else if n > 10 {
            if n < 5 {
                return n;
            }
            n - 5
        } else {
            0
        }

        println!("{}", result);
    }
}
