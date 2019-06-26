fn main() {
    println!("Hello world!");
}

fn mod_exp(m: i32, n: i32, p: i32) -> i32 {
    let mut result = 1;
    let mut a = m;
    let mut exp = n;

    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * a) % p;
        }
        a = (a * a) % p;
        exp = exp / 2;
    }

    return result;
}

fn mod_inverse(m: i32, p: i32) -> i32 {
    return mod_exp(m, p - 2, p);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mod_exp_powers_of_5_mod_7() {
        assert_eq!(1, mod_exp(5, 0, 7));
        assert_eq!(5, mod_exp(5, 1, 7));
        assert_eq!(4, mod_exp(5, 2, 7));
        assert_eq!(6, mod_exp(5, 3, 7));
        assert_eq!(2, mod_exp(5, 4, 7));
        assert_eq!(3, mod_exp(5, 5, 7));
        assert_eq!(1, mod_exp(5, 6, 7));
        assert_eq!(5, mod_exp(5, 7, 7));
    }

    #[test]
    fn test_mod_inverse_for_7() {
        let a = [2, 3, 5, 7, 13, 19];

        for p in a.iter() {
            for i in 1..p {
                assert_eq!(1, (mod_inverse(i, p) * i) % p);
            }
        }
    }
}
