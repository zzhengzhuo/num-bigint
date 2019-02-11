use std::borrow::Cow;

use num_traits::{One, Signed};

use crate::algorithms::extended_gcd;
use crate::big_digit::BigDigit;
use crate::{BigInt, BigUint};

/// Given `q` (odd) calculates `qinv`, such that `q * qinv = 1 (mod 2**32)`.
fn mod_inv1_u32(q: u32) -> u32 {
    debug_assert!(q & 1 == 1, "q must be odd");

    // Initial guess, at least 5 bits are correct.
    let mut qinv = (q.wrapping_add(q).wrapping_add(q)) ^ 0x02;

    // 0
    let mut tmp = q.wrapping_mul(qinv);
    qinv = qinv.wrapping_mul(2u32.wrapping_sub(tmp));

    // 1
    tmp = q.wrapping_mul(qinv);
    qinv = qinv.wrapping_mul(2u32.wrapping_sub(tmp));

    // 2
    tmp = q.wrapping_mul(qinv);
    qinv.wrapping_mul(2u32.wrapping_sub(tmp))
}

/// Given `q` calculates `qinv`, such that `q * qinv = 1 (mod 2**64)`.
fn mod_inv1_u64(q: u64) -> u64 {
    debug_assert!(q & 1 == 1, "q must be odd");

    let qinv = mod_inv1_u32(q as u32) as u64;
    qinv.wrapping_mul(2u64.wrapping_sub(q.wrapping_mul(qinv)))
}

/// Given `q` calculates `qinv`, such that `q * qinv = 1 (mod 2**BITS)`.
#[cfg(feature = "u64_digit")]
pub fn mod_inv1(q: BigDigit) -> BigDigit {
    mod_inv1_u64(q)
}

/// Given `q` calculates `qinv`, such that `q * qinv = 1 (mod 2**BITS)`.
#[cfg(not(feature = "u64_digit"))]
pub fn mod_inv1(q: BigDigit) -> BigDigit {
    mod_inv1_u32(q)
}

/// Calculate the modular inverse of `g`.
/// Implementation is based on the naive version from wikipedia.
#[inline]
pub fn mod_inverse(g: Cow<BigUint>, n: Cow<BigUint>) -> Option<BigInt> {
    if g.as_ref().data.len() == 1 && n.as_ref().data.len() == 1 {
        let x = g.as_ref().data[0];
        let q = n.as_ref().data[0];
        // Odd, with a power of 2 as modulus
        if (q & (q - 1)) == 0 && (x & 1 == 1) {
            return Some(mod_inv1(x).into());
        }
    }

    let (d, x, _) = extended_gcd(g, n.clone(), true);

    if !d.is_one() {
        return None;
    }

    let x = x.unwrap();

    if x.is_negative() {
        Some(x + n.as_ref())
    } else {
        Some(x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use integer::Integer;
    use num_traits::FromPrimitive;

    use crate::traits::ModInverse;

    #[test]
    fn test_mod_inverse() {
        let tests = [
            ["1234567", "458948883992"],
	    ["239487239847", "2410312426921032588552076022197566074856950548502459942654116941958108831682612228890093858261341614673227141477904012196503648957050582631942730706805009223062734745341073406696246014589361659774041027169249453200378729434170325843778659198143763193776859869524088940195577346119843545301547043747207749969763750084308926339295559968882457872412993810129130294592999947926365264059284647209730384947211681434464714438488520940127459844288859336526896320919633919"],
	    ["-10", "13"],
            ["-6193420858199668535", "2881"],
        ];

        for test in &tests {
            let element = BigInt::parse_bytes(test[0].as_bytes(), 10).unwrap();
            let modulus = BigInt::parse_bytes(test[1].as_bytes(), 10).unwrap();

            println!("{} modinv {}", element, modulus);
            let inverse = element.clone().mod_inverse(&modulus).unwrap();
            println!("inverse: {}", &inverse);
            let cmp = (inverse * &element).mod_floor(&modulus);

            assert_eq!(
                cmp,
                BigInt::one(),
                "mod_inverse({}, {}) * {} % {} = {}, not 1",
                &element,
                &modulus,
                &element,
                &modulus,
                &cmp
            );
        }

        // exhaustive tests for small numbers
        for n in 2..100 {
            let modulus = BigInt::from_u64(n).unwrap();
            for x in 1..n {
                for sign in vec![1i64, -1i64] {
                    let element = BigInt::from_i64(sign * x as i64).unwrap();
                    let gcd = element.gcd(&modulus);

                    if !gcd.is_one() {
                        continue;
                    }

                    let inverse = element.clone().mod_inverse(&modulus).unwrap();
                    let cmp = (&inverse * &element).mod_floor(&modulus);
                    println!("inverse: {}", &inverse);
                    assert_eq!(
                        cmp,
                        BigInt::one(),
                        "mod_inverse({}, {}) * {} % {} = {}, not 1",
                        &element,
                        &modulus,
                        &element,
                        &modulus,
                        &cmp
                    );
                }
            }
        }
    }

    #[test]
    fn test_mod_inv1_u32() {
        for q in (1u32..100_000).step_by(2) {
            let qinv = mod_inv1_u32(q as u32);
            assert_eq!(q.wrapping_mul(qinv), 1, "{} * {} != 1", q, qinv);
        }
    }

    #[test]
    fn test_mod_inv1_u64() {
        let start = u32::max_value() as u64;
        for q in (start..start + 100_000).step_by(2) {
            let qinv = mod_inv1_u64(q as u64);
            assert_eq!(q.wrapping_mul(qinv), 1, "{} * {} != 1", q, qinv);
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_quotient_remainder() {
        use rand::{thread_rng, Rng};
        let mut rng = thread_rng();

        for _ in 1..1000 {
            let mut q: BigDigit = rng.gen();
            // make odd
            q |= 1;
            let qinv = mod_inv1(q);
            assert_eq!(q.wrapping_mul(qinv), 1, "{} * {} != 1", q, qinv);
        }
    }

    // Note: this takes some time ;)
    // #[test]
    // fn test_mod_inv1_u64_exhaustive() {
    //     for q in (1u64..u64::max_value()).step_by(2) {
    //         let qinv = mod_inv1_u64(q as u64);
    //         assert_eq!(q.wrapping_mul(qinv), 1, "{} * {} != 1", q, qinv);
    //     }
    // }
}
