use std::borrow::Cow;

use num_traits::{One, Signed};

use crate::algorithms::extended_gcd;
use crate::big_digit::BigDigit;
use crate::{BigInt, BigUint};

/// Precomputed lower 8 bits for inversion.
const MINV8: [u8; 128] = [
    //  Index:
    0x01, 0xAB, 0xCD, 0xB7, 0x39, 0xA3, 0xC5, 0xEF, 0xF1, 0x1B, 0x3D, 0xA7, 0x29, 0x13, 0x35,
    0xDF, //   0- 15
    0xE1, 0x8B, 0xAD, 0x97, 0x19, 0x83, 0xA5, 0xCF, 0xD1, 0xFB, 0x1D, 0x87, 0x09, 0xF3, 0x15,
    0xBF, //  16- 31
    0xC1, 0x6B, 0x8D, 0x77, 0xF9, 0x63, 0x85, 0xAF, 0xB1, 0xDB, 0xFD, 0x67, 0xE9, 0xD3, 0xF5,
    0x9F, //  32- 47
    0xA1, 0x4B, 0x6D, 0x57, 0xD9, 0x43, 0x65, 0x8F, 0x91, 0xBB, 0xDD, 0x47, 0xC9, 0xB3, 0xD5,
    0x7F, //  48- 63
    0x81, 0x2B, 0x4D, 0x37, 0xB9, 0x23, 0x45, 0x6F, 0x71, 0x9B, 0xBD, 0x27, 0xA9, 0x93, 0xB5,
    0x5F, //  64- 79
    0x61, 0x0B, 0x2D, 0x17, 0x99, 0x03, 0x25, 0x4F, 0x51, 0x7B, 0x9D, 0x07, 0x89, 0x73, 0x95,
    0x3F, //  80- 95
    0x41, 0xEB, 0x0D, 0xF7, 0x79, 0xE3, 0x05, 0x2F, 0x31, 0x5B, 0x7D, 0xE7, 0x69, 0x53, 0x75,
    0x1F, //  96-111
    0x21, 0xCB, 0xED, 0xD7, 0x59, 0xC3, 0xE5, 0x0F, 0x11, 0x3B, 0x5D, 0xC7, 0x49, 0x33, 0x55,
    0xFF, // 112-127
];

/// Given `q` (odd) calculates `qinv`, such that `q * qinv = 1 (mod 2**32)`.
fn mod_inv1_u32(q: u32) -> u32 {
    debug_assert!(q & 1 == 1, "q must be odd");

    // Initial guess, lower 8 bits are correct.
    let mut qinv = MINV8[((q & 0xFF) >> 1) as usize] as u32;

    // lower 16 bits
    let mut tmp = q.wrapping_mul(qinv);
    qinv = qinv.wrapping_mul(2u32.wrapping_sub(tmp));

    // lower 32 bits
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
