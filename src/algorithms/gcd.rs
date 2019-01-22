use std::borrow::Cow;

use num_traits::Zero;

use crate::algorithms::div_rem;
use crate::big_digit::{BigDigit, BITS};
use crate::bigint::Sign::*;
use crate::bigint::{BigInt, ToBigInt};
use crate::biguint::{BigUint, IntDigits};

/// Uses the lehemer algorithm.
/// Based on https://github.com/golang/go/blob/master/src/math/big/int.go#L612
/// If `extended` is set, the Bezout coefficients are calculated, otherwise they are `None`.
pub fn extended_gcd(
    a_in: Cow<BigUint>,
    b_in: Cow<BigUint>,
    extended: bool,
) -> (BigInt, Option<BigInt>, Option<BigInt>) {
    println!("-- egcd {:?} - {:?} - {}", a_in, b_in, extended);
    assert!(!a_in.is_zero(), "a must not be 0");
    assert!(!b_in.is_zero(), "b must not be 0");

    let a_in = a_in.to_bigint().unwrap();
    let b_in = b_in.to_bigint().unwrap();

    let mut a = a_in.clone();
    let mut b = b_in.clone();

    // `ua` (`ub`) tracks how many times input `a_in` has beeen accumulated into `a` (`b`).
    let mut ua = if extended { Some(1.into()) } else { None };
    let mut ub = if extended { Some(0.into()) } else { None };

    // Ensure that a >= b
    if a < b {
        std::mem::swap(&mut a, &mut b);
        std::mem::swap(&mut ua, &mut ub);
    }

    println!("  ua: {:?} - ub: {:?}", ua, ub);

    let mut q: BigInt = 0.into();
    let mut r: BigInt = 0.into();
    let mut s: BigInt = 0.into();
    let mut t: BigInt = 0.into();

    while b.len() > 1 {
        // Attempt to calculate in single-precision using leading words of a and b.
        let (u0, u1, v0, v1, even) = lehmer_simulate(&a, &b);

        // multiprecision step
        if v0 != 0 {
            // Simulate the effect of the single-precision steps using cosequences.
            // a = u0 * a + v0 * b
            // b = u1 * a + v1 * b
            lehmer_update(
                &mut a, &mut b, &mut q, &mut r, &mut s, &mut t, u0, u1, v0, v1, even,
            );

            if extended {
                // ua = u0 * ua + v0 * ub
                // ub = u1 * ua + v1 * ub
                lehmer_update(
                    ua.as_mut().unwrap(),
                    ub.as_mut().unwrap(),
                    &mut q,
                    &mut r,
                    &mut s,
                    &mut t,
                    u0,
                    u1,
                    v0,
                    v1,
                    even,
                );
            }
        } else {
            // Single-digit calculations failed to simulate any quotients.
            euclid_udpate(
                &mut a, &mut b, &mut ua, &mut ub, &mut q, &mut r, &mut s, &mut t, extended,
            );
        }
    }

    if b.len() > 0 {
        println!("  -- base case ({} - {})", &a, &b);
        // base case if b is a single digit
        if a.len() > 1 {
            // a is longer than a single word, so one update is needed
            euclid_udpate(
                &mut a, &mut b, &mut ua, &mut ub, &mut q, &mut r, &mut s, &mut t, extended,
            );
        }

        if b.len() > 0 {
            println!("  -- inner base case");
            // a and b are both single word
            let mut a_word = a.digits()[0];
            let mut b_word = b.digits()[0];

            if extended {
                let mut ua_word: BigDigit = 1;
                let mut ub_word: BigDigit = 0;
                let mut va: BigDigit = 0;
                let mut vb: BigDigit = 1;
                let mut even = true;

                while b_word != 0 {
                    println!("\tloop: {} - {}", a_word, b_word);
                    let q = a_word / b_word;
                    let r = a_word % b_word;
                    a_word = b_word;
                    b_word = r;

                    let q = ua_word.wrapping_add(q.wrapping_mul(ub_word));
                    ua_word = ub_word;
                    ub_word = q;

                    let q = va.wrapping_add(q.wrapping_mul(vb));
                    va = vb;
                    vb = q;
                    even = !even;
                }
                println!("\t{} - {} - {}", ua_word, va, even);
                t.data.set_digit(ua_word);
                s.data.set_digit(va);
                t.sign = if even { Plus } else { Minus };
                s.sign = if even { Minus } else { Plus };

                println!(
                    "\t{} {} {} {}",
                    t,
                    s,
                    ua.clone().unwrap(),
                    ub.clone().unwrap()
                );
                if let Some(ua) = ua.as_mut() {
                    t *= ua.clone();
                    s *= ub.unwrap();

                    *ua = &t + &s;
                }
            } else {
                while b_word != 0 {
                    let quotient = a_word % b_word;
                    a_word = b_word;
                    b_word = quotient;
                }
            }
            a.digits_mut()[0] = a_word;

            println!("\ta: {} - {}", &a, a_word)
        }
    }

    a.normalize();

    let y = if let Some(ref ua) = ua {
        // y = (z - a * x) / b
        Some((&a - (&a_in * ua)) / &b_in)
    } else {
        None
    };

    (a, ua, y)
}

/// Attempts to simulate several Euclidean update steps using leading digits of `a` and `b`.
/// It returns `u0`, `u1`, `v0`, `v1` such that `a` and `b` can be updated as:
///     a = u0 * a + v0 * b
///     b = u1 * a + v1 * b
///
/// Requirements: `a >= b` and `b.len() > 1`.
/// Since we are calculating the with full words to avoid overflow, `even` (the returned bool)
/// is used to track the sign of cosequences.
/// For even iterations: `u0, v1 >= 0 && u1, v0 <= 0`
/// For odd iterations: `u0, v1 <= && u1, v0 >= 0`
#[inline]
fn lehmer_simulate(a: &BigInt, b: &BigInt) -> (BigDigit, BigDigit, BigDigit, BigDigit, bool) {
    println!("-- lehmer_simulate");
    // m >= 2
    let m = b.len();
    // n >= m >= 2
    let n = a.len();

    // extract the top word of bits from a and b
    let h = a.digits()[n - 1].leading_zeros();
    let mut a1 = a.digits()[n - 1] << h | a.digits()[n - 2].wrapping_shr(BITS as u32 - h);

    // b may have implicit zero words in the high bits if the lengths differ
    let mut a2 = if n == m {
        b.digits()[n - 1] << h | b.digits()[n - 2].wrapping_shr(BITS as u32 - h)
    } else if n == m + 1 {
        b.digits()[n - 2].wrapping_shr(BITS as u32 - h)
    } else {
        0
    };

    // odd, even tracking
    let mut even = false;
    let mut u = (0, 1, 0);
    let mut v = (0, 0, 1);

    // Calculate the quotient and cosequences using Collins' stoppting condition.
    while a2 >= v.2 && a1.wrapping_sub(a2) > v.1 + v.2 {
        let q = a1 / a2;
        let r = a1 % a2;

        a1 = a2;
        a2 = r;

        u = (u.1, u.2, u.1 + q * u.2);
        v = (v.1, v.2, v.1 + q * v.2);
        even = !even;
    }

    (u.0, u.1, v.0, v.1, even)
}

fn lehmer_update(
    a: &mut BigInt,
    b: &mut BigInt,
    q: &mut BigInt,
    r: &mut BigInt,
    s: &mut BigInt,
    t: &mut BigInt,
    u0: BigDigit,
    u1: BigDigit,
    v0: BigDigit,
    v1: BigDigit,
    even: bool,
) {
    println!("-- lehmer_update");
    t.data.set_digit(u0);
    s.data.set_digit(v0);
    t.sign = if even { Plus } else { Minus };
    s.sign = if even { Minus } else { Plus };

    // TODO: why do I need to clone?
    *t *= a.clone();
    *s *= b.clone();

    r.data.set_digit(u1);
    q.data.set_digit(v1);
    r.sign = if even { Minus } else { Plus };
    q.sign = if even { Plus } else { Minus };

    // TODO: why do I need to clone?
    *r *= a.clone();
    *q *= b.clone();

    *a = t + s;
    *b = r + q;
}

fn euclid_udpate(
    a: &mut BigInt,
    b: &mut BigInt,
    ua: &mut Option<BigInt>,
    ub: &mut Option<BigInt>,
    q: &mut BigInt,
    r: &mut BigInt,
    s: &mut BigInt,
    t: &mut BigInt,
    extended: bool,
) {
    println!("-- euclid_update");
    let (q_new, r_new) = div_rem(&a.data, &b.data);
    q.data = q_new;
    r.data = r_new;

    // *a = *b;
    // *b = *r;
    // *r = *a;
    // std::mem::swap(a, b);
    // std::mem::swap(b, r);
    // TODO: avoid cloning
    let old_a = a.clone();
    *a = b.clone();
    *b = r.clone();
    *r = old_a;

    if extended {
        // ua, ub = ub, ua - q * ub
        if let Some(ub) = ub.as_mut() {
            if let Some(ua) = ua.as_mut() {
                // TODO: figure out how to avoid these clonese
                *t = ub.clone();
                *s = ub.clone() * q.clone();
                *ub = ua.clone() - s.clone();
                *ua = t.clone();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use num_traits::FromPrimitive;

    #[cfg(feature = "rand")]
    use crate::bigrand::RandBigInt;
    #[cfg(feature = "rand")]
    use num_traits::One;
    #[cfg(feature = "rand")]
    use rand::{SeedableRng, XorShiftRng};

    /// Calculates the extended eucledian algorithm.
    /// See https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm for details.
    /// The returned values are
    /// - greatest common divisor (1)
    /// - Bezout coefficients (2)
    // TODO: implement optimized variants
    #[cfg(feature = "rand")]
    fn extended_gcd_euclid(a: Cow<BigUint>, b: Cow<BigUint>) -> (BigInt, BigInt, BigInt) {
        use crate::bigint::ToBigInt;
        use num_traits::{One, Zero};

        let (mut s, mut old_s) = (BigInt::zero(), BigInt::one());
        let (mut t, mut old_t) = (BigInt::one(), BigInt::zero());
        let (mut r, mut old_r) = (b.to_bigint().unwrap(), a.to_bigint().unwrap());

        while !r.is_zero() {
            let quotient = &old_r / &r;
            old_r = old_r - &quotient * &r;
            std::mem::swap(&mut old_r, &mut r);
            old_s = old_s - &quotient * &s;
            std::mem::swap(&mut old_s, &mut s);
            old_t = old_t - quotient * &t;
            std::mem::swap(&mut old_t, &mut t);
        }

        // == (a, b) / gcd
        // let quotients = (t, s);

        (old_r, old_s, old_t)
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_extended_gcd_assumptions() {
        let mut rng = XorShiftRng::from_seed([1u8; 16]);

        for i in 1usize..100 {
            for j in &[2usize, 64, 128] {
                println!("round {} - {}", i, j);
                let a = rng.gen_biguint_range(&BigUint::one(), &BigUint::from(i * j));
                let b = rng.gen_biguint_range(&BigUint::one(), &BigUint::from(i * j));
                let (q, s_k, t_k) = extended_gcd(Cow::Borrowed(&a), Cow::Borrowed(&b), true);
                println!(
                    "gcd({}, {}) = {} [{}, {}]",
                    &a,
                    &b,
                    &q,
                    s_k.clone().unwrap(),
                    t_k.clone().unwrap()
                );

                let lhs = BigInt::from_biguint(Plus, a) * &s_k.unwrap();
                let rhs = BigInt::from_biguint(Plus, b) * &t_k.unwrap();

                assert_eq!(q.clone(), &lhs + &rhs, "{} = {} + {}", q, lhs, rhs);
            }
        }
    }

    #[test]
    fn test_extended_gcd_example() {
        // simple example for wikipedia
        let a = BigUint::from_u32(240).unwrap();
        let b = BigUint::from_u32(46).unwrap();
        let (q, s_k, t_k) = extended_gcd(Cow::Owned(a), Cow::Owned(b), true);

        assert_eq!(q, BigInt::from_i32(2).unwrap());
        assert_eq!(s_k.unwrap(), BigInt::from_i32(-9).unwrap());
        assert_eq!(t_k.unwrap(), BigInt::from_i32(47).unwrap());
    }

    #[test]
    fn test_extended_gcd_example_not_extended() {
        // simple example for wikipedia
        let a = BigUint::from_u32(240).unwrap();
        let b = BigUint::from_u32(46).unwrap();
        let (q, s_k, t_k) = extended_gcd(Cow::Owned(a), Cow::Owned(b), false);

        assert_eq!(q, BigInt::from_i32(2).unwrap());
        assert_eq!(s_k, None);
        assert_eq!(t_k, None);
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_extended_gcd_lehmer_euclid() {
        let mut rng = XorShiftRng::from_seed([1u8; 16]);

        for i in 1usize..100 {
            for j in &[2usize, 64, 128] {
                println!("round {} - {}", i, j);
                let a = rng.gen_biguint_range(&BigUint::one(), &BigUint::from(i * j));
                let b = rng.gen_biguint_range(&BigUint::one(), &BigUint::from(i * j));
                let (q, s_k, t_k) = extended_gcd(Cow::Borrowed(&a), Cow::Borrowed(&b), true);

                let expected = extended_gcd_euclid(Cow::Borrowed(&a), Cow::Borrowed(&b));
                assert_eq!(q, expected.0);
                assert_eq!(s_k.unwrap(), expected.1);
                assert_eq!(t_k.unwrap(), expected.2);
            }
        }
    }
}
