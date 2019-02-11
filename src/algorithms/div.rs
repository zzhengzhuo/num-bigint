use bit_field::BitField;
use num_traits::{One, Zero};
use smallvec::SmallVec;
use std::cmp::Ordering;

use crate::algorithms::{add2, cmp_slice, mod_inv1, sub2};
use crate::big_digit::{self, BigDigit, DoubleBigDigit};
use crate::BigUint;

pub fn div(u: &BigUint, d: &BigUint) -> BigUint {
    if d.is_zero() {
        panic!("Cannot divide by zero");
    }
    if u.is_zero() {
        return Zero::zero();
    }
    if d.data.len() == 1 {
        if d.data[0] == 1 {
            return u.clone();
        }
        let mut res = u.clone();
        div_digit(&mut res, d.data[0]);
        return res;
    }

    // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
    match u.cmp(d) {
        Ordering::Less => return Zero::zero(),
        Ordering::Equal => return One::one(),
        Ordering::Greater => {} // Do nothing
    }

    let shift = d.data.last().unwrap().leading_zeros() as usize;
    let mut a = u << shift;
    let b = d << shift;

    let bn = *b.data.last().unwrap();
    let q_len = a.data.len() - b.data.len() + 1;
    let mut q = BigUint {
        data: smallvec![0; q_len],
    };

    let mut tmp = BigUint {
        data: SmallVec::with_capacity(2),
    };

    for j in (0..q_len).rev() {
        let offset = j + b.data.len() - 1;
        if offset >= a.data.len() {
            continue;
        }

        let mut q0 = tmp;
        q0.data.truncate(0);
        q0.data.extend_from_slice(&a.data[offset..]);

        div_digit(&mut q0, bn);
        let mut prod = &b * &q0;

        while cmp_slice(&prod.data[..], &a.data[j..]) == Ordering::Greater {
            let one: BigUint = One::one();
            q0 = q0 - one;
            prod = prod - &b;
        }

        add2(&mut q.data[j..], &q0.data[..]);
        sub2(&mut a.data[j..], &prod.data[..]);
        a.normalize();

        tmp = q0;
    }

    debug_assert!(a < b);

    q.normalized()
}

pub fn rem(u: &BigUint, d: &BigUint) -> BigUint {
    if d.is_zero() {
        panic!("Cannot divide by zero");
    }
    if u.is_zero() {
        return Zero::zero();
    }
    if d.data.len() == 1 {
        if d.data[0] == 1 {
            return Zero::zero();
        }

        return rem_digit(u, d.data[0]).into();
    }

    // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
    match u.cmp(d) {
        Ordering::Less => return u.clone(),
        Ordering::Equal => return Zero::zero(),
        Ordering::Greater => {} // Do nothing
    }

    let shift = d.data.last().unwrap().leading_zeros() as usize;
    let mut a = u << shift;
    let b = d << shift;

    let bn = *b.data.last().unwrap();
    let q_len = a.data.len() - b.data.len() + 1;
    let mut q = BigUint {
        data: smallvec![0; q_len],
    };

    let mut tmp = BigUint {
        data: SmallVec::with_capacity(2),
    };

    for j in (0..q_len).rev() {
        let offset = j + b.data.len() - 1;
        if offset >= a.data.len() {
            continue;
        }
        let mut q0 = tmp;
        q0.data.truncate(0);
        q0.data.extend_from_slice(&a.data[offset..]);

        div_digit(&mut q0, bn);
        let mut prod = &b * &q0;

        while cmp_slice(&prod.data[..], &a.data[j..]) == Ordering::Greater {
            let one: BigUint = One::one();
            q0 = q0 - one;
            prod = prod - &b;
        }

        add2(&mut q.data[j..], &q0.data[..]);
        sub2(&mut a.data[j..], &prod.data[..]);
        a.normalize();

        tmp = q0;
    }

    debug_assert!(a < b);

    a >> shift
}

pub fn div_rem(u: &BigUint, d: &BigUint) -> (BigUint, BigUint) {
    if d.is_zero() {
        panic!("Cannot divide by zero");
    }
    if u.is_zero() {
        return (Zero::zero(), Zero::zero());
    }
    if d.data.len() == 1 {
        if d.data[0] == 1 {
            return (u.clone(), Zero::zero());
        }
        let mut res = u.clone();
        let rem = div_rem_digit(&mut res, d.data[0]);
        return (res, rem.into());
    }

    // Required or the q_len calculation below can underflow:
    match u.cmp(d) {
        Ordering::Less => return (Zero::zero(), u.clone()),
        Ordering::Equal => return (One::one(), Zero::zero()),
        Ordering::Greater => {} // Do nothing
    }

    // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
    //
    // First, normalize the arguments so the highest bit in the highest digit of the divisor is
    // set: the main loop uses the highest digit of the divisor for generating guesses, so we
    // want it to be the largest number we can efficiently divide by.
    //
    let shift = d.data.last().unwrap().leading_zeros() as usize;
    let mut a = u << shift;
    let b = d << shift;

    // The algorithm works by incrementally calculating "guesses", q0, for part of the
    // remainder. Once we have any number q0 such that q0 * b <= a, we can set
    //
    //     q += q0
    //     a -= q0 * b
    //
    // and then iterate until a < b. Then, (q, a) will be our desired quotient and remainder.
    //
    // q0, our guess, is calculated by dividing the last few digits of a by the last digit of b
    // - this should give us a guess that is "close" to the actual quotient, but is possibly
    // greater than the actual quotient. If q0 * b > a, we simply use iterated subtraction
    // until we have a guess such that q0 * b <= a.
    //

    let bn = *b.data.last().unwrap();
    let q_len = a.data.len() - b.data.len() + 1;
    let mut q = BigUint {
        data: smallvec![0; q_len],
    };

    // We reuse the same temporary to avoid hitting the allocator in our inner loop - this is
    // sized to hold a0 (in the common case; if a particular digit of the quotient is zero a0
    // can be bigger).
    //
    let mut tmp = BigUint {
        data: SmallVec::with_capacity(2),
    };

    for j in (0..q_len).rev() {
        /*
         * When calculating our next guess q0, we don't need to consider the digits below j
         * + b.data.len() - 1: we're guessing digit j of the quotient (i.e. q0 << j) from
         * digit bn of the divisor (i.e. bn << (b.data.len() - 1) - so the product of those
         * two numbers will be zero in all digits up to (j + b.data.len() - 1).
         */
        let offset = j + b.data.len() - 1;
        if offset >= a.data.len() {
            continue;
        }

        /* just avoiding a heap allocation: */
        let mut q0 = tmp;
        q0.data.truncate(0);
        q0.data.extend_from_slice(&a.data[offset..]);

        /*
         * q0 << j * big_digit::BITS is our actual quotient estimate - we do the shifts
         * implicitly at the end, when adding and subtracting to a and q. Not only do we
         * save the cost of the shifts, the rest of the arithmetic gets to work with
         * smaller numbers.
         */
        // let (mut q0, _) = div_rem_digit(a0, bn);
        div_digit(&mut q0, bn);
        let mut prod = &b * &q0;

        while cmp_slice(&prod.data[..], &a.data[j..]) == Ordering::Greater {
            let one: BigUint = One::one();
            q0 = q0 - one;
            prod = prod - &b;
        }

        add2(&mut q.data[j..], &q0.data[..]);
        sub2(&mut a.data[j..], &prod.data[..]);
        a.normalize();

        tmp = q0;
    }

    debug_assert!(a < b);

    (q.normalized(), a >> shift)
}

/// Returns the scaled remainder, `s = x * R**-n (mod q)`
/// `q * qinv = 1 (mod 2**BITS)`, `q` is odd.
fn remainder_a(x: &BigUint, q: BigDigit, qinv: BigDigit) -> BigDigit {
    debug_assert_eq!(q & 1, 1);
    debug_assert_eq!(q.wrapping_mul(qinv), 1);

    // special handling for q = 1
    if q == 1 {
        return 0;
    }

    let mut cy = 0;
    for xi in x.data.iter() {
        let (mut tmp, bw) = xi.overflowing_sub(cy);
        tmp = tmp.wrapping_mul(qinv) + bw as BigDigit;
        cy = umulh(tmp, q);
    }

    if cy > 0 {
        cy = q - cy;
    }

    // Final multiply to radix scale the remainder
    let n = x.data.len();
    let (j, p, bm) = calc_bitmap(n + 1);
    let r_scaled = radix_power(n + 1, j, p, bm, q, qinv);
    mont_mul(cy, r_scaled, q, qinv)
}

/// Returns the scaled remainder, `s = x * R**-n (mod q)`
/// `q * qinv = 1 (mod 2**BITS)`, `q` is odd.
fn remainder_a_u2(x: &BigUint, q: BigDigit, qinv: BigDigit) -> BigDigit {
    debug_assert_eq!(q & 1, 1);
    debug_assert_eq!(q.wrapping_mul(qinv), 1);

    let n = x.data.len();
    if n < 2 {
        return remainder_a(x, q, qinv);
    }
    // special handling for q = 1
    if q == 1 {
        return 0;
    }

    // Pad to even length and then divide by 2.
    let n2 = (n + (n & 1)) >> 1;

    let mut cy0 = 0;
    let mut cy1 = 0;

    for i in 0..n2 {
        let (mut tmp0, bw0) = x.data[i].overflowing_sub(cy0);
        let xin2 = if i + n2 < n {
            x.data[i + n2]
        } else {
            // Handle the case of odd limbs
            0
        };
        let (mut tmp1, bw1) = xin2.overflowing_sub(cy1);

        // Add q to loop output if there was a borrow
        tmp0 = tmp0.wrapping_mul(qinv) + bw0 as BigDigit;
        tmp1 = tmp1.wrapping_mul(qinv) + bw1 as BigDigit;

        cy0 = umulh(tmp0, q);
        cy1 = umulh(tmp1, q);
    }

    if cy0 > 0 {
        cy0 = q - cy0;
    }
    if cy1 > 0 {
        cy1 = q - cy1;
    }

    // P * R = R**n2+1 (mod q)
    let (j, p, bm) = calc_bitmap(n2 + 1);
    let scale = radix_power(n2 + 1, j, p, bm, q, qinv);

    cy1 = mont_mul(cy1, scale, q, qinv);

    // Sum the scaled partial remainders
    cy0 = cy0.wrapping_add(cy1);

    // Check for overflow on addition
    if cy0 < cy1 || cy0 >= q {
        cy0 = cy0.wrapping_sub(q);
    }

    mont_mul(cy0, scale, q, qinv)
}

/// Calculate the montgomery product `x * y * R**-1 (mod q)`,
/// with `R = 2**b`.
/// `q * qinv = 1 (mod 2**b)`, `q` is odd.
fn mont_mul(x: BigDigit, y: BigDigit, q: BigDigit, qinv: BigDigit) -> BigDigit {
    debug_assert_eq!(q & 1, 1);

    let (hi, mut lo) = umul_lohi(x, y);

    lo = qinv.wrapping_mul(lo);
    lo = umulh(q, lo);

    if hi < lo {
        // hi - lo + q, reordered to avoid negative numbers
        q - (lo - hi)
    } else {
        hi - lo
    }
}

/// Calculate the montgomery square `x**2 * R**-1 (mod q)`,
/// with `R = 2**b`.
/// `q * qinv = 1 (mod 2**b)`, `q` is odd.
fn mont_sqr(x: BigDigit, q: BigDigit, qinv: BigDigit) -> BigDigit {
    debug_assert_eq!(q & 1, 1);

    let (hi, mut lo) = usqr_lohi(x);
    lo = qinv.wrapping_mul(lo);
    lo = umulh(q, lo);

    if hi < lo {
        // hi - lo + q, reordered to avoid negative numbers
        q - (lo - hi)
    } else {
        hi - lo
    }
}

/// Calculate the montgomery multiply by unity `x * R**-1 (mod q)`,
/// with `R = 2**b`.
/// `q * qinv = 1 (mod 2**b)`, `q` is odd.
fn mmul_one(x: BigDigit, q: BigDigit, qinv: BigDigit) -> BigDigit {
    debug_assert_eq!(q & 1, 1);

    let mut lo = qinv.wrapping_mul(x);
    lo = umulh(q, lo);

    if lo != 0 {
        q - lo
    } else {
        lo
    }
}

fn calc_bitmap(n: usize) -> (usize, usize, u32) {
    let mut j = 0;
    let mut p = n;
    let mut bm = 0u32;

    while p > 5 {
        bm.set_bit(j, is_even(p));
        p = (p / 2) + 1;
        j += 1;
    }

    (j, p, bm)
}

/// Computes `R**n (mod q)`.
/// - `pow = R**2 (mod q)`
/// - `q * qinv = 1 (mod 2**BITS)`, `q` is odd.
fn radix_power(n: usize, j: usize, p: usize, bm: u32, q: BigDigit, qinv: BigDigit) -> BigDigit {
    // TODO: Constant
    let r = 2u128.pow(big_digit::BITS as u32) % q as u128;
    // TODO: implement optimized squaring algorithm
    let r2 = ((r * r) % q as u128) as u64;

    if n == 2 {
        return r2;
    }

    // R**3 (mod q)
    let mut ptmp = mont_sqr(r2, q, qinv);

    if n == 3 {
        return ptmp;
    }

    let mut pow = if p == 4 {
        mont_mul(r2, ptmp, q, qinv)
    } else {
        mont_sqr(ptmp, q, qinv)
    };

    // Bitmap controlled powering loop, only for n > 5
    for i in (0..j).rev() {
        if bm.get_bit(i) {
            // Reduce R-power by 1
            ptmp = mmul_one(pow, q, qinv);

            // and multiply
            pow = mont_mul(ptmp, pow, q, qinv);
        } else {
            pow = mont_sqr(pow, q, qinv)
        }
    }

    pow
}

#[inline(always)]
fn is_even(n: usize) -> bool {
    (n & 1) as u8 == 0
}

#[inline(always)]
fn umul_lohi(x: BigDigit, y: BigDigit) -> (BigDigit, BigDigit) {
    let res = x as DoubleBigDigit * y as DoubleBigDigit;
    (big_digit::get_hi(res), big_digit::get_lo(res))
}

/// Returns the scaled remainder, `s = x * R**-n (mod q)`
/// `q * qinv = 1 (mod 2**BITS)`, `q` is odd.
fn remainder_b(x: &BigUint, q: BigDigit, qinv: BigDigit) -> BigDigit {
    debug_assert_eq!(q & 1, 1);
    debug_assert_eq!(q.wrapping_mul(qinv), 1);

    let n = x.data.len();
    if n == 1 {
        return x.data[0] % q;
    }

    let mut cy = 0;

    for xi in x.data.iter().take(n - 1) {
        let (mut tmp, overflow) = xi.overflowing_sub(cy);

        tmp = (tmp.wrapping_mul(qinv)) + overflow as BigDigit;
        cy = umulh(tmp, q);
    }

    // Final term, without multiplication
    let xi = x.data[n - 1];

    let tmp = xi.wrapping_sub(cy);
    let lo = if cy > xi { tmp.wrapping_add(q) } else { tmp };

    // Final multiply to radix scale the remainder
    let n = x.data.len();
    let (j, p, bm) = calc_bitmap(n);
    let r_scaled = radix_power(n, j, p, bm, q, qinv);

    mont_mul(lo, r_scaled, q, qinv)
}

/// Calculates the full double width multiply.
#[inline(always)]
fn usqr_lohi(x: BigDigit) -> (BigDigit, BigDigit) {
    // TODO: ensure this uses an optimized squaring method.
    umul_lohi(x, x)
}

/// Upper half multiply. Calculates `floor(x * y / R)`, with `R = 2**BITS`.
#[inline(always)]
fn umulh(x: BigDigit, y: BigDigit) -> BigDigit {
    big_digit::get_hi(x as DoubleBigDigit * y as DoubleBigDigit)
}

/// Calculate the remainder.
pub fn remainder_odd(x: &BigUint, q: BigDigit, qinv: BigDigit) -> BigDigit {
    let n = x.data.len() as usize;

    let (_, _, bm) = calc_bitmap(n);
    let (_, _, bm1) = calc_bitmap(n + 1);

    // if the even element has fewer set bits than the odd, use a, otherwise b
    // TODO: use A for odd, B for even
    if bm.count_ones() < bm1.count_ones() {
        // Algorithm B
        remainder_b(x, q, qinv)
    } else {
        // Algorithm A
        remainder_a_u2(x, q, qinv)
    }
}

/// Calculate the quotient and remainder of `x / q`.
/// The quotient will be in `x` and the remainder is returned.
pub fn div_rem_digit(x: &mut BigUint, q: BigDigit) -> BigDigit {
    if x.is_zero() {
        return 0;
    }
    if x.data.len() == 1 {
        let rem = x.data[0] % q;
        x.data[0] /= q;
        x.normalize();
        return rem;
    }

    if q & 1 == 1 {
        let qinv = mod_inv1(q);

        let r = remainder_a_u2(&*x, q, qinv);

        quotient_odd(x, r, q, qinv);
        r
    } else {
        let tz = q.trailing_zeros();
        let bsave = x.data[0] & ((2 as BigDigit).pow(tz) - 1);

        let q_dash = q >> tz as usize;

        let qinv_dash = mod_inv1(q_dash);
        *x >>= tz as usize;

        let r_dash = remainder_b(&*x, q_dash, qinv_dash);

        quotient_odd(x, r_dash, q_dash, qinv_dash);

        (r_dash << tz as usize) + bsave
    }
}

/// Calculate the remainder of `x / q`.
/// The quotient will be returned.
pub fn rem_digit(x: &BigUint, q: BigDigit) -> BigDigit {
    if x.is_zero() {
        return 0;
    }
    if x.data.len() == 1 {
        return x.data[0] % q;
    }

    if q & 1 == 1 {
        let qinv = mod_inv1(q);
        remainder_odd(&x, q, qinv)
    } else {
        let tz = q.trailing_zeros();
        let bsave = x.data[0] & ((2 as BigDigit).pow(tz) - 1);

        let q_dash = q >> tz as usize;

        let qinv_dash = mod_inv1(q_dash);
        let x_dash = x >> tz as usize;

        let r_dash = remainder_odd(&x_dash, q_dash, qinv_dash);

        (r_dash << tz as usize) + bsave
    }
}

/// Calculate the quotient of `x / q`.
/// The quotient will be in `x`.
pub fn div_digit(x: &mut BigUint, q: BigDigit) {
    if x.is_zero() {
        return;
    }

    if x.data.len() == 1 {
        x.data[0] /= q;
        x.normalize();
        return;
    }

    if q & 1 == 1 {
        let qinv = mod_inv1(q);
        let r = remainder_odd(&*x, q, qinv);

        quotient_odd(x, r, q, qinv);
    } else {
        let tz = q.trailing_zeros() as usize;

        let q_dash = q >> tz;
        let qinv_dash = mod_inv1(q_dash);
        *x >>= tz;

        let r_dash = remainder_odd(&*x, q_dash, qinv_dash);

        quotient_odd(x, r_dash, q_dash, qinv_dash);
    }
}

fn quotient_odd(x: &mut BigUint, r: BigDigit, q: BigDigit, qinv: BigDigit) {
    let mut bw = 0;
    let mut cy = r;

    for xi in x.data.iter_mut() {
        let mut tmp = xi.wrapping_sub(bw).wrapping_sub(cy);
        bw = (tmp > *xi) as BigDigit;
        tmp = tmp.wrapping_mul(qinv);
        cy = umulh(tmp, q);

        *xi = tmp
    }

    debug_assert!(cy == 0, "cy: {} != 0", cy);
    x.normalize()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::biguint::IntoBigUint;
    use crate::traits::ModInverse;

    use num_traits::{FromPrimitive, Pow, ToPrimitive};
    use std::str::FromStr;

    #[test]
    fn test_is_even() {
        assert!(is_even(10));
        assert!(!is_even(11));
    }

    #[test]
    fn test_mont_mul() {
        let x = 10;
        let y = 40;
        let q = 13;
        let qinv = mod_inv1(q);

        let res = mont_mul(x, y, q, qinv);
        let r = 2u128.pow(big_digit::BITS as u32);
        let rinv = r
            .into_biguint()
            .unwrap()
            .mod_inverse(BigUint::from(q))
            .unwrap()
            .into_biguint()
            .unwrap();
        let expected = ((BigUint::from(x) * BigUint::from(y) * rinv) % q)
            .to_u64()
            .unwrap();

        assert_eq!(res, expected);
    }

    #[test]
    fn test_mont_sqr() {
        let x = 1234;
        let q = 13;
        let qinv = mod_inv1(q);

        assert_eq!(mont_sqr(x, q, qinv), mont_mul(x, x, q, qinv),);
    }

    #[test]
    fn test_mmul_one() {
        let x = 1234;
        let q = 13;
        let qinv = mod_inv1(q);

        assert_eq!(mmul_one(x, q, qinv), mont_mul(x, 1, q, qinv));
    }

    #[test]
    #[cfg(feature = "u64_digit")]
    fn test_remainder_a_example() {
        let x: BigUint = (BigUint::from_u64(2).unwrap().pow(977u32)) - 1u32;
        let q = 16357897499336320049;
        let qinv = mod_inv1(q);

        assert_eq!(remainder_a(&x, q, qinv), 8623243291871090711);
    }

    #[test]
    #[cfg(feature = "u64_digit")]
    fn test_remainder_a_u2_example() {
        let x: BigUint = (BigUint::from_u64(2).unwrap().pow(977u32)) - 1u32;
        let q = 16357897499336320049;
        let qinv = mod_inv1(q);

        assert_eq!(remainder_a_u2(&x, q, qinv), 8623243291871090711);
    }

    #[test]
    #[cfg(feature = "u64_digit")]
    fn test_remainder_b_example() {
        let x: BigUint = (BigUint::from_u64(2).unwrap().pow(977u32)) - 1u32;
        let q = 16357897499336320049;
        let qinv = mod_inv1(q);

        assert_eq!(remainder_b(&x, q, qinv), 8623243291871090711);
    }

    #[test]
    #[cfg(feature = "u64_digit")]
    fn test_radix_power_example() {
        let q = 16357897499336320049;
        let qinv = mod_inv1(q);

        // Algorithm A:
        let (j, p, bm) = calc_bitmap(17);
        let pow = radix_power(17, j, p, bm, q, qinv);

        let r17 = 8502984233828494641;
        assert_eq!(&pow, &r17);
    }

    #[test]
    fn test_remainder_odd() {
        let x: BigUint = (BigUint::from_u64(2).unwrap().pow(977u32)) - 1u32;
        let q = 16357897499336320049;
        let qinv = mod_inv1(q);

        let expected = 8623243291871090711u64;
        let result = remainder_odd(&x, q, qinv);

        assert_eq!(expected, result);
    }

    #[test]
    fn test_quotient_odd() {
        let mut x: BigUint = (BigUint::from_u64(2).unwrap().pow(977u32)) - 1u32;
        let q = 16357897499336320049;
        let qinv = mod_inv1(q);

        let rem = remainder_odd(&x, q, qinv);
        quotient_odd(&mut x, rem, q, qinv);
        let expected = BigUint::from_str("78086917842225469457022075217415018633622146158582987787805457927845552003930951370242413093007381680736663345444780010948879462256334087427082857530164140957807257857039967815743361429510512762352923129675520587113443817607507240658518046987342885964515476672818868436366440").unwrap();

        assert_eq!(x, expected);
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_div_rem_digit() {
        use rand::{thread_rng, Rng};
        let mut rng = thread_rng();

        for _ in 1..1000 {
            let x_orig: BigDigit = rng.gen();
            let mut x: BigUint = x_orig.into();
            let q: BigDigit = rng.gen();

            let rem = div_rem_digit(&mut x, q);
            assert_eq!(x_orig % q, rem);
            assert_eq!(x_orig / q, x.to_u64().unwrap());
        }
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_remainder_odd_range() {
        use rand::{thread_rng, Rng};
        let mut rng = thread_rng();

        for _ in 1..1000 {
            let x_orig: BigDigit = rng.gen();
            let mut x: BigUint = x_orig.into();
            let mut q: BigDigit = rng.gen();
            // make q odd
            q |= 1;
            let qinv = mod_inv1(q);

            let rem = remainder_odd(&x, q, qinv);
            assert_eq!(x_orig % q, rem);
        }
    }
}
