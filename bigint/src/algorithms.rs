use std::borrow::Cow;
use std::cmp;
use std::cmp::Ordering::{self, Less, Greater, Equal};
use std::iter::repeat;
use std::mem;
use traits;
use traits::{Zero, One};

use biguint::BigUint;

use bigint::BigInt;
use bigint::Sign;
use bigint::Sign::{Minus, NoSign, Plus};

#[allow(non_snake_case)]
pub mod big_digit {
    /// A `BigDigit` is a `BigUint`'s composing element.
    pub type BigDigit = u32;

    /// A `DoubleBigDigit` is the internal type used to do the computations.  Its
    /// size is the double of the size of `BigDigit`.
    pub type DoubleBigDigit = u64;

    pub const ZERO_BIG_DIGIT: BigDigit = 0;

    // `DoubleBigDigit` size dependent
    pub const BITS: usize = 32;

    pub const BASE: DoubleBigDigit = 1 << BITS;
    const LO_MASK: DoubleBigDigit = (-1i32 as DoubleBigDigit) >> BITS;

    #[inline]
    fn get_hi(n: DoubleBigDigit) -> BigDigit {
        (n >> BITS) as BigDigit
    }
    #[inline]
    fn get_lo(n: DoubleBigDigit) -> BigDigit {
        (n & LO_MASK) as BigDigit
    }

    /// Split one `DoubleBigDigit` into two `BigDigit`s.
    #[inline]
    pub fn from_doublebigdigit(n: DoubleBigDigit) -> (BigDigit, BigDigit) {
        (get_hi(n), get_lo(n))
    }

    /// Join two `BigDigit`s into one `DoubleBigDigit`
    #[inline]
    pub fn to_doublebigdigit(hi: BigDigit, lo: BigDigit) -> DoubleBigDigit {
        (lo as DoubleBigDigit) | ((hi as DoubleBigDigit) << BITS)
    }
}

use big_digit::{BigDigit, DoubleBigDigit};

// Generic functions for add/subtract/multiply with carry/borrow:

// Add with carry:
#[inline]
fn adc(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit((a as DoubleBigDigit) + (b as DoubleBigDigit) +
                                                  (*carry as DoubleBigDigit));

    *carry = hi;
    lo
}

// Subtract with borrow:
#[inline]
fn sbb(a: BigDigit, b: BigDigit, borrow: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit(big_digit::BASE + (a as DoubleBigDigit) -
                                                  (b as DoubleBigDigit) -
                                                  (*borrow as DoubleBigDigit));
    // hi * (base) + lo == 1*(base) + ai - bi - borrow
    // => ai - bi - borrow < 0 <=> hi == 0
    *borrow = (hi == 0) as BigDigit;
    lo
}

#[inline]
pub fn mac_with_carry(a: BigDigit, b: BigDigit, c: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit((a as DoubleBigDigit) +
                                                  (b as DoubleBigDigit) * (c as DoubleBigDigit) +
                                                  (*carry as DoubleBigDigit));
    *carry = hi;
    lo
}

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, carry: &mut BigDigit) -> BigDigit {
    let (hi, lo) = big_digit::from_doublebigdigit((a as DoubleBigDigit) * (b as DoubleBigDigit) +
                                                  (*carry as DoubleBigDigit));

    *carry = hi;
    lo
}

/// Divide a two digit numerator by a one digit divisor, returns quotient and remainder:
///
/// Note: the caller must ensure that both the quotient and remainder will fit into a single digit.
/// This is _not_ true for an arbitrary numerator/denominator.
///
/// (This function also matches what the x86 divide instruction does).
#[inline]
fn div_wide(hi: BigDigit, lo: BigDigit, divisor: BigDigit) -> (BigDigit, BigDigit) {
    debug_assert!(hi < divisor);

    let lhs = big_digit::to_doublebigdigit(hi, lo);
    let rhs = divisor as DoubleBigDigit;
    ((lhs / rhs) as BigDigit, (lhs % rhs) as BigDigit)
}

pub fn div_rem_digit(mut a: BigUint, b: BigDigit) -> (BigUint, BigDigit) {
    let mut rem = 0;

    for d in a.data.iter_mut().rev() {
        let (q, r) = div_wide(rem, *d, b);
        *d = q;
        rem = r;
    }

    (a.normalized(), rem)
}

// Only for the Add impl:
#[must_use]
#[inline]
pub fn __add2(a: &mut [BigDigit], b: &[BigDigit]) -> BigDigit {
    debug_assert!(a.len() >= b.len());

    let mut carry = 0;
    let (a_lo, a_hi) = a.split_at_mut(b.len());

    for (a, b) in a_lo.iter_mut().zip(b) {
        *a = adc(*a, *b, &mut carry);
    }

    if carry != 0 {
        for a in a_hi {
            *a = adc(*a, 0, &mut carry);
            if carry == 0 { break }
        }
    }

    carry
}

/// /Two argument addition of raw slices:
/// a += b
///
/// The caller _must_ ensure that a is big enough to store the result - typically this means
/// resizing a to max(a.len(), b.len()) + 1, to fit a possible carry.
pub fn add2(a: &mut [BigDigit], b: &[BigDigit]) {
    let carry = __add2(a, b);

    debug_assert!(carry == 0);
}

pub fn sub2(a: &mut [BigDigit], b: &[BigDigit]) {
    let mut borrow = 0;

    let len = cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at_mut(len);
    let (b_lo, b_hi) = b.split_at(len);

    for (a, b) in a_lo.iter_mut().zip(b_lo) {
        *a = sbb(*a, *b, &mut borrow);
    }

    if borrow != 0 {
        for a in a_hi {
            *a = sbb(*a, 0, &mut borrow);
            if borrow == 0 { break }
        }
    }

    // note: we're _required_ to fail on underflow
    assert!(borrow == 0 && b_hi.iter().all(|x| *x == 0),
            "Cannot subtract b from a because b is larger than a.");
}

pub fn sub2rev(a: &[BigDigit], b: &mut [BigDigit]) {
    debug_assert!(b.len() >= a.len());

    let mut borrow = 0;

    let len = cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at(len);
    let (b_lo, b_hi) = b.split_at_mut(len);

    for (a, b) in a_lo.iter().zip(b_lo) {
        *b = sbb(*a, *b, &mut borrow);
    }

    assert!(a_hi.is_empty());

    // note: we're _required_ to fail on underflow
    assert!(borrow == 0 && b_hi.iter().all(|x| *x == 0),
            "Cannot subtract b from a because b is larger than a.");
}

pub fn sub_sign(a: &[BigDigit], b: &[BigDigit]) -> (Sign, BigUint) {
    // Normalize:
    let a = &a[..a.iter().rposition(|&x| x != 0).map_or(0, |i| i + 1)];
    let b = &b[..b.iter().rposition(|&x| x != 0).map_or(0, |i| i + 1)];

    match cmp_slice(a, b) {
        Greater => {
            let mut a = a.to_vec();
            sub2(&mut a, b);
            (Plus, BigUint::new(a))
        }
        Less => {
            let mut b = b.to_vec();
            sub2(&mut b, a);
            (Minus, BigUint::new(b))
        }
        _ => (NoSign, Zero::zero()),
    }
}

/// Three argument multiply accumulate:
/// acc += b * c
fn mac_digit(acc: &mut [BigDigit], b: &[BigDigit], c: BigDigit) {
    if c == 0 {
        return;
    }

    let mut b_iter = b.iter();
    let mut carry = 0;

    for ai in acc.iter_mut() {
        if let Some(bi) = b_iter.next() {
            *ai = mac_with_carry(*ai, *bi, c, &mut carry);
        } else if carry != 0 {
            *ai = mac_with_carry(*ai, 0, c, &mut carry);
        } else {
            break;
        }
    }

    assert!(carry == 0);
}

/// Three argument multiply accumulate:
/// acc += b * c
fn mac3(acc: &mut [BigDigit], b: &[BigDigit], c: &[BigDigit]) {
    let (x, y) = if b.len() < c.len() {
        (b, c)
    } else {
        (c, b)
    };

    // Karatsuba multiplication is slower than long multiplication for small x and y:
    //
    if x.len() <= 4 {
        for (i, xi) in x.iter().enumerate() {
            mac_digit(&mut acc[i..], y, *xi);
        }
    } else if y.len() <= 0 {
        /*
         * Karatsuba multiplication:
         *
         * The idea is that we break x and y up into two smaller numbers that each have about half
         * as many digits, like so (note that multiplying by b is just a shift):
         *
         * x = x0 + x1 * b
         * y = y0 + y1 * b
         *
         * With some algebra, we can compute x * y with three smaller products, where the inputs to
         * each of the smaller products have only about half as many digits as x and y:
         *
         * x * y = (x0 + x1 * b) * (y0 + y1 * b)
         *
         * x * y = x0 * y0
         *       + x0 * y1 * b
         *       + x1 * y0 * b
         *       + x1 * y1 * b^2
         *
         * Let p0 = x0 * y0 and p2 = x1 * y1:
         *
         * x * y = p0
         *       + (x0 * y1 + x1 * y0) * b
         *       + p2 * b^2
         *
         * The real trick is that middle term:
         *
         *         x0 * y1 + x1 * y0
         *
         *       = x0 * y1 + x1 * y0 - p0 + p0 - p2 + p2
         *
         *       = x0 * y1 + x1 * y0 - x0 * y0 - x1 * y1 + p0 + p2
         *
         * Now we complete the square:
         *
         *       = -(x0 * y0 - x0 * y1 - x1 * y0 + x1 * y1) + p0 + p2
         *
         *       = -((x1 - x0) * (y1 - y0)) + p0 + p2
         *
         * Let p1 = (x1 - x0) * (y1 - y0), and substitute back into our original formula:
         *
         * x * y = p0
         *       + (p0 + p2 - p1) * b
         *       + p2 * b^2
         *
         * Where the three intermediate products are:
         *
         * p0 = x0 * y0
         * p1 = (x1 - x0) * (y1 - y0)
         * p2 = x1 * y1
         *
         * In doing the computation, we take great care to avoid unnecessary temporary variables
         * (since creating a BigUint requires a heap allocation): thus, we rearrange the formula a
         * bit so we can use the same temporary variable for all the intermediate products:
         *
         * x * y = p2 * b^2 + p2 * b
         *       + p0 * b + p0
         *       - p1 * b
         *
         * The other trick we use is instead of doing explicit shifts, we slice acc at the
         * appropriate offset when doing the add.
         */

        /*
         * When x is smaller than y, it's significantly faster to pick b such that x is split in
         * half, not y:
         */
        let b = x.len() / 2;
        let (x0, x1) = x.split_at(b);
        let (y0, y1) = y.split_at(b);

        /*
         * We reuse the same BigUint for all the intermediate multiplies and have to size p
         * appropriately here: x1.len() >= x0.len and y1.len() >= y0.len():
         */
        let len = x1.len() + y1.len() + 1;
        let mut p = BigUint { data: vec![0; len] };

        // p2 = x1 * y1
        mac3(&mut p.data[..], x1, y1);

        // Not required, but the adds go faster if we drop any unneeded 0s from the end:
        p.normalize();

        add2(&mut acc[b..],        &p.data[..]);
        add2(&mut acc[b * 2..],    &p.data[..]);

        // Zero out p before the next multiply:
        p.data.truncate(0);
        p.data.extend(repeat(0).take(len));

        // p0 = x0 * y0
        mac3(&mut p.data[..], x0, y0);
        p.normalize();

        add2(&mut acc[..],         &p.data[..]);
        add2(&mut acc[b..],        &p.data[..]);

        // p1 = (x1 - x0) * (y1 - y0)
        // We do this one last, since it may be negative and acc can't ever be negative:
        let (j0_sign, j0) = sub_sign(x1, x0);
        let (j1_sign, j1) = sub_sign(y1, y0);

        match j0_sign * j1_sign {
            Plus    => {
                p.data.truncate(0);
                p.data.extend(repeat(0).take(len));

                mac3(&mut p.data[..], &j0.data[..], &j1.data[..]);
                p.normalize();

                sub2(&mut acc[b..], &p.data[..]);
            },
            Minus   => {
                mac3(&mut acc[b..], &j0.data[..], &j1.data[..]);
            },
            NoSign  => (),
        }

    } else {
        let i = y.len()/3 + 1;

        let x0_len = cmp::min(x.len(), i);
        let x1_len = cmp::min(x.len() - x0_len, i);

        let y0_len = i;
        let y1_len = cmp::min(y.len() - y0_len, i);

        let x0 = BigInt::from_slice(Plus, &x[..x0_len]);
        let x1 = BigInt::from_slice(Plus, &x[x0_len..x0_len + x1_len]);
        let x2 = BigInt::from_slice(Plus, &x[x0_len + x1_len..]);

        let y0 = BigInt::from_slice(Plus, &y[..y0_len]);
        let y1 = BigInt::from_slice(Plus, &y[y0_len..y0_len + y1_len]);
        let y2 = BigInt::from_slice(Plus, &y[y0_len + y1_len..]);

        let r0 = &x0 * &y0;
        let r1 = (&x0 + &x1 + &x2) * (&y0 + &y1 + &y2);
        let r2 = (&x0 - &x1 + &x2) * (&y0 - &y1 + &y2);
        let r3 = (&x0 - &x1*2 + &x2*4) * (&y0 - &y1*2 + &y2*4);
        let r4 = &x2 * &y2;

        let comp0: BigInt = r0.clone();
        let comp4: BigInt = r4.clone();
        let mut comp3: BigInt = (&r3 - &r1) / 3;
        let mut comp1: BigInt = (&r1 - &r2) / 2;
        let mut comp2: BigInt = &r2 - &r0;
        comp3 = (&comp2 - &comp3)/2 + &r4*2;
        comp2 = comp2 + &comp1 - &comp4;
        comp1 = comp1 - &comp3;

        let result = comp0 + (comp1 << 32*i) + (comp2 << 2*32*i) + (comp3 << 3*32*i) + (comp4 << 4*32*i);
        assert!(result.sign != Minus);
        add2(&mut acc[..], &result.data.data);

        // add2(&mut acc[..], &comp0.data.data);
        // add2(&mut acc[4*i..], &comp4.data.data);
        //
        // match (comp1.sign, comp2.sign, comp3.sign) {
        //     (Minus, Minus, Minus) => {
        //         for _ in 0..i {
        //             comp1.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp1.data.data);
        //
        //         for _ in 0..2*i {
        //             comp2.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp2.data.data);
        //
        //         for _ in 0..3*i {
        //             comp3.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp3.data.data);
        //     },
        //
        //     (Minus, Minus, _) => {
        //         add2(&mut acc[3*i..], &comp3.data.data);
        //         for _ in 0..i {
        //             comp1.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp1.data.data);
        //         for _ in 0..2*i {
        //             comp2.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp2.data.data);
        //     },
        //
        //     (Minus, _, Minus) => {
        //         add2(&mut acc[2*i..], &comp2.data.data);
        //         for _ in 0..i {
        //             comp1.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp1.data.data);
        //         for _ in 0..3*i {
        //             comp3.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp3.data.data);
        //     },
        //
        //     (_, Minus, Minus) => {
        //         add2(&mut acc[i..], &comp1.data.data);
        //         for _ in 0..2*i {
        //             comp2.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp2.data.data);
        //         for _ in 0..3*i {
        //             comp3.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp3.data.data);
        //     },
        //
        //     (Minus, _, _) => {
        //         add2(&mut acc[2*i..], &comp2.data.data);
        //         add2(&mut acc[3*i..], &comp3.data.data);
        //         for _ in 0..i {
        //             comp1.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp1.data.data);
        //     },
        //
        //     (_, Minus, _) => {
        //         add2(&mut acc[i..], &comp1.data.data);
        //         add2(&mut acc[3*i..], &comp3.data.data);
        //         for _ in 0..2*i {
        //             comp2.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp2.data.data);
        //     },
        //
        //     (_, _, Minus) => {
        //         add2(&mut acc[i..], &comp1.data.data);
        //         add2(&mut acc[2*i..], &comp2.data.data);
        //         for _ in 0..3*i {
        //             comp3.data.data.insert(0, 0);
        //         }
        //         sub2(&mut acc[..], &comp3.data.data);
        //     },
        //
        //     _ => {
        //         add2(&mut acc[i..], &comp1.data.data);
        //         add2(&mut acc[2*i..], &comp2.data.data);
        //         add2(&mut acc[3*i..], &comp3.data.data);
        //     }
        // }

        // let mut r0 = BigUint{ data: vec![0; 2*i + 1] };
        // mac3(&mut r0.data, &x0, &y0);
        // r0.normalize();
        //
        // let mut r1 = BigUint{ data: vec![0; 2*(i+2) + 1] };
        // p.data.assign_from_slice(&x0);
        // p.data.data.extend_from_slice(&[0, 0]);
        // add2(&mut p.data.data, &x1);
        // add2(&mut p.data.data, &x2);
        // q.data.assign_from_slice(&y0);
        // q.data.data.extend_from_slice(&[0, 0]);
        // add2(&mut q.data.data, &y1);
        // add2(&mut q.data.data, &y2);
        // mac3(&mut r1.data, &p.data.data, &q.data.data);
        // r1.normalize();
        //
        // let mut r2 = BigUint{ data: vec![0; 2*(i+1) + 1] };
        // p.data.assign_from_slice(&x0);
        // p.data.data.extend_from_slice(&[0, 0]);
        // add2(&mut p.data, &x2);
        // p = p - BigInt::from_biguint(Plus, BigUint::from_slice(&x1));
        // q.data.assign_from_slice(&y0);
        // q.data.data.extend_from_slice(&[0, 0]);
        // add2(&mut q.data, &y2);
        // q = q - BigInt::from_biguint(Plus, BigUint::from_slice(&y1));
        // mac3(&mut r2.data, &p.data, &q.data);
        // r2.normalize();
        // let r2_sign = p_sign * q_sign;
        //
        // let mut r3 = BigUint{ data: vec![0; 2*(i+2) + 1] };
        // p.assign_from_slice(&x0);
        // p.data.extend_from_slice(&[0, 0]);
        // let mut temp = BigUint { data: Vec::with_capacity(i + 1) };
        // temp.assign_from_slice(&x2);
        // temp = temp * 4_u32;
        // add2(&mut p.data, &temp.data);
        // temp.assign_from_slice(&x1);
        // temp = temp * 2_u32;
        // if p.data[i] == 0 && p.data[..i].iter().rev().lt(temp.data.iter().rev()) {
        //     p_sign = Minus;
        //     let p_temp = p.clone();
        //     p.assign_from_slice(&temp.data);
        //     sub2(&mut p.data, &p_temp.data);
        // } else {
        //     p_sign = Plus;
        //     sub2(&mut p.data, &temp.data);
        // }
        // q.assign_from_slice(&y0);
        // q.data.extend_from_slice(&[0, 0]);
        // temp.assign_from_slice(&y2);
        // temp = temp * 4_u32;
        // add2(&mut q.data, &temp.data);
        // temp.assign_from_slice(&y1);
        // temp = temp * 2_u32;
        // if q.data[i] == 0 && q.data[..i].iter().rev().lt(temp.data.iter().rev()) {
        //     q_sign = Minus;
        //     let q_temp = q.clone();
        //     q.assign_from_slice(&temp.data);
        //     sub2(&mut q.data, &q_temp.data);
        // } else {
        //     q_sign = Plus;
        //     sub2(&mut q.data, &temp.data);
        // }
        // mac3(&mut r3.data, &p.data, &q.data);
        // r3.normalize();
        // let r3_sign = p_sign * q_sign;
        //
        // let mut r4 = BigUint{ data: vec![0; 2*i + 1] };
        // mac3(&mut r4.data, &x2, &y2);
        // r4.normalize();
        //
        // let signed_r0 = BigInt::from_biguint(Plus, r0);
        // let signed_r1 = BigInt::from_biguint(Plus, r1);
        // let signed_r2 = BigInt::from_biguint(r2_sign, r2);
        // let signed_r3 = BigInt::from_biguint(r3_sign, r3);
        // let signed_r4 = BigInt::from_biguint(Plus, r4);
        //
        // let comp0 = signed_r0.clone();
        // let comp4 = signed_r4.clone();
        // let mut comp3: BigInt = (&signed_r3 - &signed_r1) / 3;
        // let mut comp1: BigInt = (&signed_r1 - &signed_r2) / 2;
        // let mut comp2 = &signed_r2 - &signed_r0;
        // comp3 = ((&comp2 - &comp3) / 2) + (&signed_r4 * 2);
        // comp2 = comp2 + &comp1 - &comp4;
        // comp1 = comp1 - &comp3;
        //
        // add2(&mut acc[..], &comp0.data.data);
        // add2(&mut acc[i..], &comp1.data.data);
        // add2(&mut acc[2*i..], &comp2.data.data);
        // add2(&mut acc[3*i..], &comp3.data.data);
        // add2(&mut acc[4*i..], &comp4.data.data);
    }
}

pub fn mul3(x: &[BigDigit], y: &[BigDigit]) -> BigUint {
    let len = x.len() + y.len() + 1;
    let mut prod = BigUint { data: vec![0; len] };

    mac3(&mut prod.data[..], x, y);
    prod.normalized()
}

pub fn scalar_mul(a: &mut [BigDigit], b: BigDigit) -> BigDigit {
    let mut carry = 0;
    for a in a.iter_mut() {
        *a = mul_with_carry(*a, b, &mut carry);
    }
    carry
}

pub fn div_rem(u: &BigUint, d: &BigUint) -> (BigUint, BigUint) {
    if d.is_zero() {
        panic!()
    }
    if u.is_zero() {
        return (Zero::zero(), Zero::zero());
    }
    if *d == One::one() {
        return (u.clone(), Zero::zero());
    }

    // Required or the q_len calculation below can underflow:
    match u.cmp(d) {
        Less => return (Zero::zero(), u.clone()),
        Equal => return (One::one(), Zero::zero()),
        Greater => {} // Do nothing
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
    let mut q = BigUint { data: vec![0; q_len] };

    // We reuse the same temporary to avoid hitting the allocator in our inner loop - this is
    // sized to hold a0 (in the common case; if a particular digit of the quotient is zero a0
    // can be bigger).
    //
    let mut tmp = BigUint { data: Vec::with_capacity(2) };

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
        let mut a0 = tmp;
        a0.data.truncate(0);
        a0.data.extend(a.data[offset..].iter().cloned());

        /*
         * q0 << j * big_digit::BITS is our actual quotient estimate - we do the shifts
         * implicitly at the end, when adding and subtracting to a and q. Not only do we
         * save the cost of the shifts, the rest of the arithmetic gets to work with
         * smaller numbers.
         */
        let (mut q0, _) = div_rem_digit(a0, bn);
        let mut prod = &b * &q0;

        while cmp_slice(&prod.data[..], &a.data[j..]) == Greater {
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

/// Find last set bit
/// fls(0) == 0, fls(u32::MAX) == 32
pub fn fls<T: traits::PrimInt>(v: T) -> usize {
    mem::size_of::<T>() * 8 - v.leading_zeros() as usize
}

pub fn ilog2<T: traits::PrimInt>(v: T) -> usize {
    fls(v) - 1
}

#[inline]
pub fn biguint_shl(n: Cow<BigUint>, bits: usize) -> BigUint {
    let n_unit = bits / big_digit::BITS;
    let mut data = match n_unit {
        0 => n.into_owned().data,
        _ => {
            let len = n_unit + n.data.len() + 1;
            let mut data = Vec::with_capacity(len);
            data.extend(repeat(0).take(n_unit));
            data.extend(n.data.iter().cloned());
            data
        }
    };

    let n_bits = bits % big_digit::BITS;
    if n_bits > 0 {
        let mut carry = 0;
        for elem in data[n_unit..].iter_mut() {
            let new_carry = *elem >> (big_digit::BITS - n_bits);
            *elem = (*elem << n_bits) | carry;
            carry = new_carry;
        }
        if carry != 0 {
            data.push(carry);
        }
    }

    BigUint::new(data)
}

#[inline]
pub fn biguint_shr(n: Cow<BigUint>, bits: usize) -> BigUint {
    let n_unit = bits / big_digit::BITS;
    if n_unit >= n.data.len() {
        return Zero::zero();
    }
    let mut data = match n_unit {
        0 => n.into_owned().data,
        _ => n.data[n_unit..].to_vec(),
    };

    let n_bits = bits % big_digit::BITS;
    if n_bits > 0 {
        let mut borrow = 0;
        for elem in data.iter_mut().rev() {
            let new_borrow = *elem << (big_digit::BITS - n_bits);
            *elem = (*elem >> n_bits) | borrow;
            borrow = new_borrow;
        }
    }

    BigUint::new(data)
}

pub fn cmp_slice(a: &[BigDigit], b: &[BigDigit]) -> Ordering {
    debug_assert!(a.last() != Some(&0));
    debug_assert!(b.last() != Some(&0));

    let (a_len, b_len) = (a.len(), b.len());
    if a_len < b_len {
        return Less;
    }
    if a_len > b_len {
        return Greater;
    }

    for (&ai, &bi) in a.iter().rev().zip(b.iter().rev()) {
        if ai < bi {
            return Less;
        }
        if ai > bi {
            return Greater;
        }
    }
    return Equal;
}

#[cfg(test)]
mod algorithm_tests {
    use {BigDigit, BigUint, BigInt};
    use Sign::Plus;
    use traits::Num;

    #[test]
    fn test_sub_sign() {
        use super::sub_sign;

        fn sub_sign_i(a: &[BigDigit], b: &[BigDigit]) -> BigInt {
            let (sign, val) = sub_sign(a, b);
            BigInt::from_biguint(sign, val)
        }

        let a = BigUint::from_str_radix("265252859812191058636308480000000", 10).unwrap();
        let b = BigUint::from_str_radix("26525285981219105863630848000000", 10).unwrap();
        let a_i = BigInt::from_biguint(Plus, a.clone());
        let b_i = BigInt::from_biguint(Plus, b.clone());

        assert_eq!(sub_sign_i(&a.data[..], &b.data[..]), &a_i - &b_i);
        assert_eq!(sub_sign_i(&b.data[..], &a.data[..]), &b_i - &a_i);
    }
}
