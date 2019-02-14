use std::cmp::Ordering;

use bit_field::BitField;
use integer::Integer;
use num_traits::{One, Pow, Zero};
use smallvec::SmallVec;

use crate::algorithms::{
    __add2, __add_scalar, __mul3, __sub2, add2, cmp_slice, mod_inv1, mul_hi, mul_lo, sub2,
};
use crate::big_digit::{self, BigDigit, DoubleBigDigit};
use crate::BigUint;

/// 2**54
const TWO54FLOAT: f64 = 1.0 * 0x08000000 as f64 * 0x08000000 as f64;

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

    div_rem_mont(u, d)
}

fn div_rem_mont(x: &BigUint, y: &BigUint) -> (BigUint, BigUint) {
    let len_x = x.data.len();
    if len_x == y.data.len() {
        // First attempt at fast-mod based on FP approximation of the quotient `x/y`,
        // which switches to binary for `x/y > 2**53`.

        let (lo, i) = get_leading_bits(x);
        let (itmp, j) = get_leading_bits(y);
        let bw = 1u64.wrapping_shl(i.wrapping_sub(j) as u32);
        let ncmax = 16;

        // Power-of-2 sacaling needed on ratio of left justified leading bits.
        // TODO: Use FloatBigDigit
        let fquo = (bw as f64) * (lo as f64 / itmp as f64);

        // NOTE: only needed when calculating the remainder.
        if fquo < TWO54FLOAT {
            let mut itmp = fquo as BigDigit;
            let yinv = y * &itmp;
            let mut r = x.clone();
            let bw = __sub2(&mut r.data, &yinv.data);
            r.normalize();

            // If `bw == true` we need an additional correction, `+= y`.
            // nc tracks the number of correction steps needed
            let mut nc = 0;
            if bw {
                while (nc < ncmax) && y < &r {
                    nc += 1;
                    __add2(&mut r.data, &y.data);

                    // decr quotient by 1 to account for extra add-y
                    itmp -= 1;
                }
            } else {
                while (nc < ncmax) && &r > y {
                    nc += 1;
                    __sub2(&mut r.data, &y.data);

                    // inc quotient by 1 for extra sub-y
                    itmp += 1;
                }
            }

            debug_assert!(nc < ncmax);
            debug_assert!(&r < y, "remainder should be less than the modulus");

            return (itmp.into(), r.into());
        }

        return div_rem_binary(x, y);
    }

    // Modulus must be odd for Montgomery.
    let nshift = y.trailing_zeros() as usize;

    let x_adj: BigUint;
    let y_adj: BigUint;
    let mut rem_save = BigUint::zero();

    let (v, w) = if nshift > 0 {
        let nws = (nshift + big_digit::BITS - 1) >> 6; // TODO: adjust for 32bit
        let nbs = nshift & (big_digit::BITS - 1);

        // Save the bottom nshifts of x
        let mask = (-1i64 as BigDigit) >> (big_digit::BITS - nbs);
        rem_save.data.extend_from_slice(&x.data[..nws]);
        rem_save.data[nws - 1] &= mask;

        x_adj = x >> nshift;
        y_adj = y >> nshift;

        (&x_adj, &y_adj)
    } else {
        (x, y)
    };

    // Short cut for single odd-component divisor.
    if w.data.len() == 1 {
        let mut q = v.clone();
        let mut rem: BigUint = div_rem_digit(&mut q, w.data[0]).into();

        // Restore for the even case
        if nshift > 0 {
            rem <<= nshift;
            __add2(&mut rem.data, &rem_save.data);
        }

        return (q, rem);
    }

    // The actual core of this function.

    // We require a modular inverse of w for modmul using montgomery.
    let winv = mod_invn(w);
    println!(
        "yinv = {}",
        BigUint {
            data: winv.data.clone()
        }
    );

    // Process `v` in `w` len sized chunks. If the last chunk does not fit properly it gets special handling at the end.

    let v_len = v.data.len();
    let w_len = w.data.len();
    // lo: [..w_len], hi: [w_len..]
    let mut lohi = vec![0; 2 * w_len];

    for i in (0..(v_len - w_len + 1)).step_by(w_len) {
        println!(
            "i = {}; v = {}",
            i,
            BigUint {
                data: (&v.data[i..i + w_len]).into()
            }
        );
        let mut tmp = v.data[i..i + w_len].to_vec();
        let bw = __sub2(&mut tmp, &lohi[w_len..]);

        // Montgomery mul step: cy = UMULH(w, MULL(tmp, yinv))
        lohi[..w_len].copy_from_slice(&tmp);
        mul_lo(
            &mut lohi[..w_len],
            &winv.data[..std::cmp::min(winv.data.len(), w_len)],
            w_len,
        );

        println!(
            "MULL = {}",
            BigUint {
                data: (&lohi[..w_len]).to_vec().into()
            }
            .normalized()
        );

        assert!(__add_scalar(&mut tmp, bw as BigDigit) == 0);

        // lo:hi = MUL_LOHI(w, tmp)
        let tmp = __mul3(&lohi[..w_len], &w.data);
        let cl = std::cmp::min(tmp.len(), lohi.len());
        lohi[..cl].copy_from_slice(&tmp[..cl]);
        println!(
            "  lo = {}",
            BigUint {
                data: (&lohi[..w_len]).to_vec().into()
            }
            .normalized()
        );
        println!(
            "  hi = {}",
            BigUint {
                data: (&lohi[w_len..]).to_vec().into()
            }
            .normalized()
        );
    }

    // Special handling for the last term.
    let i = v_len - w_len + 1;
    let j = v_len - i;
    let mut cy = BigUint {
        data: smallvec![0; w_len],
    };

    if j > 0 {
        // Zero pad the last element from v into cy.
        cy.data[..j].copy_from_slice(&v.data[i..]);

        let bw = __sub2(&mut cy.data, &lohi[w_len..]);
        if bw {
            __add2(&mut cy.data, &w.data);
        }
    } else {
        cy.data.copy_from_slice(&lohi[..w_len]);
    }

    println!("MR = {:?}", &cy.data[..]);

    // Transform back out of Montgomery space.
    //   calculate R**w_len
    let basepow = radix_power_n(w_len, &w, &winv);
    println!("r**{} = {}", w_len, &basepow);
    //  multiply the residue in `cy` with `basepow`
    let mut cy = mont_mul_n(&cy, &basepow, &w, &winv);

    println!("remainder = {}", &cy);

    // Calculate quotient, now that we have the remainder.
    let mut q = smallvec![0; 2 * w_len];
    let cl = std::cmp::min(cy.data.len(), w_len);
    lohi[w_len..w_len + cl].copy_from_slice(&cy.data[..cl]);
    if cl < w_len {
        lohi[w_len + cl..].copy_from_slice(&vec![0; w_len - cl]);
    }
    for i in (0..v_len - w_len + 1).step_by(w_len) {
        println!(
            "i = {}, v = {}",
            i,
            BigUint {
                data: v.data[i..i + w_len].into()
            }
            .normalized()
        );
        let mut tmp = v.data[i..i + w_len].to_vec();
        let bw = __sub2(&mut tmp, &lohi[w_len..]);

        // Montgomery mul step
        mul_lo(&mut tmp, &winv.data, w_len);

        println!(
            "tmp * yinv = {}",
            BigUint {
                data: tmp.clone().into()
            }
            .normalized()
        );

        let tmp2 = __mul3(&tmp, &w.data);
        lohi[..].copy_from_slice(&tmp2[..2 * w_len]);
        lohi[w_len] += bw as BigDigit;
        println!("{:?}", &lohi);
        debug_assert!(lohi[w_len] >= bw as BigDigit, "carry issue");
        println!(
            "  lo = {}",
            BigUint {
                data: (&lohi[..w_len]).to_vec().into()
            }
            .normalized()
        );
        println!(
            "  hi = {}",
            BigUint {
                data: (&lohi[w_len..]).to_vec().into()
            }
            .normalized()
        );
        // this is the y[i] = tmp step in the scalar routine
        q[i..i + w_len].copy_from_slice(&tmp[..w_len]);
        println!("q: {}", BigUint { data: q.clone() }.normalized());
    }

    // handle last step, for non dividing cases
    let i = v_len - w_len + 1;
    let j = v_len - i;
    println!("i = {}, j = {}", i, j);
    if j > 0 {
        // clear q[i..j]
        for qi in q.iter_mut().skip(i).take(j) {
            *qi = 0;
        }
    }
    println!("q = {}", BigUint { data: q.clone() }.normalized());
    // Adjust remainder for even modulus.
    if nshift > 0 {
        cy <<= nshift;
        __add2(&mut cy.data, &rem_save.data);
    }

    (BigUint { data: q }.normalized(), cy.normalized())
}

/// Computes `R**n (mod q)`.
/// - `pow = R**2 (mod q)`
/// - `q * qinv = 1 (mod 2**BITS)`, `q` is odd.
fn radix_power_n(n: usize, q: &BigUint, qinv: &BigUint) -> BigUint {
    let len = q.data.len();
    // TODO: use a constant
    let two: BigUint = 2u32.into();
    let r = &two.pow(big_digit::BITS as u32 * len as u32) % q;
    // TODO: implement optimized squaring algorithm
    let r2 = r.modpow(&two, q);

    println!("R**2 = {}", &r2);
    if n == 2 {
        return r2;
    }

    // R**3 (mod q)

    if n == 3 {
        return mont_sqr_n(&r2, q, qinv);
    }

    let mut bm = 0u32;
    let mut j = 0;
    let mut n = n;
    while n > 5 {
        bm.set_bit(j, is_even(n));
        n = (n / 2) + 1;
        j += 1;
    }

    let r3 = mont_sqr_n(&r2, q, qinv);
    println!("R**3 = {}", &r3);
    let mut pow = if n == 4 {
        mont_mul_n(&r2, &r3, q, qinv)
    } else if n == 5 {
        mont_sqr_n(&r3, q, qinv)
    } else {
        unreachable!("bad power of p")
    };

    for i in (0..j).rev() {
        if bm.get_bit(i) {
            // Reduce R-power by 1
            let tmp = mmul_one_n(&pow, q, qinv);

            // and multiply
            pow = mont_mul_n(&tmp, &pow, q, qinv);
        } else {
            pow = mont_sqr_n(&pow, q, qinv);
        }
    }

    pow
}

/// Calculates the modular inverse of `x` , such that `x * xinv = 1 (mod 2**BITS)`.
/// `x` must be `odd`.
/// Uses Netwon iterations to do so.
fn mod_invn(x: &BigUint) -> BigUint {
    debug_assert!(x.is_odd());

    let xbits = x.data.len() << 6; // TODO: adjust for 32bit
    let log2_numbits = ((1.0 * xbits as f64).ln() / (2.0f64.ln())).ceil() as usize;

    let mut xinv = BigUint {
        data: SmallVec::with_capacity(x.data.len()),
    };

    // inverse for one limb
    xinv.data.push(mod_inv1(x.data[0]));
    xinv.data.resize(x.data.len(), 0);

    // calculate the other limbs, we double the good limbs each iteration.
    println!("x: {:?}", &x);
    println!("xinv: {:?}", &xinv);

    let len = x.data.len();
    for j in 6..log2_numbits {
        let mut tmp = x.data.clone();
        println!("{} / {}", j, log2_numbits);
        println!("tmp = {}", BigUint { data: tmp.clone() });
        println!("w = {}", &x);
        mul_lo(&mut tmp, &xinv.data, len);
        println!("tmp: {:?}", &tmp);
        nega(&mut tmp);
        println!("tmp: {:?}", &tmp);
        let _bw = __add_scalar(&mut tmp, 2);
        // debug_assert!(bw == 0, "unexpected carry");

        mul_lo(&mut xinv.data, &tmp, len);
    }

    xinv.normalized()
}

/// Arithmetic negation, based on `-x = !x + 1`.
#[inline]
fn nega(x: &mut [BigDigit]) {
    negl(x);
    __add_scalar(x, 1);
}

/// Logical negation.
#[inline]
fn negl(x: &mut [BigDigit]) {
    for xi in x.iter_mut() {
        *xi = !*xi;
    }
}

/// Slow division one bit at a time.
fn div_rem_binary(x: &BigUint, y: &BigUint) -> (BigUint, BigUint) {
    println!("div_rem_binary {} / {}", x, y);
    assert!(!y.is_zero(), "dividing by 0");

    let x_len = x.data.len();
    let y_len = y.data.len();
    let max_len = std::cmp::max(x_len, y_len);

    // Done if `x < y`.
    if x_len < y_len || (x_len == y_len && x < y) {
        return (0u32.into(), x.clone());
    }

    let lz_x = x.leading_zeros() as usize + (max_len - x_len) * big_digit::BITS;
    let lz_y = y.leading_zeros() as usize + (max_len - y_len) * big_digit::BITS;
    let nshift = lz_y - lz_x;

    // Left justify the modulus
    let mut y_loc = y << nshift;
    let mut x_loc = x.clone();

    let mut q = BigUint {
        data: smallvec![0; max_len],
    };

    for i in (0..nshift + 1).rev() {
        if &x_loc > &y_loc {
            __sub2(&mut x_loc.data, &y_loc.data);
            x_loc.normalize();
            q.set_bit(i, true);
        }

        if i > 0 {
            y_loc >>= 1;
        }
    }

    // Remainder is in x_loc
    debug_assert!(&x_loc < y, "remainder should be less than the modulus");

    return (q.normalized(), x_loc);
}

/// Extract the leading `BITS` bits from `x`.
fn get_leading_bits(x: &BigUint) -> (BigDigit, usize) {
    let len = x.data.len();
    let nshift = x.leading_zeros() as usize;
    let nwshift = nshift >> 6; // TODO: adjust for 32bit
    let rembits = nshift & (big_digit::BITS - 1);

    if nwshift >= len {
        return (0, 0);
    }

    let i = len - 1 - nwshift;

    let bits = if rembits > 0 {
        let mut bits = x.data[i] << rembits;
        if i > 0 {
            bits += x.data[i - 1] >> (big_digit::BITS - rembits);
        }
        bits
    } else {
        x.data[i]
    };

    (bits, (len << 6) - nshift)
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
    let r_scaled = radix_power(n + 1, q, qinv);
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
    let scale = radix_power(n2 + 1, q, qinv);

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

/// Calculate the montgomery product `x * y * R**-1 (mod q)`,
/// with `R = 2**b`.
/// `q * qinv = 1 (mod 2**b)`, `q` is odd.
fn mont_mul_n(x: &BigUint, y: &BigUint, q: &BigUint, qinv: &BigUint) -> BigUint {
    debug_assert!(q.is_odd());

    let len = x.data.len();

    let mut lohi = x.data.clone();
    lohi.resize(2 * len, 0);
    let tmp = __mul3(&lohi, &y.data);

    lohi.copy_from_slice(&tmp[..2 * len]);

    let (lo, hi) = lohi.split_at_mut(len);

    mul_lo(lo, &qinv.data, len);
    mul_hi(lo, &q.data, len);

    let bw = __sub2(hi, &*lo);
    if bw {
        __add2(hi, &q.data);
    }

    BigUint::new_native(hi.to_vec().into())
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

/// Calculate the montgomery square `x**2 * R**-1 (mod q)`,
/// with `R = 2**b`.
/// `q * qinv = 1 (mod 2**b)`, `q` is odd.
fn mont_sqr_n(x: &BigUint, q: &BigUint, qinv: &BigUint) -> BigUint {
    debug_assert!(q.is_odd());
    let len = x.data.len();

    // TODO: optimize for squaring
    let mut lohi = x.data.clone();
    lohi.resize(2 * len, 0);
    let tmp = __mul3(&lohi, &lohi);
    lohi.copy_from_slice(&tmp[..2 * len]);

    let (lo, hi) = lohi.split_at_mut(len);

    mul_lo(lo, &qinv.data, len);
    mul_hi(lo, &q.data, len);

    let bw = __sub2(hi, &*lo);
    if bw {
        __add2(hi, &q.data);
    }

    BigUint::new_native(hi.to_vec().into())
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

/// Calculate the montgomery multiply by unity `x * R**-1 (mod q)`,
/// with `R = 2**b`.
/// `q * qinv = 1 (mod 2**b)`, `q` is odd.
fn mmul_one_n(x: &BigUint, q: &BigUint, qinv: &BigUint) -> BigUint {
    debug_assert!(q.is_odd());

    unimplemented!("");
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
fn radix_power(n: usize, q: BigDigit, qinv: BigDigit) -> BigDigit {
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

    let (j, p, bm) = calc_bitmap(n);

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
    if n == 0 {
        return 0;
    }
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
    let r_scaled = radix_power(n, q, qinv);

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
        remainder_a_u2(&x, q, qinv)
    } else {
        let tz = q.trailing_zeros();
        let bsave = x.data[0] & ((2 as BigDigit).pow(tz) - 1);

        let q_dash = q >> tz as usize;

        let qinv_dash = mod_inv1(q_dash);
        let x_dash = x >> tz as usize;

        let r_dash = remainder_b(&x_dash, q_dash, qinv_dash);

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
        let r = remainder_a_u2(&*x, q, qinv);

        quotient_odd(x, r, q, qinv);
    } else {
        let tz = q.trailing_zeros() as usize;

        let q_dash = q >> tz;
        let qinv_dash = mod_inv1(q_dash);
        *x >>= tz;

        let r_dash = remainder_b(&*x, q_dash, qinv_dash);

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

    use num_traits::{FromPrimitive, Num, Pow, ToPrimitive};
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
        let pow = radix_power(17, q, qinv);

        let r17 = 8502984233828494641;
        assert_eq!(&pow, &r17);
    }

    #[test]
    fn test_quotient_odd() {
        let mut x: BigUint = (BigUint::from_u64(2).unwrap().pow(977u32)) - 1u32;
        let q = 16357897499336320049;
        let qinv = mod_inv1(q);

        let rem = remainder_a_u2(&x, q, qinv);
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

            let rem = remainder_a_u2(&x, q, qinv);
            assert_eq!(x_orig % q, rem);
        }
    }

    #[test]
    fn test_negl() {
        let mut x = vec![1, 2, 3];
        negl(&mut x);
        assert_eq!(x, vec![!1, !2, !3]);
    }

    #[test]
    fn test_nega() {
        let mut x = vec![5];
        nega(&mut x);
        assert_eq!(x, vec![!5 + 1]);
    }

    #[test]
    fn test_div_rem_binary() {
        let x = BigUint::from_u64(123).unwrap();
        let y = BigUint::from_u64(456).unwrap();

        let q: u32 = 123 / 456;
        let r: u32 = 123 % 456;

        assert_eq!(div_rem_binary(&x, &y), (q.into(), r.into()));

        let x = BigUint::from_str_radix("364131549958466711308970009901738230041", 10).unwrap();
        let y = BigUint::from_str_radix("19437941122649628431", 10).unwrap();

        let q = BigUint::from_str_radix("18733030811281269087", 10).unwrap();
        let r = BigUint::from_str_radix("618006351061617544", 10).unwrap();

        assert_eq!(div_rem_binary(&x, &y), (q.into(), r.into()));
    }

    #[test]
    fn test_mont_mul_n() {
        let x: BigUint = 10u32.into();
        let y: BigUint = 40u32.into();
        let q: BigUint = 13u32.into();
        let qinv = mod_invn(&q);

        let res = mont_mul_n(&x, &y, &q, &qinv);
        let r = 2u128.pow(big_digit::BITS as u32);
        let rinv = r
            .into_biguint()
            .unwrap()
            .mod_inverse(&q)
            .unwrap()
            .into_biguint()
            .unwrap();
        let expected = (&x * &y * rinv) % q;

        assert_eq!(res, expected);
    }

    #[test]
    fn test_mont_sqr_n() {
        let x: BigUint = 10u32.into();
        let q: BigUint = 13u32.into();
        let qinv = mod_invn(&q);

        let res = mont_sqr_n(&x, &q, &qinv);
        let r = 2u128.pow(big_digit::BITS as u32);
        let rinv = r
            .into_biguint()
            .unwrap()
            .mod_inverse(&q)
            .unwrap()
            .into_biguint()
            .unwrap();
        let expected = (&x * &x * rinv) % q;

        assert_eq!(res, expected);
    }

    #[test]
    fn test_mod_invn() {
        let y = BigUint::from_str_radix("19437941122649628431", 10).unwrap();

        assert_eq!(
            mod_invn(&y),
            BigUint::from_str_radix("232515390938603038445704290069949444079", 10).unwrap()
        );
    }

    #[test]
    #[cfg(feature = "rand")]
    fn test_mod_invn_rand() {
        use crate::bigrand::RandBigInt;
        use rand::thread_rng;

        let mut rng = thread_rng();

        for i in 0..1000 {
            for b in &[64, 128, 256, 1024, 2048] {
                let mut x = rng.gen_biguint(*b);
                // make x odd
                x.set_bit(0, true);
                let xinv = mod_invn(&x);
                let r = 2u32
                    .into_biguint()
                    .unwrap()
                    .pow((big_digit::BITS * x.data.len()) as u32);

                assert_eq!((&x * &xinv) % r, BigUint::one(), "{} * {}", &x, &xinv);
            }
        }
    }

    #[test]
    fn test_div_rem_mont() {
        let x = BigUint::from_u64(123).unwrap();
        let y = BigUint::from_u64(456).unwrap();

        let q: u32 = 123 / 456;
        let r: u32 = 123 % 456;

        assert_eq!(div_rem_mont(&x, &y), (q.into(), r.into()));

        let x = BigUint::from_str_radix("364131549958466711308970009901738230041", 10).unwrap();
        let y = BigUint::from_str_radix("19437941122649628431", 10).unwrap();

        let q = BigUint::from_str_radix("18733030811281269087", 10).unwrap();
        let r = BigUint::from_str_radix("618006351061617544", 10).unwrap();

        assert_eq!(div_rem_mont(&x, &y), (q.into(), r.into()));
    }

    #[test]
    fn test_radix_power_n() {
        let q: BigUint = 16357897499336320049u64.into();
        let qinv = mod_invn(&q);

        // Algorithm A:
        let pow = radix_power_n(17, &q, &qinv);

        let r17: BigUint = 8502984233828494641u64.into();
        assert_eq!(&pow, &r17);
    }
}
