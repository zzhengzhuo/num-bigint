use smallvec::SmallVec;

use crate::algorithms::{__add2, __mac_digit, mac3};
use crate::big_digit::{self, BigDigit, DoubleBigDigit, BITS};
use crate::{BigUint, VEC_SIZE};

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, acc: &mut DoubleBigDigit) -> BigDigit {
    *acc += (a as DoubleBigDigit) * (b as DoubleBigDigit);
    let lo = *acc as BigDigit;
    *acc >>= BITS;
    lo
}

#[inline]
pub fn mul3(x: &[BigDigit], y: &[BigDigit]) -> BigUint {
    let len = x.len() + y.len() + 1;
    let mut data = smallvec![0; len];

    mac3(&mut data, x, y);

    BigUint { data }.normalized()
}

#[inline]
pub fn scalar_mul(a: &mut [BigDigit], b: BigDigit) -> BigDigit {
    let mut carry = 0;
    for a in a.iter_mut() {
        *a = mul_with_carry(*a, b, &mut carry);
    }
    carry as BigDigit
}

#[inline]
fn mul_lohi(a: BigDigit, b: BigDigit, lo: &mut BigDigit, hi: &mut BigDigit) {
    let c = (a as DoubleBigDigit) * (b as DoubleBigDigit);

    *lo = big_digit::get_lo(c);
    *hi = big_digit::get_hi(c);
}

#[inline]
fn scalar_mul3(x: &[BigDigit], a: BigDigit, y: &mut [BigDigit]) -> BigDigit {
    let mut cy = 0;
    // for (a, c) in a.iter().zip(c.iter_mut()) {
    //     *c = mul_with_carry(*a, b, &mut carry);
    // }

    let len = x.len();
    let lmod4 = (len & 0x3);
    let ihi = len - lmod4;

    let mut lo = 0;
    let mut hi = 0;
    let mut i = 0;
    while i < ihi {
        mul_lohi(x[i], a, &mut lo, &mut hi);
        y[i] = lo.wrapping_add(cy);
        cy = hi + (y[i] < lo) as BigDigit;
        i += 1;

        mul_lohi(x[i], a, &mut lo, &mut hi);
        y[i] = lo.wrapping_add(cy);
        cy = hi + (y[i] < lo) as BigDigit;
        i += 1;

        mul_lohi(x[i], a, &mut lo, &mut hi);
        y[i] = lo.wrapping_add(cy);
        cy = hi + (y[i] < lo) as BigDigit;
        i += 1;

        mul_lohi(x[i], a, &mut lo, &mut hi);
        y[i] = lo.wrapping_add(cy);
        cy = hi + (y[i] < lo) as BigDigit;
        i += 1;
    }

    // cleanup remaining terms
    while i < len {
        mul_lohi(x[i], a, &mut lo, &mut hi);
        y[i] = lo.wrapping_add(cy);
        cy = hi + (y[i] < lo) as BigDigit;
        i += 1;
    }

    cy
}

/// Multiply the lower half (of length `len`) of two vectors, writing the result into `x`.
#[inline]
pub fn mul_lo(x: &mut [BigDigit], y: &[BigDigit], len: usize, scratch: &mut [BigDigit]) {
    assert!(len > 0);
    assert!(scratch.len() >= len + 1);
    // clear out, so we can use `mac`.
    for s in scratch.iter_mut().take(len + 1) {
        *s = 0;
    }

    for (j, yj) in y.iter().enumerate().take(len) {
        if *yj == 0 {
            continue;
        }
        __mac_digit(&mut scratch[j..len + 1], &x[..len - j], *yj);
    }

    x[..len].copy_from_slice(&scratch[..len]);
}

/// Multiply the high half (of length `len`) of two vectors, writing the result into `x`.
#[inline]
pub fn mul_hi(x: &mut [BigDigit], y: &[BigDigit], len: usize, scratch: &mut [BigDigit]) {
    assert!(len > 0);
    assert!(scratch.len() > 3 * len + 1);

    let (u, v_all) = scratch.split_at_mut(len + 1);
    let (v, _) = v_all.split_at_mut(3 * len + 1);

    for vi in v.iter_mut() {
        *vi = 0;
    }

    for (j, yj) in y.iter().enumerate().take(len) {
        if *yj == 0 {
            continue;
        }

        u[len] = scalar_mul3(&x, *yj, u) as BigDigit;
        v[len + j] = u[len] + __add2(&mut v[j..j + len], &u[..len]) as BigDigit;
    }

    x[..len].copy_from_slice(&v[len..2 * len]);
}

/// Calcs `(lo, hi) = x * y`. (split at x.len())
pub fn __mul3(
    x: &[BigDigit],
    y: &[BigDigit],
    scratch: &mut [BigDigit],
) -> SmallVec<[BigDigit; VEC_SIZE]> {
    let len = x.len() + y.len() + 1;
    assert!(scratch.len() >= len);

    // order them
    let (a, b, a_len, b_len) = if x.len() >= y.len() {
        (x, y, x.len(), y.len())
    } else {
        (y, x, y.len(), x.len())
    };

    // Nothing to do
    if b_len == 0 {
        return smallvec![];
    }

    let mut z = smallvec![0; len];

    for (j, bj) in b.iter().enumerate() {
        scratch[a_len] = scalar_mul3(a, *bj, scratch);
        z[a_len + j] = scratch[a_len] + __add2(&mut z[j..j + a_len], &scratch[..a_len]) as BigDigit;
    }

    z
}

#[cfg(test)]
mod tests {
    use super::*;

    use num_traits::Num;

    #[test]
    fn test_mul_lo() {
        let a = [10, 15];
        let b = [12, 3];
        let mut scratch = vec![0; 8];

        let mut res = a.clone();
        mul_lo(&mut res, &b, 1, &mut scratch);
        assert_eq!(&res[..1], &__mul3(&a[..1], &b[..1], &mut scratch)[..1]);

        let a = [10, 15, 3];
        let b = [12, 3, 4, 2];

        let mut res = a.clone();
        mul_lo(&mut res, &b, 2, &mut scratch);
        assert_eq!(&res[..2], &__mul3(&a[..2], &b[..2], &mut scratch)[..2]);
    }

    #[test]
    fn test_mul_hi() {
        let a = BigUint::from_str_radix("329463491476029530175143993024310918392", 10).unwrap();
        let b = BigUint::from_str_radix("19437941122649628431", 10).unwrap();
        let len = 2;
        let mut scratch = vec![0; 10];
        let mut res = a.clone();
        mul_hi(&mut res.data, &b.data, len, &mut scratch);
        assert_eq!(
            res.normalized(),
            BigUint::from_str_radix("18819934771588010887", 10).unwrap()
        );
    }
}
