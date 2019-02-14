use smallvec::SmallVec;

use crate::algorithms::{__add2, __mac_digit, mac3, mac_digit};
use crate::big_digit::{BigDigit, DoubleBigDigit, BITS};
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
    let data = __mul3(x, y);
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

/// Multiply the lower half (of length `len`) of two vectors, writing the result into `x`.
#[inline]
pub fn mul_lo(x: &mut [BigDigit], y: &[BigDigit], len: usize) {
    assert!(len > 0);

    let mut u = vec![0; len + 1];

    for (j, yj) in y.iter().enumerate().take(len) {
        if *yj == 0 {
            continue;
        }
        __mac_digit(&mut u[j..], &x[..len - j], *yj);
    }

    x[..len].copy_from_slice(&u[..len]);
}

/// Multiply the high half (of length `len`) of two vectors, writing the result into `x`.
#[inline]
pub fn mul_hi(x: &mut [BigDigit], y: &[BigDigit], len: usize) {
    assert!(len > 0);

    let mut u = vec![0; len + 1];
    let mut v = vec![0; 2 * len];

    for (j, yj) in y.iter().enumerate().take(len) {
        if *yj == 0 {
            continue;
        }
        u[..len].copy_from_slice(x);
        u[len] = scalar_mul(&mut u[..len], *yj) as BigDigit;
        v[len + j] = u[len] + __add2(&mut v[j..j + len], &u[..len]) as BigDigit;
    }

    x[..len].copy_from_slice(&v[len..2 * len]);
}

pub fn __mul3(x: &[BigDigit], y: &[BigDigit]) -> SmallVec<[BigDigit; VEC_SIZE]> {
    let len = x.len() + y.len() + 1;
    let mut data = smallvec![0; len];

    mac3(&mut data[..], x, y);

    data
}

#[cfg(test)]
mod tests {
    use super::*;

    use num_traits::Num;

    #[test]
    fn test_mul_lo() {
        let a = [10, 15];
        let b = [12, 3];

        let mut res = a.clone();
        mul_lo(&mut res, &b, 1);
        assert_eq!(&res[..1], &__mul3(&a[..1], &b[..1])[..1]);

        let a = [10, 15, 3];
        let b = [12, 3, 4, 2];

        let mut res = a.clone();
        mul_lo(&mut res, &b, 2);
        assert_eq!(&res[..2], &__mul3(&a[..2], &b[..2])[..2]);
    }

    #[test]
    fn test_mul_hi() {
        let a = BigUint::from_str_radix("329463491476029530175143993024310918392", 10).unwrap();
        let b = BigUint::from_str_radix("19437941122649628431", 10).unwrap();
        let len = 2;

        let mut res = a.clone();
        mul_hi(&mut res.data, &b.data, len);
        assert_eq!(
            res.normalized(),
            BigUint::from_str_radix("18819934771588010887", 10).unwrap()
        );
    }
}
