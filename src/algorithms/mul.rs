use crate::algorithms::{mac3, mac_digit};
use crate::big_digit::{BigDigit, DoubleBigDigit, BITS};
use crate::BigUint;

#[inline]
pub fn mul_with_carry(a: BigDigit, b: BigDigit, acc: &mut DoubleBigDigit) -> BigDigit {
    *acc += (a as DoubleBigDigit) * (b as DoubleBigDigit);
    let lo = *acc as BigDigit;
    *acc >>= BITS;
    lo
}

pub fn mul3(x: &[BigDigit], y: &[BigDigit]) -> BigUint {
    let len = x.len() + y.len() + 1;
    let mut prod = BigUint {
        data: smallvec![0; len],
    };

    mac3(&mut prod.data[..], x, y);
    prod.normalized()
}

pub fn scalar_mul(a: &mut [BigDigit], b: BigDigit) -> BigDigit {
    let mut carry = 0;
    for a in a.iter_mut() {
        *a = mul_with_carry(*a, b, &mut carry);
    }
    carry as BigDigit
}

/// Multiply the lower half of two vectors, writing the result into `x`.
pub fn mul_lo(x: &mut [BigDigit], y: &[BigDigit]) {
    let len = x.len();

    let mut u = vec![0; len];

    for (j, yi) in y.iter().enumerate() {
        mac_digit(&mut u[j..], &x[..len - j], *yi);
    }

    x.copy_from_slice(&u);
}

/// Multiply the high half of two vectors, writing the result into `x`.
pub fn mul_hi(x: &mut [BigDigit], y: &[BigDigit]) {
    unimplemented!("");
}

/// Specialized squaring version of `__mul2`.
pub fn __sqr2(x: &mut [BigDigit]) {
    unimplemented!("");
}

/// Multiply two vectors together.
pub fn __mul2(x: &mut [BigDigit], y: &[BigDigit]) {
    unimplemented!("");
}
