use crate::big_digit::{BigDigit, DoubleBigDigit, BITS};

// Add with carry:
#[inline]
pub fn adc(a: BigDigit, b: BigDigit, acc: &mut DoubleBigDigit) -> BigDigit {
    *acc += a as DoubleBigDigit;
    *acc += b as DoubleBigDigit;
    let lo = *acc as BigDigit;
    *acc >>= BITS;
    lo
}

/// Inplace addition of a scalar, returns `true` if there was an overflow.
#[inline]
pub fn __add_scalar(a: &mut [BigDigit], b: BigDigit) -> BigDigit {
    let mut carry = b;

    for ai in a.iter_mut() {
        let (nai, overflow) = ai.overflowing_add(carry);
        *ai = nai;
        carry = overflow as BigDigit;

        if !overflow {
            break;
        }
    }

    carry
}

/// Inplace addition of two vectors. Returns `true` if there was an overflow, meaning there was a carry
/// which did not fit into `a`.
/// Requires `a.len() >= b.len()`.
#[inline]
pub fn __add2(a: &mut [BigDigit], b: &[BigDigit]) -> BigDigit {
    debug_assert!(a.len() >= b.len());

    if b.len() == 1 {
        __add_scalar(a, b[0])
    } else {
        let mut carry = 0;
        let (a_lo, a_hi) = a.split_at_mut(b.len());
        for (a, b) in a_lo.iter_mut().zip(b) {
            *a = adc(*a, *b, &mut carry);
        }

        if carry != 0 {
            __add_scalar(a_hi, carry as BigDigit)
        } else {
            0
        }
    }

    // TODO: fix

    // let len = b.len();

    // if len == 0 {
    //     return false;
    // }

    // if a.len() < 2 {
    //     let (res, overflow) = a[0].overflowing_add(b[0]);
    //     a[0] = res;
    //     return overflow;
    // }

    // if b.len() == 1 {
    //     return __add_scalar(a, b[0]);
    // }

    // // 2-folded loop
    // let len2 = len >> 1;
    // let odd = len & 1;

    // let mut cy1 = 0;
    // let mut cy2 = 0;

    // {
    //     let (alo, ahi) = a.split_at_mut(len2);
    //     let (blo, bhi) = b.split_at(len2);

    //     for ((ai, aj), (bi, bj)) in alo
    //         .iter_mut()
    //         .zip(ahi.iter_mut())
    //         .zip(blo.iter().zip(bhi.iter()))
    //     {
    //         let (tmp1, overflow1) = ai.overflowing_add(cy1);
    //         let (tmp2, overflow2) = aj.overflowing_add(cy2);

    //         cy1 = overflow1 as BigDigit;
    //         cy2 = overflow2 as BigDigit;

    //         let (tmp1, overflow1) = tmp1.overflowing_add(*bi);
    //         let (tmp2, overflow2) = tmp2.overflowing_add(*bj);

    //         cy1 += overflow1 as BigDigit;
    //         cy2 += overflow2 as BigDigit;

    //         *ai = tmp1;
    //         *aj = tmp2;
    //     }

    //     // Propagate low half carry into high half.
    //     cy1 = __add_scalar(ahi, cy1) as BigDigit;

    //     if ahi.len() > bhi.len() {
    //         cy2 = __add_scalar(&mut ahi[bhi.len()..], cy2) as BigDigit;
    //     }
    // }
    // // In case cy1 went all the way
    // cy2 += cy1;

    // // Take care of high words
    // if odd > 0 {
    //     let i = len - 1;
    //     let (tmp, overflow) = a[i].overflowing_add(b[i]);
    //     cy1 = overflow as BigDigit;
    //     let (tmp, overflow) = tmp.overflowing_add(cy2);
    //     cy1 += overflow as BigDigit;
    //     a[i] = tmp;

    //     if cy1 == 0 {
    //         return false;
    //     }
    //     if a.len() == len {
    //         return cy1 > 0;
    //     }

    //     return __add_scalar(&mut a[len..], cy1);
    // }

    // cy2 > 0
}

/// Two argument addition of raw slices:
/// a += b
///
/// The caller _must_ ensure that a is big enough to store the result - typically this means
/// resizing a to max(a.len(), b.len()) + 1, to fit a possible carry.
#[inline]
pub fn add2(a: &mut [BigDigit], b: &[BigDigit]) {
    let carry = __add2(a, b);
    debug_assert!(carry == 0);
}

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn test_add_scalar() {
    //     let mut res = [100];
    //     assert!(!__add_scalar(&mut res, 123));
    //     assert_eq!(res[0], 100 + 123);

    //     let mut res = [BigDigit::max_value()];
    //     assert!(__add_scalar(&mut res, 10));
    //     assert_eq!(res[0], 9);

    //     let mut res = [BigDigit::max_value(), 1];
    //     assert!(!__add_scalar(&mut res, 10));
    //     assert_eq!(res[0], 9);
    //     assert_eq!(res[1], 2);
    // }

    // #[test]
    // fn test_internal_add2() {
    //     let mut res = [100];
    //     assert!(!__add2(&mut res, &[123]));
    //     assert_eq!(res[0], 100 + 123);

    //     let mut res = [BigDigit::max_value()];
    //     assert!(__add2(&mut res, &[10]));
    //     assert_eq!(res[0], 9);

    //     let mut res = [BigDigit::max_value(), 1];
    //     assert!(!__add2(&mut res, &[10]));
    //     assert_eq!(res[0], 9);
    //     assert_eq!(res[1], 2);

    //     let mut res = [BigDigit::max_value(), 2, 3, 4];
    //     assert!(!__add2(&mut res, &[BigDigit::max_value(), 2, 3, 4]));
    //     assert_eq!(res[0], BigDigit::max_value() - 1);
    //     assert_eq!(res[1], 5);
    //     assert_eq!(res[2], 6);
    //     assert_eq!(res[3], 8);

    //     let mut res = [BigDigit::max_value(), 2, 3, 4];
    //     assert!(!__add2(&mut res, &[BigDigit::max_value()]));
    //     assert_eq!(res[0], BigDigit::max_value() - 1);
    //     assert_eq!(res[1], 3);
    //     assert_eq!(res[2], 3);
    //     assert_eq!(res[3], 4);

    //     let mut res = [BigDigit::max_value(), 2, 3, 4];
    //     assert!(!__add2(
    //         &mut res,
    //         &[BigDigit::max_value(), BigDigit::max_value()]
    //     ));
    //     assert_eq!(res[0], BigDigit::max_value() - 1);
    //     assert_eq!(res[1], 2);
    //     assert_eq!(res[2], 4);
    //     assert_eq!(res[3], 4);
    // }

    #[test]
    fn test_add2() {
        let mut res = [100];
        add2(&mut res, &[123]);
        assert_eq!(res[0], 100 + 123);

        let mut res = [BigDigit::max_value(), 0];
        add2(&mut res, &[10]);
        assert_eq!(res[0], 9);
        assert_eq!(res[1], 1);

        let mut res = [BigDigit::max_value(), 1];
        add2(&mut res, &[10]);
        assert_eq!(res[0], 9);
        assert_eq!(res[1], 2);
    }
}
