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
