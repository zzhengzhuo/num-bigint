use crate::big_digit::{BigDigit, BITS};
use crate::BigUint;
use crate::VEC_SIZE;

#[inline]
pub fn biguint_shr(n: &mut BigUint, nbits: usize) {
    let mut len = n.data.len();

    // Ignore 0 shifts
    if nbits == 0 || len == 0 {
        return;
    }

    {
        let x = &mut n.data;
        let nwshift = nbits / BITS;
        let rembits = (nbits & (BITS - 1)) as u32;

        // Handle overshifts
        if nwshift >= len {
            x.resize(len, 0);
            len = x.len();
        }

        for i in 0..len - nwshift {
            x[i] = x[i + nwshift];
        }

        for i in len - nwshift..len {
            x[i] = 0;
        }

        // Non mutliple of word size shifts.
        if rembits > 0 {
            let mbits = BITS as u32 - rembits;

            for i in 0..len - 1 {
                x[i] = (x[i].wrapping_shr(rembits)) + (x[i + 1].wrapping_shl(mbits));
            }
            x[len - 1] = x[len - 1].wrapping_shr(rembits);
        }
    }

    n.normalize();
}
