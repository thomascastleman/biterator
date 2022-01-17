//! This crate provides [`Biterator`], a type for iterating over individual bits
//! in a stream of bytes.
//!
//! # Example
//! ```
//! use biterator::{Biterator, Bit::*};
//!
//! let bytes = [0b00001111, 0b10101011];
//! let b = Biterator::new(&bytes);
//!
//! assert_eq!(
//!     b.collect::<Vec<_>>(),
//!     vec![
//!         Zero, Zero, Zero, Zero, One, One,  One, One,
//!         One,  Zero, One,  Zero, One, Zero, One, One,
//!     ]
//! );
//! ```
//!
//! Use it to find which bits are set in a stream:
//! ```
//! use biterator::{Biterator, Bit};
//!
//! let bytes = [0b00110101];
//! let b = Biterator::new(&bytes);
//!
//! let set_bits: Vec<(usize, Bit)> = b.enumerate().filter(|(_, bit)| bit.is_one()).collect();
//! assert_eq!(
//!     set_bits,
//!     vec![(2, Bit::One), (3, Bit::One), (5, Bit::One), (7, Bit::One)]
//! );
//! ```

#[warn(missing_docs)]

/// A single bit.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Bit {
    /// A cleared bit.
    Zero,
    /// A set bit.
    One,
}

impl Bit {
    /// Check if this [`Bit`] is a zero bit.
    pub fn is_zero(&self) -> bool {
        *self == Bit::Zero
    }

    /// Check if this [`Bit`] is a one bit.
    pub fn is_one(&self) -> bool {
        *self == Bit::One
    }
}

/// Bits can be converted into booleans (`1` signifying `true` and `0` signifying `false`).
impl std::convert::From<Bit> for bool {
    fn from(bit: Bit) -> Self {
        bit.is_one()
    }
}

/// The bit index of the leftmost bit in a byte.
const LEFTMOST_BIT_INDEX: u8 = 7;
/// The bit index of the rightmost bit in a byte.
const RIGHTMOST_BIT_INDEX: u8 = 0;

/// An iterator over individual bits in a slice.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Biterator<'src> {
    source: &'src [u8],
    bit_index: u8,
}

impl Biterator<'_> {
    /// Construct a new `Biterator` to iterate over the [`Bit`]s in a given source,
    /// which is a slice of bytes.
    pub fn new(source: &[u8]) -> Biterator<'_> {
        Biterator {
            source,
            bit_index: LEFTMOST_BIT_INDEX,
        }
    }
}

/// [`Biterator`] implements [`Iterator`] to provide an iterator over [`Bit`]s.
impl std::iter::Iterator for Biterator<'_> {
    type Item = Bit;

    fn next(&mut self) -> Option<Self::Item> {
        // Extract the current byte we're pulling bits from--if there is none,
        // then the Biterator is exhausted.
        let byte = self.source.first()?;

        // Bitmask that will extract the bit indicated by bit_index
        let current_bit_mask = 2u8.pow(self.bit_index as u32);

        if self.bit_index == RIGHTMOST_BIT_INDEX {
            // The rightmost bit of this byte has been reached, bit_index wraps
            // and we move to the next byte of the source for the subsequent
            // call to next().
            self.source = &self.source[1..];
            self.bit_index = LEFTMOST_BIT_INDEX;
        } else {
            // Move one position to the right
            self.bit_index -= 1;
        }

        if byte & current_bit_mask > 0 {
            Some(Bit::One)
        } else {
            Some(Bit::Zero)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use Bit::*;

    #[test]
    fn empty_source() {
        let mut b = Biterator::new(&[]);
        assert!(b.next().is_none());
    }

    #[test]
    fn single_byte_source() {
        let byte = [0b10101111];
        let b = Biterator::new(&byte);

        assert_eq!(
            b.collect::<Vec<_>>(),
            vec![One, Zero, One, Zero, One, One, One, One]
        );
    }

    #[test]
    fn multiple_byte_source() {
        let bytes = [0b00110110, 0b11111011, 0b10001100];
        let b = Biterator::new(&bytes);

        #[rustfmt::skip]
        assert_eq!(
            b.collect::<Vec<_>>(),
            vec![
                Zero, Zero, One,  One,  Zero, One,  One,  Zero, 
                One,  One,  One,  One,  One,  Zero, One,  One,
                One,  Zero, Zero, Zero, One,  One,  Zero, Zero
            ]
        );
    }

    #[test]
    fn convert_bits() {
        let bits = vec![One, Zero, Zero, One];
        let as_bools: Vec<bool> = bits.into_iter().map(|b| b.into()).collect();
        assert_eq!(as_bools, vec![true, false, false, true]);
    }
}
