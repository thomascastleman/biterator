//! This crate provides [`Biterator`], a type for iterating over individual bits
//! in a stream of bytes.
//!
//! # Examples
//! ```
//! use biterator::{Biterator, Bit::*};
//!
//! let bytes = [0b00001111, 0b10101011];
//! let bits: Vec<_> = Biterator::new(&bytes).collect();
//!
//! assert_eq!(
//!     bits,
//!     vec![
//!         Zero, Zero, Zero, Zero, One, One,  One, One,
//!         One,  Zero, One,  Zero, One, Zero, One, One,
//!     ]
//! );
//! ```
//!
//! Use it to find which bits are set in a stream:
//! ```
//! use biterator::{Biterator, Bit, BiteratorExt};
//!
//! let bytes = [0b00110101];
//! let set_bits: Vec<_> = bytes
//!     .iter()
//!     .bits()
//!     .enumerate()
//!     .filter(|(_, bit)| bit.is_one())
//!     .collect();
//!
//! assert_eq!(
//!     set_bits,
//!     vec![(2, Bit::One), (3, Bit::One), (5, Bit::One), (7, Bit::One)]
//! );
//! ```
//!
//! Count the number of bits that are 0 in a buffer:
//! ```
//! use biterator::BiteratorExt;
//!
//! // There are 10 zeros here
//! let buf = [0b00110011, 0b11001111, 0b01010101];
//!
//! let zero_bit_count = buf.iter().bits().filter(|&b| b.is_zero()).count();
//! assert_eq!(zero_bit_count, 10);
//! ```

#![warn(missing_docs)]

use std::borrow::Borrow;

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
    ///
    /// # Example
    /// ```
    /// # use biterator::Bit;
    /// let bit = Bit::Zero;
    /// assert!(bit.is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        *self == Bit::Zero
    }

    /// Check if this [`Bit`] is a one bit.
    ///
    /// # Example
    /// ```
    /// # use biterator::Bit;
    /// let bit = Bit::One;
    /// assert!(bit.is_one());
    /// ```
    pub fn is_one(&self) -> bool {
        *self == Bit::One
    }
}

/// Bits can be converted into booleans (`1` signifying `true` and `0` signifying `false`).
impl std::convert::From<Bit> for bool {
    /// # Example
    /// ```
    /// # use biterator::Bit;
    /// assert_eq!(bool::from(Bit::One), true);
    /// assert_eq!(bool::from(Bit::Zero), false);
    /// ```
    fn from(bit: Bit) -> Self {
        bit.is_one()
    }
}

/// Similarly, booleans can be converted into Bits.
impl std::convert::From<bool> for Bit {
    /// # Example
    /// ```
    /// # use biterator::Bit;
    /// assert_eq!(Bit::from(true), Bit::One);
    /// assert_eq!(Bit::from(false), Bit::Zero);
    /// ```
    fn from(b: bool) -> Self {
        match b {
            true => Bit::One,
            false => Bit::Zero,
        }
    }
}

/// [`Bit`]s are displayed as either `1` or `0`.
impl std::fmt::Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Bit::Zero => 0,
                Bit::One => 1,
            }
        )
    }
}

/// The bit index of the leftmost bit in a byte.
const LEFTMOST_BIT_INDEX: u8 = 7;
/// The bit index of the rightmost bit in a byte.
const RIGHTMOST_BIT_INDEX: u8 = 0;

/// An iterator over individual bits in a byte stream. It is generic over `I`, a type
/// which implements an iterator over a type which can be borrowed as `u8`, which
/// represents the source of bytes for the [`Biterator`].
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Biterator<I> {
    source_iter: I,
    current_byte: Option<u8>,
    current_bit_index: u8,
}

impl<I> Biterator<I>
where
    I: Iterator,
    I::Item: Borrow<u8>,
{
    /// Construct a new [`Biterator`] to iterate over the [`Bit`]s in a given source.
    /// Any type which can be converted into an iterator over items that can be
    /// borrowed as `u8`s can be used as a source.
    pub fn new<S>(source: S) -> Biterator<I>
    where
        S: IntoIterator<Item = I::Item, IntoIter = I>,
    {
        Biterator {
            source_iter: source.into_iter(),
            current_byte: None,
            current_bit_index: LEFTMOST_BIT_INDEX,
        }
    }
}

/// [`Biterator`] implements [`Iterator`] to provide an iterator over [`Bit`]s from its byte source.
impl<I> std::iter::Iterator for Biterator<I>
where
    I: Iterator,
    I::Item: Borrow<u8>,
{
    /// The [`Biterator`] iterates over [`Bit`]s.
    type Item = Bit;

    fn next(&mut self) -> Option<Self::Item> {
        // If current_byte is None, we need to draw from the source of bytes
        if self.current_byte.is_none() {
            self.current_byte = self.source_iter.next().map(|b| *b.borrow());
        }

        // Unwrap the byte, but if current_byte is still None here, then the
        // source is exhausted--and so is the Biterator
        let byte = self.current_byte?;

        // Bitmask that will extract the bit indicated by current_bit_index
        let current_bit_mask = 2u8.pow(self.current_bit_index as u32);

        if self.current_bit_index == RIGHTMOST_BIT_INDEX {
            // The rightmost bit of this byte has been reached: current_bit_index wraps
            // and we mark current_byte as None to indicate that a subsequent
            // call to next() should pull from the byte source.
            self.current_byte = None;
            self.current_bit_index = LEFTMOST_BIT_INDEX;
        } else {
            // Move one position to the right
            self.current_bit_index -= 1;
        }

        if byte & current_bit_mask > 0 {
            Some(Bit::One)
        } else {
            Some(Bit::Zero)
        }
    }
}

/// An extension trait which allows iterators to easily convert themselves into
/// [`Biterator`]s in method chains.
///
/// # Example
/// ```
/// # use biterator::BiteratorExt;
/// let ones_in_nums_over_three = [1, 2, 3, 4, 5]
///     .into_iter()
///     .filter(|&n| n > 3)
///     .bits()
///     .filter(|b| b.is_one())
///     .count();
///
/// assert_eq!(ones_in_nums_over_three, 3);
/// ```
pub trait BiteratorExt: Iterator + Sized
where
    Self::Item: Borrow<u8>,
{
    /// Converts this type into a [`Biterator`]. Simply calls [`Biterator::new`].
    fn bits(self) -> Biterator<Self> {
        Biterator::new(self)
    }
}

/// Blanket implementation of [`BiteratorExt`] for any type which satisfies its
/// trait bounds. Uses the default implementation of `bits()`.
impl<I> BiteratorExt for I
where
    I: Iterator,
    I::Item: Borrow<u8>,
{
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
    fn works_with_many_types() {
        #[rustfmt::skip]
        let expected_bits = vec![
            Zero, Zero, Zero, Zero, Zero, Zero, Zero, One, 
            Zero, Zero, Zero, Zero, Zero, Zero, One, Zero, 
            Zero, Zero, Zero, Zero, Zero, Zero, One, One,
        ];

        let from_vec = Biterator::new(vec![1u8, 2u8, 3u8]);
        assert_eq!(from_vec.collect::<Vec<_>>(), expected_bits);

        let from_array = Biterator::new([1u8, 2u8, 3u8]);
        assert_eq!(from_array.collect::<Vec<_>>(), expected_bits);

        let from_slice = Biterator::new(&[1u8, 2u8, 3u8]);
        assert_eq!(from_slice.collect::<Vec<_>>(), expected_bits);

        let from_other_iter = Biterator::new([1u8, 2u8, 3u8].into_iter().filter(|b| *b < 100));
        assert_eq!(from_other_iter.collect::<Vec<_>>(), expected_bits);

        let from_option = Biterator::new(Some(0b11001100));
        assert_eq!(
            from_option.collect::<Vec<_>>(),
            vec![One, One, Zero, Zero, One, One, Zero, Zero]
        );
    }

    #[test]
    fn convert_bits() {
        let bits = vec![One, Zero, Zero, One];
        let as_bools: Vec<bool> = bits.into_iter().map(|b| b.into()).collect();
        assert_eq!(as_bools, vec![true, false, false, true]);
    }

    #[test]
    fn bits_extension() {
        let bytes = [0b00110101];
        let bits = bytes.iter().bits().collect::<Vec<_>>();
        assert_eq!(bits, vec![Zero, Zero, One, One, Zero, One, Zero, One]);
    }
}
