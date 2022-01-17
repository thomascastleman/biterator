//! This crate provides [`Biterator`], a type for iterating over individual bits
//! in a stream of bytes.

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

/// An iterator over individual bits in a slice.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Biterator<'src> {
    source: &'src [u8],
    bit_index: u8,
}

impl Biterator<'_> {
    /// Construct a new `Biterator` to iterate over the bits in a given source,
    /// which is a slice of bytes.
    pub fn new(source: &[u8]) -> Biterator<'_> {
        Biterator {
            source,
            bit_index: 0,
        }
    }
}

/// The maximum value of an index into a byte (0-7)
const MAX_BIT_INDEX: u8 = 7;

impl std::iter::Iterator for Biterator<'_> {
    type Item = Bit;

    fn next(&mut self) -> Option<Self::Item> {
        // Extract the current byte we're pulling bits from--if there is none,
        // then the Biterator is exhausted.
        let byte = self.source.first()?;

        // Bitmask that will extract the bit indicated by bit_index
        let current_bit_mask = 2u8.pow((MAX_BIT_INDEX - self.bit_index) as u32);

        // Update the bit index to point to the next bit (wrapping)
        self.bit_index = (self.bit_index + 1) % 8;

        // If we just rolled over into a new byte, move along the source slice
        if self.bit_index == 0 {
            self.source = &self.source[1..];
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
