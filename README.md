# biterator
[![Crates.io](https://img.shields.io/crates/v/biterator.svg)](https://crates.io/crates/biterator)
[![Documentation](https://docs.rs/biterator/badge.svg)](https://docs.rs/biterator/)

This crate provides `Biterator`, an iterator over individual bits in a source of bytes.

### Example
```rust
use biterator::{Biterator, Bit::*};

let bytes = [0b00001111, 0b10101011];
let b = Biterator::new(&bytes);

assert_eq!(
    b.collect::<Vec<_>>(),
    vec![
        Zero, Zero, Zero, Zero, One, One,  One, One,
        One,  Zero, One,  Zero, One, Zero, One, One,
    ]
);
```