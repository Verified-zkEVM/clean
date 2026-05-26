# SHA-256 Gadgets

This folder contains a bit-level SHA-256 compression circuit. The construction expands a 16-word block into the 64-word message schedule, runs the 64 compression rounds, and adds the original state back into the result. It is proven correct with respect to the Lean SHA-256 specification in [`Clean/Specs/SHA256.lean`](../../Specs/SHA256.lean).

## Design Choices

SHA-256 words are represented as `fields 32`: 32 boolean field elements in
least-significant-bit-first order. A `u32` is therefore a bit string, not a
packed field element.

Operations are implemented bitwise over those words. Rotations and shifts are
rewiring operations; word-level functions compose bitwise boolean operations and
modular addition.

The target fields are prime fields with `p > 2^33`. This is enough headroom for
the natural-number interpretation used by 32-bit modular addition.

The circuit does not use lookup tables. It is built only from ordinary circuit
constraints, so the design is compatible with R1CS-style backends.

## Templates

- `BitwiseOps.lean`: shared word, state, block, and schedule types; pure helpers
  for constants, bit interpretation, rotations, shifts, and normalization.
- `And32.lean`: bitwise 32-bit AND.
- `Xor32.lean`: bitwise 32-bit XOR.
- `Add32.lean`: 32-bit addition modulo `2^32`.
- `Ch32.lean`: SHA-256 choice function.
- `Maj32.lean`: SHA-256 majority function.
- `LowerSigma0.lean`: message schedule `sigma0`.
- `LowerSigma1.lean`: message schedule `sigma1`.
- `UpperSigma0.lean`: round function `Sigma0`.
- `UpperSigma1.lean`: round function `Sigma1`.
- `SHA256Schedule.lean`: expands a 16-word message block into 64 schedule words.
- `SHA256Round.lean`: implements one SHA-256 compression round.
- `SHA256Compress.lean`: composes schedule expansion, 64 rounds, and final state addition into the compression circuit.
