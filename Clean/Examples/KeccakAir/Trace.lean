/-
The trace of Plonky3's Keccak-f AIR, computed as Plonky3's `generate_trace_rows` does: 24 rows per
permutation, padded to a power of two with the rows of the permutation of the zero state.
-/
module

public import Clean.Examples.KeccakAir.Air

@[expose] public section

namespace KeccakAir.Trace
open Specs.Keccak256

/-- A Keccak-f state in Plonky3's input order: lane `(x, y)` at `x + 5 y`. -/
abbrev State := Vector UInt64 25

def lane (state : State) (x y : ℕ) : UInt64 := state[(x % 5) + 5 * (y % 5)]!

def rotateLeft (value : UInt64) (offset : ℕ) : UInt64 :=
  if offset % 64 = 0 then value
  else (value <<< (offset % 64).toUInt64) ||| (value >>> (64 - offset % 64).toUInt64)

/-- The 16-bit limbs of a lane, lowest first. -/
def limbs (value : UInt64) : List ℕ :=
  (List.range 4).map fun limb => (value >>> (16 * limb).toUInt64).toNat % 2 ^ 16

/-- The bits of a lane, lowest first. -/
def bits (value : UInt64) : List ℕ :=
  (List.range 64).map fun z => (value >>> z.toUInt64).toNat % 2

/-- The cells of a lane-indexed quantity, `y`-major. -/
def yMajor (cells : UInt64 → List ℕ) (value : ℕ → ℕ → UInt64) : List ℕ :=
  (List.range 5).flatMap fun y => (List.range 5).flatMap fun x => cells (value x y)

/-- The row of round `round` with input `state` of the permutation of `preimage`, and the round's
output. -/
def roundRow (preimage state : State) (round : ℕ) : List ℕ × State :=
  let a := lane state
  let c (x : ℕ) : UInt64 := a x 0 ^^^ a x 1 ^^^ a x 2 ^^^ a x 3 ^^^ a x 4
  let cPrime (x : ℕ) : UInt64 := c x ^^^ c (x + 4) ^^^ rotateLeft (c (x + 1)) 1
  let aPrime (x y : ℕ) : UInt64 := a x y ^^^ c (x % 5) ^^^ cPrime (x % 5)
  let b (x y : ℕ) : UInt64 :=
    let source := (x + 3 * y) % 5
    rotateLeft (aPrime source x) ((rotationOffsets[source]!)[x % 5]!).val
  let aPrimePrime (x y : ℕ) : UInt64 := b x y ^^^ (~~~(b (x + 1) y) &&& b (x + 2) y)
  let roundConstant := roundConstants[round]!
  let output (x y : ℕ) : UInt64 :=
    if x % 5 = 0 ∧ y % 5 = 0 then aPrimePrime 0 0 ^^^ roundConstant else aPrimePrime x y
  let cells :=
    (List.range 24).map (fun r => if r = round then 1 else 0) ++ [0] ++
    yMajor limbs (lane preimage) ++ yMajor limbs a ++
    (List.range 5).flatMap (fun x => bits (c x)) ++
    (List.range 5).flatMap (fun x => bits (cPrime x)) ++
    yMajor bits aPrime ++ yMajor limbs aPrimePrime ++
    bits (aPrimePrime 0 0) ++ limbs (aPrimePrime 0 0 ^^^ roundConstant)
  (cells, Vector.ofFn fun i => output (i.val % 5) (i.val / 5))

/-- The 24 rows of the permutation of `preimage`, and its output. -/
def permutationRows (preimage : State) : List (List ℕ) × State :=
  (List.range 24).foldl (fun (rows, state) round =>
    let (row, output) := roundRow preimage state round
    (rows ++ [row], output)) ([], preimage)

/-- The trace of the permutations of `inputs`: 24 rows per permutation, followed by the rows of the
permutation of the zero state up to a power of two. -/
def rows (inputs : List State) : List (List ℕ) :=
  let real := inputs.flatMap fun input => (permutationRows input).1
  let height := (24 * inputs.length).nextPowerOfTwo
  let padding := (permutationRows (Vector.replicate 25 0)).1
  real ++ (List.range (height - real.length)).map fun i => padding[i % 24]!

end KeccakAir.Trace
