/-
The inputs of Plonky3's Keccak-f AIR as witness generation reads them, packed, over any field with
word conversions.
-/
module

public import Clean.Air.WitnessGeneration.Packed
public import Clean.Examples.KeccakAir.Ensemble

@[expose] public section

namespace KeccakAir
open Air.Flat

/-- The height of the trace of `n` permutations, Plonky3's `(24 n).next_power_of_two()`. -/
def traceHeight (n : ℕ) : ℕ := (24 * n).nextPowerOfTwo

/-- A Keccak-f state in Plonky3's input order: lane `(x, y)` at `x + 5 y`. -/
abbrev State := Vector UInt64 25

/-- The 100 16-bit limbs of a permutation's input, in the order of the `preimage` columns: limb `l`
of lane `(x, y)` at `(5 y + x) 4 + l`. -/
def preimageLimbs (input : State) : List ℕ :=
  (List.range 100).map fun j => (input[j / 4]! >>> (16 * (j % 4)).toUInt64).toNat % 2 ^ 16

/-- The ensemble's packed private input over `K` for the permutations of `inputs`: a row of
`preimageLimbs` per input. Elements past the inputs read as zero, the limbs of the zero state that
pads the trace. -/
def proverInput {K : Type} [FiniteField K] [WordField K] [CompPoly.PackedRepr K]
    (inputs : Array State) : ByteArray := Id.run do
  let mut elements := ByteArray.zeros (CompPoly.PackedRepr.width K * (100 * inputs.size))
  for h : k in [0:inputs.size] do
    let input := inputs[k]
    for i in [0:25] do
      for l in [0:4] do
        let limb := (input[i]! >>> (16 * l).toUInt64) &&& 0xffff
        elements := WitnessGeneration.storeElement elements (100 * k + 4 * i + l)
          (WordField.ofSmallWord limb : K)
  return elements

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 16 < p)]

/-- The hint tables over `K` of the trace of the permutations of `inputs`. -/
def hints (K : Type) [FiniteField K] [WordField K] [CompPoly.PackedRepr K]
    (inputs : Array State) : Array ByteArray :=
  WitnessGeneration.packedHints K (ensemble (p := p) (traceHeight inputs.size).toUInt64).hintTables
    (proverInput (K := K) inputs)

end KeccakAir
