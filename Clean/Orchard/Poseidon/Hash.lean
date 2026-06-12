import Clean.Orchard.Poseidon.Sponge

/-!
# Orchard Poseidon hash APIs

This module mirrors `halo2_gadgets/src/poseidon.rs::Hash` for the source-shaped pieces
that can be expressed once a full padded rate-2 block is available.
-/

namespace Orchard
namespace Poseidon
namespace Hash

/-- Source file mirrored by this module. -/
def sourceFile : String := "halo2_gadgets/src/poseidon.rs"

namespace Init

/-- `Hash::init`: construct a sponge by calling `Pow5Chip::initial_state`. -/
def main (capacity : Ecc.Fp) : Var unit Ecc.Fp → Circuit Ecc.Fp (Var Permute.State Ecc.Fp) :=
  Sponge.InitialState.circuit capacity

def Spec (capacity : Ecc.Fp) (_ : Unit) (output : Permute.State Ecc.Fp) : Prop :=
  Sponge.InitialState.Spec capacity () output

/-- Packaged `Hash::init` state initialization. -/
def circuit (capacity : Ecc.Fp) : FormalCircuit Ecc.Fp unit Permute.State where
  name := "Hash::init"
  main := main capacity
  Spec := Spec capacity
  soundness := by
    circuit_proof_start [main, Sponge.InitialState.circuit, Spec, Sponge.InitialState.Spec]
    exact h_holds
  completeness := by
    circuit_proof_start [main, Sponge.InitialState.circuit, Spec, Sponge.InitialState.Spec]

end Init

namespace HashPaddedBlock

/-- Value-level one-block hash after the caller/domain has prepared a full padded rate-2
block.  This is the straight-line source composition `init -> add_input -> permute ->
squeeze first`. -/
def value (roundConstants : Nat → Permute.State Ecc.Fp) (capacity : Ecc.Fp)
    (block : Sponge.Rate2 Ecc.Fp) : Ecc.Fp :=
  let initial : Permute.State Ecc.Fp := { x0 := 0, x1 := 0, x2 := capacity }
  let absorbed := Sponge.AddInput.value { initialState := initial, input := block }
  let permuted := Permute.permuteP128Value roundConstants absorbed
  (Sponge.GetOutput.value permuted).x0

/-- `Hash::hash` for one already-padded rate-2 block. -/
def main (roundConstants : Nat → Permute.State Ecc.Fp) (capacity : Ecc.Fp)
    (block : Var Sponge.Rate2 Ecc.Fp) : Circuit Ecc.Fp (Expression Ecc.Fp) := do
  let initial ← Init.circuit capacity ()
  let absorbed ← Sponge.AddInput.circuit { initialState := initial, input := block }
  let permuted ← Permute.mainP128Circuit roundConstants absorbed
  let output ← Sponge.GetOutput.circuit permuted
  return output.x0

def Spec (roundConstants : Nat → Permute.State Ecc.Fp) (capacity : Ecc.Fp)
    (block : Sponge.Rate2 Ecc.Fp) (output : Ecc.Fp) : Prop :=
  output = value roundConstants capacity block

/-- Packaged one-padded-block `Hash::hash` composition. -/
def circuit (roundConstants : Nat → Permute.State Ecc.Fp) (capacity : Ecc.Fp) :
    FormalCircuit Ecc.Fp Sponge.Rate2 field where
  name := "Hash::hash[padded_block]"
  main := main roundConstants capacity
  Spec := Spec roundConstants capacity
  soundness := by
    circuit_proof_start [main, value, Init.circuit, Sponge.InitialState.circuit,
      Sponge.AddInput.circuit, Permute.mainP128Circuit, Sponge.GetOutput.circuit,
      Sponge.InitialState.Spec, Sponge.AddInput.Spec, Sponge.GetOutput.Spec]
    rcases h_holds with ⟨hinit, habsorb, hpermute, houtput⟩
    rw [hinit] at habsorb
    rw [habsorb] at hpermute
    rw [hpermute] at houtput
    simpa [Sponge.GetOutput.value] using congrArg Sponge.Rate2.x0 houtput
  completeness := by
    circuit_proof_start [main, value, Init.circuit, Sponge.InitialState.circuit,
      Sponge.AddInput.circuit, Permute.mainP128Circuit, Sponge.GetOutput.circuit,
      Sponge.InitialState.Spec, Sponge.AddInput.Spec, Sponge.GetOutput.Spec]

/-- Concrete one-padded-block P128 hash value using ported round constants. -/
def concreteValue (capacity : Ecc.Fp) (block : Sponge.Rate2 Ecc.Fp) : Ecc.Fp :=
  value Permute.P128Pow5T3.roundConstants capacity block

/-- Concrete one-padded-block P128 hash circuit using ported round constants. -/
def concreteCircuit (capacity : Ecc.Fp) : FormalCircuit Ecc.Fp Sponge.Rate2 field :=
  circuit Permute.P128Pow5T3.roundConstants capacity

end HashPaddedBlock

namespace ConstantLength

/-- Number of rate-2 blocks after padding a constant-length message of length `L` with
zeroes to a multiple of the rate.  This is `(L + RATE - 1) / RATE` for `RATE = 2`. -/
def blockCount (L : Nat) : Nat :=
  (L + 1) / 2

/-- Capacity element for `halo2_poseidon::ConstantLength<L>` with output length one:
`L * 2^64`. -/
def capacity (L : Nat) : Ecc.Fp :=
  (L * 2 ^ 64 : Nat)

/-- Value-level padded word at a flattened padded index. -/
def paddedWord {L : Nat} (message : Vector Ecc.Fp L) (idx : Nat) : Ecc.Fp :=
  if h : idx < L then message.get ⟨idx, h⟩ else 0

/-- Circuit-level padded word at a flattened padded index. -/
def paddedVar {L : Nat} (message : Vector (Expression Ecc.Fp) L) (idx : Nat) :
    Expression Ecc.Fp :=
  if h : idx < L then message.get ⟨idx, h⟩ else 0

/-- Value-level padded rate-2 block. -/
def blockValue {L : Nat} (message : Vector Ecc.Fp L) (i : Nat) : Sponge.Rate2 Ecc.Fp :=
  { x0 := paddedWord message (2 * i), x1 := paddedWord message (2 * i + 1) }

/-- Circuit-level padded rate-2 block. -/
def blockVar {L : Nat} (message : Vector (Expression Ecc.Fp) L) (i : Nat) :
    Var Sponge.Rate2 Ecc.Fp :=
  { x0 := paddedVar message (2 * i), x1 := paddedVar message (2 * i + 1) }

/-- Value-level state after absorbing and permuting one padded block. -/
def absorbPermuteValue (input : Sponge.AddInputInput Ecc.Fp) : Permute.State Ecc.Fp :=
  Permute.permuteP128ConcreteValue (Sponge.AddInput.value input)

namespace AbsorbPermute

/-- Source-shaped one-block sponge step: `add_input -> permute`. -/
def main (input : Var Sponge.AddInputInput Ecc.Fp) : Circuit Ecc.Fp (Var Permute.State Ecc.Fp) := do
  let absorbed ← Sponge.AddInput.circuit input
  Permute.mainP128ConcreteCircuit absorbed

def Spec (input : Sponge.AddInputInput Ecc.Fp) (output : Permute.State Ecc.Fp) : Prop :=
  output = absorbPermuteValue input

/-- Packaged one-block sponge step used by the `ConstantLength<L>` scheduler. -/
def circuit : FormalCircuit Ecc.Fp Sponge.AddInputInput Permute.State where
  name := "Hash::hash[ConstantLength]/absorb_permute_block"
  main
  Spec
  soundness := by
    circuit_proof_start [main, Spec, absorbPermuteValue, Sponge.AddInput.circuit,
      Permute.mainP128ConcreteCircuit]
    rcases h_holds with ⟨habsorb, hpermute⟩
    rw [habsorb] at hpermute
    constructor
    · simpa using hpermute trivial
    · simp [Permute.mainP128Circuit]
  completeness := by
    circuit_proof_start [main, Spec, absorbPermuteValue, Sponge.AddInput.circuit,
      Permute.mainP128ConcreteCircuit]
    trivial

end AbsorbPermute

/-- Value-level `Hash::hash` for `ConstantLength<L>`. -/
def value {L : Nat} (message : Vector Ecc.Fp L) : Ecc.Fp :=
  let initial : Permute.State Ecc.Fp := { x0 := 0, x1 := 0, x2 := capacity L }
  let finalState := Fin.foldl (blockCount L)
    (fun state i => absorbPermuteValue { initialState := state, input := blockValue message i.val })
    initial
  (Sponge.GetOutput.value finalState).x0

/-- Source-shaped `Hash::hash` for `ConstantLength<L>`, specialized to P128Pow5T3. -/
def main {L : Nat} (message : Vector (Expression Ecc.Fp) L) :
    Circuit Ecc.Fp (Expression Ecc.Fp) := do
  let initial ← Init.circuit (capacity L) ()
  let finalState ← Circuit.foldlRange (blockCount L) initial
    (fun state i => AbsorbPermute.circuit { initialState := state, input := blockVar message i.val })
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      simp [AbsorbPermute.circuit, circuit_norm])
  let output ← Sponge.GetOutput.circuit finalState
  return output.x0

/-- Spec for `Hash::hash` over `ConstantLength<L>`. -/
def Spec {L : Nat} (message : Vector Ecc.Fp L) (output : Ecc.Fp) : Prop :=
  output = value message

/-!
The source-shaped generic scheduler above mirrors the `ConstantLength<L>` padding loop.
Packaging its dependent `foldlRange` proof is the remaining proof task; fixed one-block
hashes are already packaged by `HashPaddedBlock.circuit`.
-/

end ConstantLength

end Hash
end Poseidon
end Orchard
