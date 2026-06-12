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

end HashPaddedBlock

end Hash
end Poseidon
end Orchard
