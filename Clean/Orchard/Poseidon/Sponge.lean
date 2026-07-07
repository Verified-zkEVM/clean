import Clean.Orchard.Poseidon.Pow5

/-!
# Orchard Poseidon sponge APIs

This module mirrors `halo2_gadgets/src/poseidon.rs` around `Sponge`,
`poseidon_sponge`, and `PoseidonSpongeInstructions` for Orchard's width-3/rate-2
`P128Pow5T3` instance.
-/

namespace Orchard.Poseidon.Sponge

/-- The rate-2 part of a P128 Poseidon state. -/
structure Rate2 (F : Type) where
  x0 : F
  x1 : F
deriving ProvableStruct

/-- Input to `Pow5Chip::add_input`: a previous state and two already-padded rate words. -/
structure AddInputInput (F : Type) where
  initialState : Permute.State F
  input : Rate2 F
deriving ProvableStruct

namespace InitialState

/-- `Pow5Chip::initial_state` for width 3/rate 2.  The capacity element is supplied by
  the domain (`D::initial_capacity_element()` in Halo2). -/
def main (capacity : Fp) (_ : Var unit Fp) : Circuit Fp (Var Permute.State Fp) := do
  let x0 <== (0 : Expression Fp)
  let x1 <== (0 : Expression Fp)
  let x2 <== (capacity : Expression Fp)
  return { x0, x1, x2 }

def Spec (capacity : Fp) (_ : Unit) (output : Permute.State Fp) : Prop :=
  output = { x0 := 0, x1 := 0, x2 := capacity }

/-- Packaged `Pow5Chip::initial_state`. -/
def circuit (capacity : Fp) : FormalCircuit Fp unit Permute.State where
  name := "Pow5Chip::initial_state"
  main := main capacity
  Spec := Spec capacity
  soundness := by
    circuit_proof_start [main, Spec]
    simp_all
  completeness := by
    circuit_proof_start [main, Spec]
    exact h_env

end InitialState

namespace AddInput

/-- Value-level effect of `Pow5Chip::add_input`: add the two rate words and preserve the
capacity element. -/
def value (input : AddInputInput Fp) : Permute.State Fp :=
  { x0 := input.initialState.x0 + input.input.x0
    x1 := input.initialState.x1 + input.input.x1
    x2 := input.initialState.x2 }

/-- Source-shaped `Pow5Chip::add_input` for width 3/rate 2.  The input words are assumed
already padded, matching the `Absorbing<PaddedWord<F>, RATE>` argument after the sponge
mode has produced a full padded rate block. -/
def main (input : Var AddInputInput Fp) : Circuit Fp (Var Permute.State Fp) := do
  -- Halo2 copies the initial state and input words into a fresh region before enabling
  -- the pad-and-add gate, so we allocate fresh cells and constrain them equal here.
  let initial0 <== input.initialState.x0
  let initial1 <== input.initialState.x1
  let initial2 <== input.initialState.x2
  let input0 <== input.input.x0
  let input1 <== input.input.x1
  let output ← witness <|
    Permute.State.mk (input.initialState.x0 + input.input.x0)
      (input.initialState.x1 + input.input.x1)
      input.initialState.x2
  PadAndAdd.circuit
    { initial0, initial1, initial2, input0, input1,
      output0 := output.x0, output1 := output.x1, output2 := output.x2 }
  return output

def Spec (input : AddInputInput Fp) (output : Permute.State Fp) : Prop :=
  output = value input

/-- Packaged `Pow5Chip::add_input`. -/
def circuit : FormalCircuit Fp AddInputInput Permute.State where
  name := "Pow5Chip::add_input"
  main
  Spec
  soundness := by
    circuit_proof_start [main, Spec, value, PadAndAdd.circuit, PadAndAdd.Spec]
    rcases h_holds with ⟨hcopy0, hcopy1, hcopy2, hcopy3, hcopy4, hpad⟩
    rcases hpad with ⟨h0, h1, h2⟩
    simp [Permute.State.mk.injEq] at hcopy0 hcopy1 hcopy2 hcopy3 hcopy4 h0 h1 h2 ⊢
    exact ⟨by simpa [hcopy0, hcopy3] using h0,
      by simpa [hcopy1, hcopy4] using h1,
      by simpa [hcopy2] using h2⟩
  completeness := by
    -- TODO(4.30 bump): legacy defeq so circuit_norm's witness-IR completeness lemmas
    -- keep matching through stuck size indices (lean4#12179); see Pow5.circuitP128.
    set_option backward.isDefEq.respectTransparency false in
    circuit_proof_start [main, Spec, value, PadAndAdd.circuit, PadAndAdd.Spec]
    rcases h_env with ⟨hinit0, hinit1, hinit2, hinput0, hinput1, houtput⟩
    simp only [circuit_norm, Permute.State.mk.injEq] at houtput
    obtain ⟨hout0, hout1, hout2⟩ := houtput
    exact ⟨hinit0, hinit1, hinit2, hinput0, hinput1,
      by
        constructor
        · rw [hinit0, hinput0]
          exact hout0
        constructor
        · rw [hinit1, hinput1]
          exact hout1
        · rw [hinit2]
          exact hout2⟩

end AddInput

namespace GetOutput

/-- `PoseidonSpongeInstructions::get_output`: expose the rate portion of the state. -/
def value (state : Permute.State Fp) : Rate2 Fp :=
  { x0 := state.x0, x1 := state.x1 }

def main (state : Var Permute.State Fp) : Circuit Fp (Var Rate2 Fp) :=
  return { x0 := state.x0, x1 := state.x1 }

def Spec (state : Permute.State Fp) (output : Rate2 Fp) : Prop :=
  output = value state

/-- Packaged `PoseidonSpongeInstructions::get_output`. -/
def circuit : FormalCircuit Fp Permute.State Rate2 where
  name := "PoseidonSpongeInstructions::get_output"
  main
  Spec
  soundness := by
    circuit_proof_start [main, Spec, value]
  completeness := by
    circuit_proof_start [main, Spec, value]

end GetOutput

end Orchard.Poseidon.Sponge
