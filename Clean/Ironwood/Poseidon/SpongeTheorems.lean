import Clean.Ironwood.Poseidon.Pow5Theorems

/-!
# Orchard Poseidon sponge APIs

This module mirrors `halo2_gadgets/src/poseidon.rs` around `Sponge`,
`poseidon_sponge`, and `PoseidonSpongeInstructions` for Orchard's width-3/rate-2
`P128Pow5T3` instance.
-/

namespace Halo2.Ironwood.Poseidon.Sponge

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

def Spec (capacity : Fp) (_ : Unit) (output : Permute.State Fp) : Prop :=
  output = { x0 := 0, x1 := 0, x2 := capacity }

end InitialState

namespace AddInput

/-- Value-level effect of `Pow5Chip::add_input`: add the two rate words and preserve the
capacity element. -/
def value (input : AddInputInput Fp) : Permute.State Fp :=
  { x0 := input.initialState.x0 + input.input.x0
    x1 := input.initialState.x1 + input.input.x1
    x2 := input.initialState.x2 }

def Spec (input : AddInputInput Fp) (output : Permute.State Fp) : Prop :=
  output = value input

end AddInput

namespace GetOutput

/-- `PoseidonSpongeInstructions::get_output`: expose the rate portion of the state. -/
def value (state : Permute.State Fp) : Rate2 Fp :=
  { x0 := state.x0, x1 := state.x1 }

def Spec (state : Permute.State Fp) (output : Rate2 Fp) : Prop :=
  output = value state

end GetOutput

end Halo2.Ironwood.Poseidon.Sponge
