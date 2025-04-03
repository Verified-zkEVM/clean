import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64

namespace Gadgets.Keccak.ThetaD
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Provable (field field2 fields)
open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)
open Clean.Gadgets.Keccak256

structure Inputs (F : Type) where
  state : KeccakState F
  d : vec_provable U64 5 F

instance : ProvableType Inputs where
  size := (ProvableType.size KeccakState) + (ProvableType.size (vec_provable U64 5))
  to_elements s := ProvableType.to_elements s.state ++ ProvableType.to_elements s.d
  from_elements v :=
    let state : KeccakState _ := ProvableType.from_elements <| v.take (ProvableType.size KeccakState)
    let d : vec_provable U64 5 _ := ProvableType.from_elements <| v.drop (ProvableType.size KeccakState)
    ⟨state, d⟩


@[reducible]
def Outputs := KeccakState

def theta_xor (inputs : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨state, d⟩ := inputs
  return #v[
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 0), (d.get 0)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 1), (d.get 0)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 2), (d.get 0)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 3), (d.get 0)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 4), (d.get 0)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 5), (d.get 1)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 6), (d.get 1)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 7), (d.get 1)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 8), (d.get 1)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 9), (d.get 1)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 10), (d.get 2)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 11), (d.get 2)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 12), (d.get 2)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 13), (d.get 2)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 14), (d.get 2)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 15), (d.get 3)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 16), (d.get 3)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 17), (d.get 3)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 18), (d.get 3)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 19), (d.get 3)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 20), (d.get 4)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 21), (d.get 4)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 22), (d.get 4)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 23), (d.get 4)⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨(state.get 24), (d.get 4)⟩
   ]

def assumptions (state : Inputs (F p)) : Prop :=
  true

def spec (state : Inputs (F p)) (out: Outputs (F p)) : Prop :=
  true

def circuit : FormalCircuit (F p) Inputs Outputs where
  main := theta_xor
  assumptions := assumptions
  spec := spec
  local_length _ := sorry
  local_length_eq := sorry
  output _ i0 := sorry
  output_eq := sorry

  soundness := by sorry
  completeness := by sorry
end Gadgets.Keccak.ThetaD
