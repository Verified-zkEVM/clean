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

@[reducible]
def Inputs := vec_provable U64 5

@[reducible]
def Outputs := vec_provable U64 5

def theta_d (state : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨c0⟩ ← subcircuit (Gadgets.Rotation64.circuit 1) ⟨state.get 1⟩
  let ⟨c0⟩ ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 4)⟩

  let ⟨c1⟩ ← subcircuit (Gadgets.Rotation64.circuit 1) ⟨state.get 2⟩
  let ⟨c1⟩ ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 0)⟩

  let ⟨c2⟩ ← subcircuit (Gadgets.Rotation64.circuit 1) ⟨state.get 3⟩
  let ⟨c2⟩ ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 1)⟩

  let ⟨c3⟩ ← subcircuit (Gadgets.Rotation64.circuit 1) ⟨state.get 4⟩
  let ⟨c3⟩ ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 2)⟩

  let ⟨c4⟩ ← subcircuit (Gadgets.Rotation64.circuit 1) ⟨state.get 0⟩
  let ⟨c4⟩ ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 3)⟩

  return #v[c0, c1, c2, c3, c4]

def assumptions (state : Inputs (F p)) : Prop :=
  -- TODO
  true

def spec (state : Inputs (F p)) (out: Outputs (F p)) : Prop :=
  true

def circuit : FormalCircuit (F p) Inputs Outputs where
  main := theta_d
  assumptions := assumptions
  spec := spec
  local_length _ := sorry
  local_length_eq := sorry
  output _ i0 := sorry
  output_eq := sorry

  soundness := by sorry
  completeness := by sorry
end Gadgets.Keccak.ThetaD
