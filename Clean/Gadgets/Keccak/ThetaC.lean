import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Addition32.Theorems
import Clean.Gadgets.Xor.Xor64

namespace Gadgets.Keccak.ThetaC
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Provable (field field2 fields)
open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)

structure Inputs (F : Type) where
  state: Vector (U64 F) 25

instance instProvableTypeInputs : ProvableType Inputs where
  size := 25 * ProvableType.size U64
  to_elements x := sorry
  from_elements v := sorry

structure Outputs (F : Type) where
  c : Vector (U64 F) 5

instance instProvableTypeOutputs : ProvableType Outputs where
  size := 5 * ProvableType.size U64
  to_elements x := sorry
  from_elements v := sorry

def theta_c (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨state⟩ := input

  let ⟨c0⟩ ← subcircuit Gadgets.Xor.circuit ⟨(state.get 0), (state.get 1)⟩
  let ⟨c0⟩ ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 2)⟩
  let ⟨c0⟩ ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 3)⟩
  let ⟨c0⟩ ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 4)⟩

  let ⟨c1⟩ ← subcircuit Gadgets.Xor.circuit ⟨(state.get 5), (state.get 6)⟩
  let ⟨c1⟩ ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 7)⟩
  let ⟨c1⟩ ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 8)⟩
  let ⟨c1⟩ ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 9)⟩

  let ⟨c2⟩ ← subcircuit Gadgets.Xor.circuit ⟨(state.get 10), (state.get 11)⟩
  let ⟨c2⟩ ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 12)⟩
  let ⟨c2⟩ ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 13)⟩
  let ⟨c2⟩ ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 14)⟩

  let ⟨c3⟩ ← subcircuit Gadgets.Xor.circuit ⟨(state.get 15), (state.get 16)⟩
  let ⟨c3⟩ ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 17)⟩
  let ⟨c3⟩ ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 18)⟩
  let ⟨c3⟩ ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 19)⟩

  let ⟨c4⟩ ← subcircuit Gadgets.Xor.circuit ⟨(state.get 20), (state.get 21)⟩
  let ⟨c4⟩ ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 22)⟩
  let ⟨c4⟩ ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 23)⟩
  let ⟨c4⟩ ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 24)⟩
  return { c := #v[c0, c1, c2, c3, c4] }

def assumptions (input : Inputs (F p)) : Prop :=
  let ⟨state⟩ := input
  -- TODO
  true

def spec (input : Inputs (F p)) (out: Outputs (F p)) : Prop :=
  let ⟨state⟩ := input
  -- TODO
  true

def circuit : FormalCircuit (F p) Inputs Outputs where
  main := theta_c
  assumptions := assumptions
  spec := spec
  soundness := by sorry
  completeness := by sorry
end Gadgets.Keccak.ThetaC
