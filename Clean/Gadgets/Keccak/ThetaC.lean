import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Addition32.Theorems
import Clean.Gadgets.Xor.Xor64

namespace Gadgets.Keccak.ThetaC
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)

@[reducible] def State := ProvableVector U64 25
@[reducible] def Outputs := ProvableVector U64 5
-- note: `reducible` is needed for type class inference, i.e. `ProvableType State`

def theta_c (state : Var State (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 0), (state.get 1)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 2)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 3)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 4)⟩

  let c1 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 5), (state.get 6)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 7)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 8)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 9)⟩

  let c2 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 10), (state.get 11)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 12)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 13)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 14)⟩

  let c3 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 15), (state.get 16)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 17)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 18)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 19)⟩

  let c4 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 20), (state.get 21)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 22)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 23)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 24)⟩
  return #v[c0, c1, c2, c3, c4]

def assumptions (state : State (F p)) : Prop :=
  -- TODO
  true

def spec (state : State (F p)) (out: Outputs (F p)) : Prop :=
  -- TODO
  true

#eval! theta_c (p:=p_babybear) default |>.operations.local_length
#eval! theta_c (p:=p_babybear) default |>.output

def circuit : FormalCircuit (F p) State Outputs where
  main := theta_c
  assumptions := assumptions
  spec := spec
  local_length _ := 160
  output _ i0 := #v[
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 152)
  ]
  soundness := by sorry
  completeness := by sorry
end Gadgets.Keccak.ThetaC
