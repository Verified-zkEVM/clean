import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.And.And64
import Clean.Gadgets.Not.Not64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.Chi
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]
open Gadgets.Keccak256 (KeccakState)
open Bitwise (not64)
open Not (not64_bytewise not64_bytewise_value)

def xor (x y : Var U64 (F p)) := subcircuit Xor.circuit ⟨x, y⟩
def and (x y : Var U64 (F p)) := subcircuit And.And64.circuit ⟨x, y⟩
def not (x : Var U64 (F p)) := subcircuit Not.circuit x

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do return #v[
  ←xor (state.get 0) (←and (←not (state.get 5)) (state.get 10)),
  ←xor (state.get 1) (←and (←not (state.get 6)) (state.get 11)),
  ←xor (state.get 2) (←and (←not (state.get 7)) (state.get 12)),
  ←xor (state.get 3) (←and (←not (state.get 8)) (state.get 13)),
  ←xor (state.get 4) (←and (←not (state.get 9)) (state.get 14)),
  ←xor (state.get 5) (←and (←not (state.get 10)) (state.get 15)),
  ←xor (state.get 6) (←and (←not (state.get 11)) (state.get 16)),
  ←xor (state.get 7) (←and (←not (state.get 12)) (state.get 17)),
  ←xor (state.get 8) (←and (←not (state.get 13)) (state.get 18)),
  ←xor (state.get 9) (←and (←not (state.get 14)) (state.get 19)),
  ←xor (state.get 10) (←and (←not (state.get 15)) (state.get 20)),
  ←xor (state.get 11) (←and (←not (state.get 16)) (state.get 21)),
  ←xor (state.get 12) (←and (←not (state.get 17)) (state.get 22)),
  ←xor (state.get 13) (←and (←not (state.get 18)) (state.get 23)),
  ←xor (state.get 14) (←and (←not (state.get 19)) (state.get 24)),
  ←xor (state.get 15) (←and (←not (state.get 20)) (state.get 0)),
  ←xor (state.get 16) (←and (←not (state.get 21)) (state.get 1)),
  ←xor (state.get 17) (←and (←not (state.get 22)) (state.get 2)),
  ←xor (state.get 18) (←and (←not (state.get 23)) (state.get 3)),
  ←xor (state.get 19) (←and (←not (state.get 24)) (state.get 4)),
  ←xor (state.get 20) (←and (←not (state.get 0)) (state.get 5)),
  ←xor (state.get 21) (←and (←not (state.get 1)) (state.get 6)),
  ←xor (state.get 22) (←and (←not (state.get 2)) (state.get 7)),
  ←xor (state.get 23) (←and (←not (state.get 3)) (state.get 8)),
  ←xor (state.get 24) (←and (←not (state.get 4)) (state.get 9))
]

def assumptions := KeccakState.is_normalized (p:=p)

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value

-- #eval! main (p:=p_babybear) default |>.operations.local_length
-- #eval! main (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState (Var KeccakState (F p)) where
  main
  local_length _ := 400
  local_length_eq state i := by
    dsimp only [circuit_norm, main, not, xor, and, Xor.circuit, And.And64.circuit, Not.circuit]

  output _ i0 := #v[
    var_from_offset U64 (i0 + 8),
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 40),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 72),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 104),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 136),
    var_from_offset U64 (i0 + 152),
    var_from_offset U64 (i0 + 168),
    var_from_offset U64 (i0 + 184),
    var_from_offset U64 (i0 + 200),
    var_from_offset U64 (i0 + 216),
    var_from_offset U64 (i0 + 232),
    var_from_offset U64 (i0 + 248),
    var_from_offset U64 (i0 + 264),
    var_from_offset U64 (i0 + 280),
    var_from_offset U64 (i0 + 296),
    var_from_offset U64 (i0 + 312),
    var_from_offset U64 (i0 + 328),
    var_from_offset U64 (i0 + 344),
    var_from_offset U64 (i0 + 360),
    var_from_offset U64 (i0 + 376),
    var_from_offset U64 (i0 + 392)
  ]
  output_eq state i := by
    dsimp only [circuit_norm, main, not, xor, and, Xor.circuit, And.And64.circuit, Not.circuit]

theorem soundness : Soundness (F p) assumptions spec := by
  intro i env state_var state h_input state_norm h_holds

  have h_input' (i : Fin 25) : eval env state_var[i.val] = state[i.val] := by
    rw [←h_input, eval_vector, Vector.getElem_map]

  have h_input_not (i : Fin 25) : (eval env (not64_bytewise state_var[i.val])) = not64_bytewise_value state[i.val] := by
    rw [←h_input', Not.eval_not]

  have h_not_value (i : Fin 25) : (not64_bytewise_value state[i.val]).value = not64 state[i.val].value :=
    (Not.not_bytewise_value_spec (state_norm i)).left

  have h_not_normalized (i : Fin 25) : (not64_bytewise_value state[i.val]).is_normalized :=
    (Not.not_bytewise_value_spec (state_norm i)).right

  simp only [circuit_norm, spec, KeccakState.is_normalized_iff,
    Specs.Keccak256.chi, KeccakState.value, eval_vector,
    Array.mk.injEq, List.cons.injEq, and_true]
  simp only [assumptions, KeccakState.is_normalized, Fin.getElem_fin] at state_norm

  dsimp only [circuit_norm, main,
    not, xor, and, Xor.circuit, And.And64.circuit, Not.circuit] at h_holds
  simp only [circuit_norm, subcircuit_norm, Xor.assumptions, Xor.spec,
    And.And64.assumptions, And.And64.spec] at h_holds

  simp only [h_input', h_input_not, h_not_value, state_norm, h_not_normalized,
    and_self, imp_self, forall_const, true_and, and_imp, and_assoc, and_true] at h_holds

  simp_all [not64, Specs.Keccak256.not_u64]
  and_intros <;> rfl

theorem completeness : Completeness (F p) KeccakState assumptions := by
  intro i env state_var h_env state h_input state_norm

  have h_input' (i : Fin 25) : eval env state_var[i.val] = state[i.val] := by
    rw [←h_input, eval_vector, Vector.getElem_map]

  have h_input_not (i : Fin 25) : (eval env (not64_bytewise state_var[i.val])) = not64_bytewise_value state[i.val] := by
    rw [←h_input', Not.eval_not]

  have h_not_value (i : Fin 25) : (not64_bytewise_value state[i.val]).value = not64 state[i.val].value :=
    (Not.not_bytewise_value_spec (state_norm i)).left

  have h_not_normalized (i : Fin 25) : (not64_bytewise_value state[i.val]).is_normalized :=
    (Not.not_bytewise_value_spec (state_norm i)).right

  simp only [assumptions, KeccakState.is_normalized, Fin.getElem_fin] at state_norm
  dsimp only [circuit_norm, main,
    not, xor, and, Xor.circuit, And.And64.circuit, Not.circuit] at h_env
  simp only [circuit_norm, subcircuit_norm, Xor.assumptions, Xor.spec,
    And.And64.assumptions, And.And64.spec] at h_env
  simp only [h_input', h_input_not, h_not_value, state_norm, h_not_normalized,
    and_self, imp_self, forall_const, true_and, and_imp, and_assoc, and_true] at h_env

  dsimp only [circuit_norm, main,
    not, xor, and, Xor.circuit, And.And64.circuit, Not.circuit]
  simp only [circuit_norm, subcircuit_norm, Xor.assumptions, Xor.spec,
    And.And64.assumptions, And.And64.spec]
  simp only [h_input', h_input_not, h_not_value, state_norm, h_not_normalized,
    and_self, imp_self, forall_const, true_and, and_imp, and_assoc, and_true]

  simp_all

def circuit : FormalCircuit (F p) KeccakState KeccakState where
  assumptions
  spec
  soundness
  completeness
end Gadgets.Keccak256.Chi
