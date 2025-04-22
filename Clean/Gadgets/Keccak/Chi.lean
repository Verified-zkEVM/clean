import Clean.Types.U64
import Clean.Circuit.Loops
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

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) :=
  Vector.finRange 25 |>.mapM fun i => do
    let state_not ← subcircuit Not.circuit (state.get (i + 5))
    let state_and ← subcircuit And.And64.circuit ⟨state_not, state.get (i + 10)⟩
    subcircuit Xor.circuit ⟨state.get i, state_and⟩

def assumptions := KeccakState.is_normalized (p:=p)

def spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) :=
  out_state.is_normalized
  ∧ out_state.value = Specs.Keccak256.chi state.value

instance lawful (state : Var KeccakState (F p)) : ConstantLawfulCircuit (main state) :=
  .from_mapM_vector _ (by infer_constant_lawful_circuits)

-- #eval! main (p:=p_babybear) default |>.operations.local_length
-- #eval! main (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState (Var KeccakState (F p)) where
  main
  local_length _ := 400
  local_length_eq state i0 := by
    rw [LawfulCircuit.local_length_eq]
    simp only [lawful_norm, Not.circuit, And.And64.circuit, Xor.circuit]

  initial_offset_eq state i := LawfulCircuit.initial_offset_eq (main state) i

  output _ i0 := Vector.mapRange 25 fun i => var_from_offset U64 (i0 + i*16 + 8)
  output_eq state i := by
    rw [LawfulCircuit.output_eq]
    simp only [lawful_norm, lawful, Xor.circuit, And.And64.circuit, Not.circuit]
    simp [Vector.finRange, List.finRange, Vector.range_succ, Array.range]

-- rewrite the chi spec as a loop
lemma chi_loop (state : Vector ℕ 25) :
    Specs.Keccak256.chi state = .mapFinRange fun i => state[i] ^^^ ((not64 state[i + 5]) &&& state[i + 10]) := by
  rw [Specs.Keccak256.chi, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds

  simp only [assumptions, KeccakState.is_normalized, Fin.getElem_fin] at state_norm

  -- simplify goal
  simp only [spec, lawful_norm]
  rw [chi_loop, eval_vector, KeccakState.is_normalized, Vector.ext_iff]
  simp only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_init,
    KeccakState.value, Vector.map_map, Function.comp_apply]

  suffices h : ∀ i : Fin 25, (eval env (var_from_offset U64 (i0 + i.val*16 + 8))).is_normalized ∧
    (eval env (var_from_offset U64 (i0 + i.val*16 + 8))).value =
      state.value[i] ^^^ ((not64 state.value[i + 5]) &&& state.value[i + 10]) by
    constructor
    · intro i; exact (h i).left
    · intro i' hi'
      specialize h ⟨ i', hi'⟩
      simp_all [KeccakState.value]

  -- simplify constraints using mapM theory
  simp only [elaborated, main] at h_holds
  rw [Circuit.constraints_hold.mapM_vector_soundness (lawful := by infer_constant_lawful_circuits)] at h_holds
  simp only [circuit_norm, lawful_norm, subcircuit_norm, Xor.circuit, And.And64.circuit, Not.circuit,
    Xor.assumptions, Xor.spec, And.And64.assumptions, And.And64.spec, Nat.reduceAdd] at h_holds

  -- TODO: this would be simpler if we had special theorems about Vector.finRange loops
  intro i
  specialize h_holds i
  have : i ∈ Vector.finRange 25 := by simp [Vector.finRange]
  specialize h_holds this i
  have : (i, ↑i) ∈ (Vector.finRange 25).zipIdx := by
    simp only [Vector.mem_zipIdx_iff_getElem?, Fin.is_lt, Vector.getElem?_eq_getElem, Option.some.injEq]
    simp [Vector.finRange]
  specialize h_holds this

  have h_input (i : Fin 25) : eval env state_var[i.val] = state[i.val] := by
    rw [←h_input, eval_vector, Vector.getElem_map]

  have h_input_not : (eval env (not64_bytewise state_var[(i + 5).val])) = not64_bytewise_value state[((i + 5)).val] := by
    rw [←h_input, Not.eval_not]

  have ⟨ state_not_value, state_not_norm ⟩ := Not.not_bytewise_value_spec (state_norm (i + 5))
  simp_all [KeccakState.value]

theorem completeness : Completeness (F p) KeccakState assumptions := by
  intro i env state_var h_env state h_input state_norm
  stop

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
