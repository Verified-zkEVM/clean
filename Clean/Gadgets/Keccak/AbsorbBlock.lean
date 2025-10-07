import Clean.Gadgets.Keccak.Permutation
import Clean.Circuit.Explicit
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.AbsorbBlock
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^16 + 2^8)]
open Specs.Keccak256

structure Input (F : Type) where
  state : KeccakState F
  block : KeccakBlock F

instance : ProvableStruct Input where
  components := [KeccakState, KeccakBlock]
  toComponents := fun { state, block } => .cons state (.cons block .nil)
  fromComponents := fun (.cons state (.cons block .nil)) => { state, block }

def main (input : Var Input (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let { state, block } := input
  -- absorb the block into the state by XORing with the first RATE elements
  let state_rate ← Circuit.mapFinRange RATE fun i => Xor64.circuit ⟨state[i.val], block[i.val]⟩

  -- the remaining elements of the state are unchanged
  let state_capacity := Vector.mapFinRange (25 - RATE) fun i => state[RATE + i.val]
  let state' : Vector _ 25 := state_rate ++ state_capacity

  -- apply the permutation
  Permutation.circuit state'

instance elaborated : ElaboratedCircuit (F p) Input KeccakState where
  main
  localLength _ := 31048
  output _ i0 := Permutation.stateVar (i0 + 136) 23

  localLength_eq _ _ := by simp only [main, circuit_norm, Xor64.circuit, Permutation.circuit, RATE]
  yields_eq := by intros; simp [circuit_norm, main, Xor64.circuit, Permutation.circuit, Permutation.elaborated]
  output_eq input i0 := by simp only [main, circuit_norm, Xor64.circuit, Permutation.circuit, RATE]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm, Xor64.circuit, Permutation.circuit, RATE]

@[reducible] def Assumptions (input : Input (F p)) :=
  input.state.Normalized ∧ input.block.Normalized

@[reducible] def Spec (input : Input (F p)) (out_state : KeccakState (F p)) :=
  out_state.Normalized ∧
  out_state.value = absorbBlock input.state.value input.block.value

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env yielded ⟨ state_var, block_var ⟩ ⟨ state, block ⟩ h_input h_assumptions h_holds

  -- simplify goal and constraints
  simp only [circuit_norm, RATE, main, Spec, Assumptions, absorbBlock,
    Xor64.circuit, Xor64.Assumptions, Xor64.Spec,
    Permutation.circuit, Permutation.Assumptions, Permutation.Spec,
    Input.mk.injEq] at *

  -- reduce goal to characterizing absorb step
  set state_after_absorb : Var KeccakState (F p) :=
    (Vector.mapFinRange 17 fun i => varFromOffset (F:=F p) U64 (i0 + i.val * 8)) ++
    (Vector.mapFinRange 8 fun i => state_var[17 + i.val])

  suffices goal : (eval env state_after_absorb).Normalized
    ∧ (eval env state_after_absorb).value =
      .mapFinRange 25 fun i => state.value[i.val] ^^^ if h : i.val < 17 then block.value[i.val] else 0 by
    simp_all
  replace h_holds := h_holds.left

  -- finish the proof by cases on i < 17
  apply KeccakState.normalized_value_ext
  intro ⟨ i, hi ⟩
  simp only [state_after_absorb, eval_vector, Vector.getElem_map, Vector.getElem_mapFinRange,
    KeccakState.value, KeccakBlock.value]

  by_cases hi' : i < 17 <;> simp only [hi', reduceDIte]
  · simp only [Vector.getElem_mapFinRange, Vector.getElem_append_left hi']
    specialize h_holds ⟨ i, hi'⟩
    simp only [getElem_eval_vector, h_input, h_assumptions.right ⟨ i, hi'⟩, h_assumptions.left ⟨ i, hi ⟩, and_true, true_implies] at h_holds
    exact ⟨ h_holds.right, h_holds.left ⟩
  · simp only [Vector.getElem_mapFinRange, Vector.getElem_append_right (show i < 17 + 8 from hi) (by linarith)]
    have : 17 + (i - 17) = i := by omega
    simp only [this, getElem_eval_vector, h_input, h_assumptions.left ⟨i, hi⟩, Nat.xor_zero, and_self]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i0 env yielded ⟨ state_var, block_var ⟩ h_env ⟨ state, block ⟩ h_input h_assumptions

  -- simplify goal and witnesses
  simp only [circuit_norm, RATE, main, Assumptions, Xor64.circuit, Xor64.Assumptions, Xor64.Spec,
    Permutation.circuit, Permutation.Assumptions, Permutation.Spec, Input.mk.injEq] at *
  simp only [getElem_eval_vector, h_input] at h_env ⊢

  have assumptions' (i : Fin 17) : state[i.val].Normalized ∧ block[i.val].Normalized := by
    simp [h_assumptions.left ⟨i, by linarith [i.is_lt]⟩, h_assumptions.right i]
  simp only [assumptions', and_true, true_implies, implies_true, true_and] at h_env ⊢

  -- reduce goal to characterizing absorb step
  set state_after_absorb : Var KeccakState (F p) :=
    (Vector.mapFinRange 17 fun i => varFromOffset (F:=F p) U64 (i0 + i.val * 8)) ++
    (Vector.mapFinRange 8 fun i => state_var[17 + i.val])

  suffices goal : (eval env state_after_absorb).Normalized
    ∧ (eval env state_after_absorb).value =
      .mapFinRange 25 fun i => state.value[i.val] ^^^ if h : i.val < 17 then block.value[i.val] else 0 by
    simp_all
  replace h_env := h_env.left

  -- finish the proof by cases on i < 17
  apply KeccakState.normalized_value_ext
  intro ⟨ i, hi ⟩
  simp only [eval_vector, Vector.getElem_map, KeccakState.value, KeccakBlock.value,
    Vector.getElem_mapFinRange, state_after_absorb]
  by_cases hi' : i < 17 <;> simp only [hi', reduceDIte]
  · simp only [Vector.getElem_mapFinRange, Vector.getElem_append_left hi']
    exact ⟨ (h_env ⟨ i, hi'⟩).right, (h_env ⟨ i, hi'⟩).left ⟩
  · simp only [Vector.getElem_mapFinRange, Vector.getElem_append_right (show i < 17 + 8 from hi) (by linarith)]
    have : 17 + (i - 17) = i := by omega
    simp only [this, getElem_eval_vector, h_input, h_assumptions.left ⟨i, hi⟩, Nat.xor_zero, and_self]

def circuit : FormalCircuit (F p) Input KeccakState :=
  { elaborated with Assumptions, Spec, soundness, completeness }
end Gadgets.Keccak256.AbsorbBlock
