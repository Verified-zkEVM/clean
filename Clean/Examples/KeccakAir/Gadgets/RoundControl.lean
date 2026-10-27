/-
The round control of a window of the Keccak-f AIR, the first part of Plonky3's `eval`: the step
flags start at round 0 and move by one round per transition, the first round's input is the
preimage, which stays the same along a permutation, and only the last round exports.
-/
module

public import Clean.Examples.KeccakAir.Lanes
public import Clean.Gadgets.ConditionalEquality

@[expose] public section

namespace KeccakAir.RoundControl
open Air.Flat Gadgets

variable {p : ℕ} [Fact p.Prime]

/-- The next row's step flags moved back by one round: entry `i` is the next row's flag `i + 1`. -/
def nextFlags {α : Type} (window : Window Row α) : Vector α 24 :=
  .ofFn fun i => window.next.stepFlags[i + 1]

lemma nextFlags_mapWindow {α β : Type} (f : α → β) (window : Window Row α) :
    nextFlags (mapWindow f window) = (nextFlags window).map f := by
  ext i hi
  simp [nextFlags, mapWindow, Row.map]

def main (window : Var (Window Row) (F p)) : Circuit (F p) Unit := do
  let current := window.current
  -- the first row computes round 0
  assertZero (window.isFirstRow * (current.stepFlags[0] - 1))
  Circuit.forEach (Vector.finRange 23) fun i =>
    assertZero (window.isFirstRow * current.stepFlags[i.succ])
  -- every transition moves to the next round
  ConditionalEquality.circuit (fields 24) ⟨window.isTransition, current.stepFlags, nextFlags window⟩
  -- round 0's input is the preimage, which stays the same along the permutation
  ConditionalEquality.circuit (fields 100) ⟨current.stepFlags[0], current.preimage, current.a⟩
  ConditionalEquality.circuit (fields 100)
    ⟨transitionInPermutation window, current.preimage, window.next.preimage⟩
  -- only the last round exports
  assertBool current.exportFlag
  assertZero (((1 : Expression (F p)) - current.stepFlags[23]) * current.exportFlag)

def Spec (window : Window Row (F p)) : Prop :=
  let current := window.current
  (window.isFirstRow ≠ 0 → current.stepFlags = oneHot 0) ∧
  (window.isTransition ≠ 0 → current.stepFlags = nextFlags window) ∧
  (current.stepFlags[0] ≠ 0 → current.preimage = current.a) ∧
  (transitionInPermutation window ≠ 0 → current.preimage = window.next.preimage) ∧
  IsBool current.exportFlag ∧ (current.stepFlags[23] ≠ 1 → current.exportFlag = 0)

def circuit : FormalAssertion (F p) (Window Row) where
  name := "roundControl"
  main
  Spec
  soundness := by
    intro offset env window_var window h_input _ h_holds
    rw [← h_input, eval_window]
    refine ⟨?_, by simp [main, circuit_norm, ConditionalEquality.circuit]⟩
    simp only [main, circuit_norm, ConditionalEquality.circuit] at h_holds
    simp only [Spec, provableStructEval_row, nextFlags_mapWindow, transitionInPermutation_eval,
      mapWindow_current, mapWindow_next, mapWindow_isFirstRow, mapWindow_isTransition,
      Row.map_stepFlags, Row.map_exportFlag, Row.map_preimage, Row.map_a,
      Vector.getElem_map] at h_holds ⊢
    obtain ⟨h_first, h_rest, h_transition, h_preimage, h_same, h_bool, h_export⟩ := h_holds
    refine ⟨fun h => ?_, h_transition, h_preimage, h_same, h_bool, fun h => ?_⟩
    · ext i hi
      simp only [Vector.getElem_map, oneHot, Vector.getElem_ofFn]
      cases i with
      | zero =>
        simpa [sub_eq_zero, h] using h_first
      | succ j =>
        have := h_rest ⟨j, by omega⟩
        simp only [mul_eq_zero, h, false_or] at this
        simpa [Fin.ext_iff] using this
    · rcases mul_eq_zero.mp h_export with h' | h'
      · exact absurd (sub_eq_zero.mp h').symm h
      · exact h'
  completeness := by
    intro offset env window_var _ window h_input _ h_spec
    rw [← h_input, CircuitType.eval_var_prover_to_verifier, eval_window] at h_spec
    simp only [main, circuit_norm, ConditionalEquality.circuit]
    simp only [Spec, provableStructEval_row, nextFlags_mapWindow, transitionInPermutation_eval,
      mapWindow_current, mapWindow_next, mapWindow_isFirstRow, mapWindow_isTransition,
      Row.map_stepFlags, Row.map_exportFlag, Row.map_preimage, Row.map_a,
      Vector.getElem_map] at h_spec ⊢
    obtain ⟨h_first, h_transition, h_preimage, h_same, h_bool, h_export⟩ := h_spec
    refine ⟨?_, fun i => ?_, h_transition, h_preimage, h_same, h_bool, ?_⟩
    · by_cases h : Expression.eval env.toEnvironment window_var.isFirstRow = 0
      · rw [h, zero_mul]
      · have := congrArg (·[0]) (h_first h)
        simp only [Vector.getElem_map, oneHot, Vector.getElem_ofFn] at this
        simp [this]
    · by_cases h : Expression.eval env.toEnvironment window_var.isFirstRow = 0
      · rw [h, zero_mul]
      · have h_zero : Expression.eval env.toEnvironment
            window_var.current.stepFlags[i.val + 1] = 0 := by
          have := congrArg (fun v : Vector (F p) 24 => v[i.val + 1]) (h_first h)
          simp only [Vector.getElem_map, oneHot, Vector.getElem_ofFn] at this
          rw [this]
          split_ifs with h_eq
          · exact absurd (congrArg Fin.val h_eq) (by simp)
          · rfl
        exact mul_eq_zero_of_right _ h_zero
    · by_cases h : Expression.eval env.toEnvironment window_var.current.stepFlags[23] = 1
      · rw [h, sub_self, zero_mul]
      · rw [h_export h, mul_zero]

lemma interactions_eq (window : Var (Window Row) (F p)) (offset : ℕ) :
    ((circuit.main window).operations offset).interactions = [] := by
  simp [circuit, main, circuit_norm, FormalAssertion.toSubcircuit_interactions, assertBool,
    ConditionalEquality.interactions_eq]

end KeccakAir.RoundControl
