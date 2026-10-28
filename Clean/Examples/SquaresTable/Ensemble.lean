/-
A two-row table that sums the odd numbers: row `i` holds `i` and `i^2`, the first row is `(0, 0)`
and every transition adds `2 i + 1` to the square. The last row pushes its counter and square to the
verifier, which learns that the public square is the square of the public counter.

No single row checks that its square is a square: that is an invariant along the table, which each
row assumes of itself unless it is the first row, and establishes for the next row.
-/
module

public import Clean.Air.OrderedChannel
public import Clean.Air.WitnessGeneration
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace SquaresTable
open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- A row: a counter, its square, and whether the row is the last one. -/
structure Row (F : Type) where
  index : F
  square : F
  last : F
deriving ProvableStruct

/-- The channel on which the last row reports its counter and square. -/
def resultChannel : Channel (F p) fieldPair where
  name := "squares"
  Guarantees
  | (index, square), _ => square = index * index

/-- One window of the table. Constraints that read the next row are gated by `isTransition`. -/
def step : GeneralFormalCircuit (F p) (Window Row) unit where
  name := "squares"
  main window := do
    let current := window.current
    let next := window.next
    -- the first row is `(0, 0)`
    assertZero (window.isFirstRow * current.index)
    assertZero (window.isFirstRow * current.square)
    -- every transition increments the counter and adds `2 i + 1` to the square
    assertZero (window.isTransition * (next.index - current.index - 1))
    assertZero (window.isTransition * (next.square - current.square - 2 * current.index - 1))
    -- exactly the last row reports its counter and square
    assertZero (window.isLastRow * (current.last - 1))
    assertZero (window.isTransition * current.last)
    resultChannel.emit current.last (current.index, current.square)

  -- the invariant along the table, unless this is the first row
  Assumptions
  | { current, isFirstRow, .. }, _ =>
    isFirstRow = 1 ∨ current.square = current.index * current.index
  Spec
  | { current, next, isTransition, .. }, _, _ =>
    current.square = current.index * current.index ∧
      (isTransition = 1 → next.square = next.index * next.index)
  channelsWithRequirements := [resultChannel.toRaw]

  -- the honest prover follows the table's definition
  ProverAssumptions
  | { current, next, isFirstRow, isLastRow, isTransition }, _, _ =>
    (isFirstRow ≠ 0 → current.index = 0 ∧ current.square = 0) ∧
    (isTransition ≠ 0 → next.index = current.index + 1 ∧
      next.square = current.square + 2 * current.index + 1 ∧ current.last = 0) ∧
    (isLastRow ≠ 0 → current.last = 1)

  soundness := by
    circuit_proof_start [resultChannel]
    obtain ⟨h_first_index, h_first_square, h_next_index, h_next_square, -, -⟩ := h_holds
    have h_current : input_current_square = input_current_index * input_current_index := by
      rcases h_assumptions with h_first | h_square
      · simp_all
      · exact h_square
    refine ⟨⟨h_current, fun h_transition => ?_⟩, fun _ => h_current⟩
    simp only [h_transition, one_mul, sub_eq_zero] at h_next_index h_next_square
    linear_combination h_next_square + h_current -
      (input_next_index + input_current_index + 1) * h_next_index

  completeness := by
    circuit_proof_start
    obtain ⟨h_first, h_transition, h_last⟩ := h_assumptions
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mul_eq_zero, or_iff_not_imp_left] <;> intro h
    · exact (h_first h).left
    · exact (h_first h).right
    · rw [(h_transition h).left]; ring
    · rw [(h_transition h).right.left]; ring
    · rw [h_last h]; ring
    · exact (h_transition h).right.right

/-- The table, of `height` rows. Its rows answer the verifier's pull of the result: `last` counts it
on the row that carries the pulled counter and square. -/
def component (height : UInt64) : Component (F p) where
  circuit := step
  window := Window.layout Row
  circuit_assumptions_of_assumptions := by
    rintro i window data - - previous -
    rcases previous _ rfl with h_first | ⟨previous, output, h_next, h_transition, h_spec⟩
    · left
      simpa using h_first
    · right
      simp only [Window.layout_next, Window.layout_current, Window.layout_isTransition]
        at h_next h_transition
      have h_next : previous.next = window.current := by
        simpa only [ProvableType.fromElements_toElements] using congrArg fromElements h_next
      have h_square := h_spec.right h_transition
      rw [h_next] at h_square
      exact h_square
  generation := .preallocated {
    channel := resultChannel
    trigger := .pull
    height
    input i := pure (Window.cells {
      index := .witness (.ofU64 i)
      square := .witness (.ofU64 (i * i))
      last := .multiplicity
    })
  }

/-- The verifier pulls the public counter and square. -/
def verifier : Verifier.Program (F p) fieldPair where
  main
  | (index, square) => Verifier.pull resultChannel (index, square)
  Spec
  | (index, square), _ => square = index * index
  soundness := by simp_all [circuit_norm, resultChannel]

def ensemble (height : UInt64) : Ensemble (F p) fieldPair where
  tables := [component height]
  unique_names := by simp
  channels := [resultChannel.toRaw]
  unique_channel_names := by simp
  verifier := verifier
  tables_channels := by simp [circuit_norm, component, step]
  verifier_channels := by simp [circuit_norm, verifier]

/-- The table proves that the public square is the square of the public counter. -/
def formalEnsemble (height : UInt64) : FormalEnsemble (F p) fieldPair .logUp where
  ensemble := ensemble height
  Spec
  | (index, square) => square = index * index
  soundness := by
    apply Ensemble.soundness_of_tableSoundness_and_specConsistency
    · apply Ensemble.tableSoundness_of_soundChannels
      refine ⟨[resultChannel.toRaw], by simp [ensemble], ?_, ?_, ?_⟩
      · simp [circuit_norm, ensemble, component, step, verifier, resultChannel]
      · simp [circuit_norm, ensemble, component, step, verifier, resultChannel]
      · simp only [List.mem_singleton, forall_eq]
        infer_instance
    · simp [circuit_norm, ensemble, component]
    · intro witness spec
      exact spec.left

/-- Generate the witness of the table with `height` rows, for the public counter and square. -/
def generate (height : UInt64) (publicInput : fieldPair (F p)) :
    Except WitnessGeneration.GenerationError (EnsembleWitness (ensemble (p := p) height)) :=
  WitnessGeneration.generate (ensemble height) 1000 publicInput ()

theorem soundness (height : UInt64) (index square : F p) :
    (ensemble height).Statement .logUp (index, square) → square = index * index :=
  (formalEnsemble height).soundness (index, square) trivial

end SquaresTable
