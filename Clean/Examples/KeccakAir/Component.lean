/-
Plonky3's Keccak-f AIR as a two-row component. Its row circuit is Plonky3's `eval` in four steps,
each a subcircuit with its own spec: round control, θ, ρ ∘ π ∘ χ, and ι with the link to the next
row. Its soundness composes their specs into a round of Keccak-f (`windowSpec_of_specs`). Along a
table, each row's spec gives the next row the invariant it assumes: the step flags of a round `r`,
and the state after `r` rounds of the row's preimage.
-/
module

public import Clean.Examples.KeccakAir.Soundness
public import Clean.Examples.KeccakAir.Witness
public import Clean.Air.FlatEnsemble

@[expose] public section

namespace KeccakAir
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [large : Fact (2 ^ 16 < p)]

/-- One window of the Keccak-f AIR: Plonky3's `eval`, step by step. -/
def main (window : Var (Window Row) (F p)) : Circuit (F p) Unit := do
  RoundControl.circuit window
  Theta.circuit window.current
  RhoPiChi.circuit window.current
  Iota.circuit window

/-- The row circuit has no channel interactions. -/
lemma interactions_main (window : Var (Window Row) (F p)) (offset : ℕ) :
    Operations.interactions ((main window).operations offset) = [] := by
  simp [main, circuit_norm, FormalAssertion.toSubcircuit_interactions,
    RoundControl.interactions_eq, Theta.interactions_eq, RhoPiChi.interactions_eq,
    Iota.interactions_eq]

/-- What the steps need of the honest prover's window: its cells hold the round's steps, and its
step flags are those of a round. -/
def HonestWindow (window : Window Row (F p)) : Prop :=
  RoundControl.Spec window ∧ Theta.Spec window.current ∧ RhoPiChi.Spec window.current ∧
    Iota.Assumptions window ∧ Iota.Spec window

@[reducible]
instance elaborated : ElaboratedCircuit (F p) (Window Row) unit main := by
  elaborate_circuit

/-- One window of Plonky3's Keccak-f AIR. A row may assume that it carries the permutation's state
along unless it is the first row, and then computes a round of Keccak-f. -/
def circuit : GeneralFormalCircuit (F p) (Window Row) unit where
  name := "keccak"
  main
  elaborated
  Assumptions window _ := window.isFirstRow = 1 ∨ Carried window.current
  Spec window _ _ := WindowSpec window
  ProverAssumptions window _ _ := HonestWindow window
  soundness := by
    intro offset env window_var window h_input h_assumptions h_holds
    subst h_input
    refine ⟨?_, by simp [main, circuit_norm, RoundControl.circuit, Theta.circuit,
      RhoPiChi.circuit, Iota.circuit]⟩
    simp only [main, circuit_norm, RoundControl.circuit, Theta.circuit, RhoPiChi.circuit,
      Iota.circuit] at h_holds
    rw [provableStructEval_window, provableStructEval_row, ← mapWindow_current] at h_holds
    show WindowSpec (eval env window_var)
    rw [eval_window] at h_assumptions ⊢
    obtain ⟨h_control, h_theta, h_chi, h_iota⟩ := h_holds
    exact windowSpec_of_specs large.elim h_assumptions h_control h_theta h_chi h_iota
  completeness := by
    intro offset env window_var _ window h_input h_assumptions
    subst h_input
    refine ⟨?_, trivial⟩
    simp only [main, circuit_norm, RoundControl.circuit, Theta.circuit, RhoPiChi.circuit,
      Iota.circuit]
    rw [provableStructEval_window, provableStructEval_row, ← mapWindow_current]
    rw [CircuitType.eval_var_prover_to_verifier, eval_window] at h_assumptions
    obtain ⟨h_control, h_theta, h_chi, h_flags, h_iota⟩ := h_assumptions
    exact ⟨h_control, h_theta, ⟨⟨_, h_theta.2.2.2⟩, h_chi⟩, h_flags, h_iota⟩

/-- The Keccak-f AIR with `height` rows. The fixed columns are empty and only fix the height. The
rows are computed by `Witness.program`, 24 per permutation, whose inputs are the rows of the
prover's hint table `keccak`. -/
def component (height : UInt64) : Component (F p) where
  circuit := circuit
  fixedColumns := some { Row := unit, row _ := pure (), height }
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
      rw [← h_next]
      exact carried_of_windowSpec h_spec h_transition
  generation := .segments Witness.program

end KeccakAir
