import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.BLAKE3.BLAKE3G
import Clean.Specs.BLAKE3
import Clean.Circuit.Provable
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

namespace Gadgets.BLAKE3.Round
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3 (round roundConstants)

structure Inputs (F : Type) where
  state : BLAKE3State F
  message : Vector (U32 F) 16
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var BLAKE3State (F p)) := do
  let { state, message } := input
  -- TODO: refactor using a for loop
  let state ← G.circuit 0 4 8 12 ⟨state, message[0], message[1]⟩
  let state ← G.circuit 1 5 9 13 ⟨state, message[2], message[3]⟩
  let state ← G.circuit 2 6 10 14 ⟨state, message[4], message[5]⟩
  let state ← G.circuit 3 7 11 15 ⟨state, message[6], message[7]⟩
  let state ← G.circuit 0 5 10 15 ⟨state, message[8], message[9]⟩
  let state ← G.circuit 1 6 11 12 ⟨state, message[10], message[11]⟩
  let state ← G.circuit 2 7 8 13 ⟨state, message[12], message[13]⟩
  let state ← G.circuit 3 4 9 14 ⟨state, message[14], message[15]⟩
  return state

@[reducible] instance elaborated : ElaboratedCircuit (F p) Inputs BLAKE3State main := by
  elaborate_circuit_with {
    output input i0 := main input |>.output i0
  }

def Assumptions (input : Inputs (F p)) :=
  let { state, message } := input
  state.Normalized ∧ (∀ i : Fin 16, message[i].Normalized)

def Spec (input : Inputs (F p)) (out : BLAKE3State (F p)) :=
  let { state, message } := input
  out.value = round state.value (message.map U32.value) ∧ out.Normalized

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [G.circuit, G.elaborated]
  obtain ⟨h_state, h_message⟩ := h_assumptions
  simp only [G.Assumptions, G.Spec, and_imp] at h_holds
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h_holds
  simp_all only [forall_const]

  -- resolve chain of assumptions
  specialize c1 (h_message 0) (h_message 1)
  rw [c1.left] at c2
  specialize c2 c1.right (h_message 2) (h_message 3)
  rw [c2.left] at c3
  specialize c3 c2.right (h_message 4) (h_message 5)
  rw [c3.left] at c4
  specialize c4 c3.right (h_message 6) (h_message 7)
  rw [c4.left] at c5
  specialize c5 c4.right (h_message 8) (h_message 9)
  rw [c5.left] at c6
  specialize c6 c5.right (h_message 10) (h_message 11)
  rw [c6.left] at c7
  specialize c7 c6.right (h_message 12) (h_message 13)
  rw [c7.left] at c8
  specialize c8 c7.right (h_message 14) (h_message 15)

  clear c1 c2 c3 c4 c5 c6 c7

  -- now c8 is basically the goal
  simp [Specs.BLAKE3.round, roundConstants]
  exact c8

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [G.circuit, G.Assumptions, G.Spec, ProverEnvironment.UsesLocalWitnessesCompleteness,
    getElem_eval_vector, Fin.isValue, and_imp, and_true]
  obtain ⟨h_state, h_message⟩ := h_assumptions

  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h_env
  specialize c1 h_state (h_message 0) (h_message 1)
  specialize c2 c1.right (h_message 2) (h_message 3)
  specialize c3 c2.right (h_message 4) (h_message 5)
  specialize c4 c3.right (h_message 6) (h_message 7)
  specialize c5 c4.right (h_message 8) (h_message 9)
  specialize c6 c5.right (h_message 10) (h_message 11)
  specialize c7 c6.right (h_message 12) (h_message 13)
  specialize c8 c7.right (h_message 14) (h_message 15)
  simp only [c1.right, c2.right, c3.right, c4.right, c5.right, c6.right, c7.right, true_and]
  clear c1 c2 c3 c4 c5 c6 c7 c8

  simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    IsEmpty.forall_iff, and_true] at h_message
  simp only [h_state, h_message, and_self]

/-- Index schedule of the eight `G` applications: four columns, then four diagonals. -/
def gIndices : ℕ → Fin 16 × Fin 16 × Fin 16 × Fin 16
  | 0 => (0, 4, 8, 12)
  | 1 => (1, 5, 9, 13)
  | 2 => (2, 6, 10, 14)
  | 3 => (3, 7, 11, 15)
  | 4 => (0, 5, 10, 15)
  | 5 => (1, 6, 11, 12)
  | 6 => (2, 7, 8, 13)
  | _ => (3, 4, 9, 14)

/-- Variable-level state after `k` of the eight `G` steps (spelled with projections so
the head stays `G.output` at symbolic `k`, keeping congruence lemmas unifiable). -/
def stateVar (n : ℕ) (input_state : Var BLAKE3State (F p)) : ℕ → Var BLAKE3State (F p)
  | 0 => input_state
  | k + 1 =>
    G.output (gIndices k).1 (gIndices k).2.1 (gIndices k).2.2.1 (gIndices k).2.2.2
      (stateVar n input_state k) (n + 96 * k)

omit p_large_enough in
/-- Env-agreement transfers through the `G` chain: one `output_eval_congr` per step,
composed by `eval_congr_iterate`. -/
lemma state_eval_congr {env env' : ProverEnvironment (F p)} {n : ℕ}
    {input_state : Var BLAKE3State (F p)}
    (h0 : eval env.toEnvironment input_state = eval env'.toEnvironment input_state)
    {m : ℕ} (h_agrees : env.AgreesBelow (n + 96 * m) env') :
    ∀ k, k ≤ m → eval env.toEnvironment (stateVar n input_state k) =
      eval env'.toEnvironment (stateVar n input_state k) :=
  ProverEnvironment.eval_congr_iterate (stateVar n input_state) (fun k => n + 96 * k)
    (fun _ _ hab => by dsimp only; omega) h0
    (fun _ hk hag => G.output_eval_congr hk
      (ProverEnvironment.agreesBelow_of_le hag (by simp only [Nat.mul_succ, Nat.add_assoc]; omega)))
    h_agrees

def circuit : FormalCircuit (F p) Inputs BLAKE3State := {
  main, elaborated, Assumptions, Spec, soundness, completeness
  -- Manual: the eight legs thread the `G`-output chain; `state_eval_congr` provides
  -- every prefix of the chain in one step per leg.
  computableWitnesses := by
    computable_witnesses_start
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        (G.circuit (p := p) 0 4 8 12) ?hoff1 fun h_agrees => ?_
      case hoff1 => omega
      simp only [circuit_norm]
      exact ⟨h.1, G.state_elem_congr h.2 0, G.state_elem_congr h.2 1⟩
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        _ ?hoff2 fun h_agrees => ?_
      case hoff2 => rfl
      simp only [circuit_norm]
      exact ⟨state_eval_congr (m := 1) h.1
          (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 1 (by omega),
        G.state_elem_congr h.2 2, G.state_elem_congr h.2 3⟩
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        _ ?hoff3 fun h_agrees => ?_
      case hoff3 => rfl
      simp only [circuit_norm]
      exact ⟨state_eval_congr (m := 2) h.1
          (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 2 (by omega),
        G.state_elem_congr h.2 4, G.state_elem_congr h.2 5⟩
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        _ ?hoff4 fun h_agrees => ?_
      case hoff4 => rfl
      simp only [circuit_norm]
      exact ⟨state_eval_congr (m := 3) h.1
          (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 3 (by omega),
        G.state_elem_congr h.2 6, G.state_elem_congr h.2 7⟩
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        _ ?hoff5 fun h_agrees => ?_
      case hoff5 => rfl
      simp only [circuit_norm]
      exact ⟨state_eval_congr (m := 4) h.1
          (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 4 (by omega),
        G.state_elem_congr h.2 8, G.state_elem_congr h.2 9⟩
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        _ ?hoff6 fun h_agrees => ?_
      case hoff6 => rfl
      simp only [circuit_norm]
      exact ⟨state_eval_congr (m := 5) h.1
          (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 5 (by omega),
        G.state_elem_congr h.2 10, G.state_elem_congr h.2 11⟩
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        _ ?hoff7 fun h_agrees => ?_
      case hoff7 => rfl
      simp only [circuit_norm]
      exact ⟨state_eval_congr (m := 6) h.1
          (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 6 (by omega),
        G.state_elem_congr h.2 12, G.state_elem_congr h.2 13⟩
    · refine FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
        _ ?hoff8 fun h_agrees => ?_
      case hoff8 => rfl
      simp only [circuit_norm]
      exact ⟨state_eval_congr (m := 7) h.1
          (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 7 (by omega),
        G.state_elem_congr h.2 14, G.state_elem_congr h.2 15⟩
    · -- output = the eighth G output
      exact (CircuitType.eval_expression_prover_to_verifier
          (M := ProvableVector U32 16) env _).trans
        ((state_eval_congr (m := 8) h.1
            (ProverEnvironment.agreesBelow_of_le h_agrees (by omega)) 8 (by omega)).trans
          (CircuitType.eval_expression_prover_to_verifier
            (M := ProvableVector U32 16) env' _).symm)
}

end Gadgets.BLAKE3.Round
