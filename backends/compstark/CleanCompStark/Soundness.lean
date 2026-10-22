module

public import CleanCompStark.Transfer
public import CompStark.Soundness
public import CompStark.NonInteractive

/-!
# Knowledge soundness of a component's STARK

CompStark's knowledge soundness, composed with the transfer theorem: whatever a component's
circuit proves about its tables (`TableSound`) holds for the rows of a trace close to the one an
accepted prover committed to, except with the knowledge error. Interactively
(`knowledgeSoundness_of_tableSound`) and in the random-oracle model
(`knowledgeSoundness_ro_of_tableSound`).
-/

@[expose] public section

namespace CleanCompStark
open Air.Flat CompStark CompStark.Stark CompStark.Iop

variable {F : Type} [FiniteField F] {K : Type} [BaseField K] {EF : Type} [Challenge K EF]
  (e : F ≃+* K)

/-- A property of the rows of a component's tables that its circuit proves: every table of the
component with consistent prover data whose constraints hold has rows satisfying `P`. -/
def TableSound (component : Component F) (P : List (Array F) → Prop) : Prop :=
  ∀ table : Table F, table.component = component → table.DataConsistency → table.Constraints →
    P table.table

/-- **Knowledge soundness of a component's STARK.** If a STARK proves a bridgeable component's
AIR and the component's circuit proves `P` of its tables, the verifier accepts a prover with
probability at most the knowledge error unless the rows of some trace within `δ'` of the prover's
committed trace (`toRows`) satisfy `P`. -/
theorem knowledgeSoundness_of_tableSound (S : Iop.Setup EF) {component : Component F}
    (hair : S.air = toAir e component S.logN) (hc : bridgeable component = true)
    (fits : Fits (K := K) component S.logN) {P : List (Array F) → Prop}
    (hP : TableSound component P) (publicValues : List K) (prover : Prover S)
    (δ δ' : NNReal) (hδ' : (δ' : ℝ) < 1 - S.rate) :
    (∀ trace ∈ closeTraces S δ' prover.trace, ¬ P (toRows e component S.logN trace)) →
      acceptance publicValues prover ≤ knowledgeError S δ δ' := fun h ↦
  Iop.knowledgeSoundness S publicValues prover δ δ' hδ' fun trace ht hsat ↦ by
    rw [hair] at hsat
    obtain ⟨table, hcomponent, hrows, hdata, hconstraints⟩ :=
      table_of_satisfied e S.logN trace hc fits hsat
    exact h trace ht (hrows ▸ hP table hcomponent hdata hconstraints)

/-- **Knowledge soundness of a component's STARK in the random-oracle model.** If a STARK proves
a bridgeable component's AIR and the component's circuit proves `P` of its tables, a prover
making at most `Q` oracle calls gets a proof accepted while the rows of no trace within `δ'` of
the one it committed to satisfy `P` with probability at most `q · roundError + hashError q`,
`q = Q + verifierQueries`. -/
theorem knowledgeSoundness_ro_of_tableSound (S : Iop.Setup EF) {component : Component F}
    (hair : S.air = toAir e component S.logN) (hc : bridgeable component = true)
    (fits : Fits (K := K) component S.logN) {P : List (Array F) → Prop}
    (hP : TableSound component P) (publicValues : List K) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - S.rate) (Q : ℕ) (prover : NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits = S.logN ∧
        ∀ trace ∈ closeTraces S δ' (committedTrace S log proof),
          ¬ P (toRows e component S.logN trace)] ≤
      (Q + S.verifierQueries) * roundError S δ δ' + hashError K (Q + S.verifierQueries) :=
  (prEvent_mono _ _ _ fun ⟨_, _, _⟩ h ↦ ⟨h.1, h.2.1, fun trace ht hsat ↦ by
    rw [hair] at hsat
    obtain ⟨table, hcomponent, hrows, hdata, hconstraints⟩ :=
      table_of_satisfied e S.logN trace hc fits hsat
    exact h.2.2 trace ht (hrows ▸ hP table hcomponent hdata hconstraints)⟩).trans
    (Iop.knowledgeSoundness_ro S publicValues δ δ' hδ' Q prover hQ)

end CleanCompStark
