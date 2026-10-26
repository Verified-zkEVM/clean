module

public import CleanCompStark.Transfer
public import CompStark.Soundness
public import CompStark.NonInteractive
public import CompStark.Security

/-!
# Knowledge soundness of a component's STARK

CompStark's knowledge soundness, composed with the transfer theorem: whatever a component's
circuit proves about its tables (`TableSound`) holds for the rows of a trace close to the one an
accepted prover committed to, except with the knowledge error. This holds for any bridgeable
component and any STARK proving its AIR, whatever its FRI parameters and grinding.

With CompStark's security calculator, the error is `2 ^ (-bits)` for the bits the calculator
certifies in the kernel for the STARK's configuration, at an analysis `A` and with an MCA bound
that holds: interactively (`knowledgeSoundness_of_secure`, from `S.Secure p B A bits`) and per
oracle call in the random-oracle model (`knowledgeSoundness_ro_of_secureRo`, from
`S.SecureRo p B A bits`). In terms of the knowledge and round errors at any radii, they are
`knowledgeSoundness_of_tableSound` and `knowledgeSoundness_ro_of_tableSound`.
-/

@[expose] public section

namespace CleanCompStark
open Air.Flat CompStark CompStark.Stark CompStark.Iop CompStark.Sound

variable {F : Type} [FiniteField F] {K : Type} [BaseField K] {EF : Type} [Challenge K EF]
  (e : F ≃+* K)

/-- A property of the rows of a component's tables that its circuit proves: every table of the
component with consistent prover data whose constraints hold has rows satisfying `P`. -/
def TableSound (component : Component F) (P : List (Array F) → Prop) : Prop :=
  ∀ table : Table F, table.component = component → table.DataConsistency → table.Constraints →
    P table.table

/-- A trace whose rows fail a property that a bridgeable component's circuit proves of its tables
does not satisfy the component's AIR. -/
theorem not_satisfied_of_tableSound (S : Iop.Setup EF) {component : Component F}
    (hair : S.air = toAir e component S.logN) (hc : bridgeable component = true)
    (fits : Fits (K := K) component S.logN) {P : List (Array F) → Prop}
    (hP : TableSound component P) {publicValues : List K} {trace : Array K}
    (h : ¬ P (toRows e component S.logN trace)) : ¬ S.air.Satisfied S.logN trace publicValues :=
  fun hsat ↦ by
    rw [hair] at hsat
    obtain ⟨table, hcomponent, hrows, hdata, hconstraints⟩ :=
      table_of_satisfied e S.logN trace hc fits hsat
    exact h (hrows ▸ hP table hcomponent hdata hconstraints)

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
  Iop.knowledgeSoundness S publicValues prover δ δ' hδ' fun trace ht ↦
    not_satisfied_of_tableSound e S hair hc fits hP (h trace ht)

/-- **Knowledge soundness of a component's STARK in the random-oracle model.** If a STARK proves
a bridgeable component's AIR and the component's circuit proves `P` of its tables, a prover
making at most `Q` oracle calls gets a proof accepted while the rows of no trace within `δ'` of
the one it committed to satisfy `P` with probability at most `q · roundError + hashError h q`,
`q = Q + verifierQueries`, `h` the Merkle cap height. -/
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
      (Q + S.verifierQueries) * roundError S δ δ' +
        hashError K S.params.capHeight (Q + S.verifierQueries) :=
  (prEvent_mono _ _ _ fun ⟨_, _, _⟩ h ↦ ⟨h.1, h.2.1, fun trace ht ↦
    not_satisfied_of_tableSound e S hair hc fits hP (h.2.2 trace ht)⟩).trans
    (Iop.knowledgeSoundness_ro S publicValues δ δ' hδ' Q prover hQ)

/-- **Knowledge soundness of a component's STARK from the calculator.** If a STARK proves a
bridgeable component's AIR, the component's circuit proves `P` of its tables, and the calculator
certifies `bits` bits for the STARK at the analysis `A` with an MCA bound `B` that holds, for a base
field of `p` elements, the verifier accepts a prover with probability at most `2 ^ (-bits)` unless
the rows of some trace within `δ' = A.δ'` of the prover's committed trace satisfy `P`. -/
theorem knowledgeSoundness_of_secure (S : Iop.Setup EF) {component : Component F}
    (hair : S.air = toAir e component S.logN) (hc : bridgeable component = true)
    (fits : Fits (K := K) component S.logN) {P : List (Array F) → Prop}
    (hP : TableSound component P) {p : ℕ} (hp : Nat.card K = p) {B : McaBound} (hB : B.Holds)
    (A : Analysis) {bits : ℕ} (hsecure : S.Secure p B A bits) (δ' : NNReal)
    (hδ' : (δ' : ℝ) = A.δ') (publicValues : List K) (prover : Prover S) :
    (∀ trace ∈ closeTraces S δ' prover.trace, ¬ P (toRows e component S.logN trace)) →
      acceptance publicValues prover ≤ (2 ^ bits)⁻¹ := fun h ↦
  Iop.knowledgeSoundness_of_secure S hp hB A hsecure δ' hδ' publicValues prover fun trace ht ↦
    not_satisfied_of_tableSound e S hair hc fits hP (h trace ht)

/-- **Knowledge soundness of a component's STARK in the random-oracle model from the
calculator.** If a STARK proves a bridgeable component's AIR, the component's circuit proves `P`
of its tables, and the calculator certifies `bits` bits per oracle answer for the STARK at the
analysis `A` with an MCA bound `B` that holds, for a base field of `p` elements, a prover making at
most `Q` oracle calls gets a proof accepted while the rows of no trace within `δ' = A.δ'` of the
one it committed to satisfy `P` with probability at most `q · 2 ^ (-bits) + hashError h q`,
`q = Q + verifierQueries`, `h` the Merkle cap height. -/
theorem knowledgeSoundness_ro_of_secureRo (S : Iop.Setup EF) {component : Component F}
    (hair : S.air = toAir e component S.logN) (hc : bridgeable component = true)
    (fits : Fits (K := K) component S.logN) {P : List (Array F) → Prop}
    (hP : TableSound component P) {p : ℕ} (hp : Nat.card K = p) {B : McaBound} (hB : B.Holds)
    (A : Analysis) {bits : ℕ} (hsecure : S.SecureRo p B A bits) (δ' : NNReal)
    (hδ' : (δ' : ℝ) = A.δ') (publicValues : List K) (Q : ℕ) (prover : NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits = S.logN ∧
        ∀ trace ∈ closeTraces S δ' (committedTrace S log proof),
          ¬ P (toRows e component S.logN trace)] ≤
      (Q + S.verifierQueries) * (2 ^ bits)⁻¹ +
        hashError K S.params.capHeight (Q + S.verifierQueries) :=
  (prEvent_mono _ _ _ fun ⟨_, _, _⟩ h ↦ ⟨h.1, h.2.1, fun trace ht ↦
    not_satisfied_of_tableSound e S hair hc fits hP (h.2.2 trace ht)⟩).trans
    (Iop.knowledgeSoundness_ro_of_secureRo S hp hB A hsecure δ' hδ' publicValues Q prover hQ)

end CleanCompStark
