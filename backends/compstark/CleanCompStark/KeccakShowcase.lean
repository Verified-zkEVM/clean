module

public import CleanCompStark.KeccakAir.Setup
public import CompStark.Security
public import Mathlib.Tactic.IntervalCases

/-!
# Plonky3's keccak-air in Clean, proved by CompStark

Plonky3's Keccak-f AIR (`p3-keccak-air`: 2633 columns, 3182 constraints, 24 rows per permutation)
is a two-row Clean component, `KeccakAir.component`, proved sound against Clean's Keccak-f
specification `Specs.Keccak256.keccakPermutation` (`KeccakAir.table_block_soundness`). CompStark
proves it as a STARK over KoalaBear's quartic extension (`stark`), with FRI's parameters chosen for
proven security: blowup `2`, folding by arity `2` down to a constant, `204` queries with `16` bits
of query grinding and `10` bits of batching grinding, and Merkle caps of height `3`, as Plonky3's
example `prove_prime_field_31` commits.

**`keccak_soundness_ro`**, in the random-oracle model: on `2 ^ 11` to `2 ^ 21` rows, a prover
making at most `Q` oracle calls gets a proof accepted while the rows of every trace close to the one
it committed to fail to compute Keccak-f on some 24-row block starting at round 0, with probability
at most `(Q + verifierQueries) · 2 ^ (-100) + hashError`. The extracted trace's blocks are correct
Keccak-f evaluations, with 100 bits of security per oracle call.

It composes:

* CompStark's knowledge soundness in the random-oracle model (`Iop.knowledgeSoundness_ro`);
* the transfer theorem: a trace satisfying the AIR is a table of the component whose constraints
  hold (`table_of_satisfied`), since the component is bridgeable (`bridgeable_component`, proved
  from the shape of the constraints);
* Clean's soundness of the component: every 24-row block starting at round 0 of such a table
  computes Keccak-f (`KeccakAir.table_block_soundness`);
* the security calculator: every round error is at most `2 ^ (-100)` (`secureRo`), from the AIR's
  numbers (`numConstraints_setup`, `identityDegree_setup`, `numOpened_setup`).

**`keccak_soundness`** is the interactive version: without grinding to credit, the same
configuration has 84 bits of knowledge soundness.
-/

@[expose] public section

namespace CleanCompStark.KeccakShowcase
open CompStark CompStark.Stark CompStark.Iop CompStark.Sound CleanCompStark.KeccakAir

/-- FRI's parameters for 100 proven bits: blowup `2`, folding by arity `2` down to a constant,
`204` queries with `16` bits of query grinding, `10` bits of batching grinding, Merkle caps of
height `3`. -/
def params : Fri.Params where
  logBlowup := 1
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 204
  commitPowBits := 0
  queryPowBits := 16
  batchPowBits := 10
  oodPowBits := 0
  capHeight := 3

/-- The trace lengths of the theorem: `2 ^ 11` to `2 ^ 21` rows. -/
def Sized (logN : ℕ) : Prop := 11 ≤ logN ∧ logN ≤ 21

theorem paramsFit {logN : ℕ} (h : Sized logN) : ParamsFit params logN := by
  obtain ⟨h1, h2⟩ := h
  simp only [ParamsFit, params]
  omega

/-- The STARK of the Keccak-f component on `2 ^ logN` rows over KoalaBear's quartic extension. -/
abbrev stark (logN : ℕ) (h : Sized logN) : Iop.Setup KoalaBear.Fast.Ext4 :=
  setup params logN (paramsFit h)

/-- The calculator's analysis: FRI's proximity `δ = 1/4 - 2 ^ (-10)`, the extractor's radius
`δ' = 1/4 - 2 ^ (-11)`, below the unique-decoding radius `1/4` of rate `1/2`, a proximity loss of
`2 ^ (-20)` per fold, and the lossy bound for folds onto at least `2 ^ 10` points. -/
def analysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 10, 1 / 4 - 1 / 2 ^ 11, 1 / 2 ^ 20, 10⟩

/-- The extractor's radius `δ' = 1/4 - 2 ^ (-11)`. -/
noncomputable def extractorRadius : NNReal := 1 / 4 - 2 ^ (-11 : ℤ)

theorem coe_extractorRadius : (extractorRadius : ℝ) = analysis.δ' := by
  have hle : (2 : NNReal) ^ (-11 : ℤ) ≤ 1 / 4 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  rw [extractorRadius, NNReal.coe_sub hle]
  simp only [analysis]
  push_cast
  norm_num

/-- **100 bits per oracle answer.** The calculator certifies every round error of the Keccak-f
STARK on `2 ^ 11` to `2 ^ 21` rows to be at most `2 ^ (-100)`. -/
theorem secureRo (logN : ℕ) (h : Sized logN) :
    (stark logN h).SecureRo KoalaBear.fieldSize analysis 100 := by
  obtain ⟨h1, h2⟩ := h
  interval_cases logN <;>
  · refine (fun (hp : ParamsFit params _)
        (hsecure : (setup params _ hp).SecureRo KoalaBear.fieldSize analysis 100) => hsecure)
      (by decide) ?_
    unfold Setup.SecureRo Setup.Fits Setup.roundErrorBound Setup.roundErrorTerms
    rw [numOpened_setup]
    simp only [numConstraints_setup, identityDegree_setup]
    decide +kernel

/-- **84 bits of knowledge soundness.** Without grinding to credit, the calculator certifies the
knowledge error of the Keccak-f STARK on `2 ^ 11` to `2 ^ 21` rows to be at most `2 ^ (-84)`. -/
theorem secure (logN : ℕ) (h : Sized logN) :
    (stark logN h).Secure KoalaBear.fieldSize analysis 84 := by
  obtain ⟨h1, h2⟩ := h
  interval_cases logN <;>
  · refine (fun (hp : ParamsFit params _)
        (hsecure : (setup params _ hp).Secure KoalaBear.fieldSize analysis 84) => hsecure)
      (by decide) ?_
    unfold Setup.Secure Setup.Fits Setup.knowledgeErrorBound Setup.knowledgeErrorTerms
    rw [numOpened_setup]
    simp only [numConstraints_setup, identityDegree_setup]
    decide +kernel

/-- **Plonky3's keccak-air proved by CompStark, in the random-oracle model.** On `2 ^ logN` rows,
`2 ^ 11` to `2 ^ 21`, a prover making at most `Q` oracle calls gets a proof accepted while the rows
read off every trace within `δ' = 1/4 - 2 ^ (-11)` of the one it committed to fail to compute
Keccak-f (`Specs.Keccak256.keccakPermutation`) on some 24-row block starting at round 0, with
probability at most `q · 2 ^ (-100) + hashError q`, `q = Q + verifierQueries`. -/
theorem keccak_soundness_ro (logN : ℕ) (h : Sized logN) (Q : ℕ)
    (prover : NIProver (stark logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark logN h) extractorRadius
            (committedTrace (stark logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark logN h).verifierQueries) * (2 ^ 100)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark logN h).verifierQueries) := by
  have hsecure := secureRo logN h
  refine (KeccakAir.knowledgeSoundness_ro (stark logN h) rfl (Real.toNNReal analysis.δ)
    extractorRadius (lt_one_sub_rate _ analysis hsecure.1.2.1 _ coe_extractorRadius) Q prover
    hQ).trans ?_
  refine add_le_add (mul_le_mul_right ?_ _) le_rfl
  exact roundError_le_of_secureRo _ KoalaBear.card_eq analysis hsecure _ _
    (coe_toNNReal_δ analysis hsecure.1.2.1) coe_extractorRadius

/-- **Plonky3's keccak-air proved by CompStark, interactively.** On `2 ^ logN` rows, `2 ^ 11` to
`2 ^ 21`, unless the rows read off some trace within `δ' = 1/4 - 2 ^ (-11)` of the prover's
committed trace compute Keccak-f on every 24-row block starting at round 0, the verifier accepts
with probability at most `2 ^ (-84)`. -/
theorem keccak_soundness (logN : ℕ) (h : Sized logN) (prover : Prover (stark logN h)) :
    (∀ trace ∈ closeTraces (stark logN h) extractorRadius prover.trace,
      ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)) →
      acceptance [] prover ≤ (2 ^ 84)⁻¹ := fun hfar => by
  have hsecure := secure logN h
  exact (KeccakAir.knowledgeSoundness (stark logN h) rfl prover (Real.toNNReal analysis.δ)
    extractorRadius (lt_one_sub_rate _ analysis hsecure.1.2.1 _ coe_extractorRadius) hfar).trans
    (knowledgeError_le_of_secure _ KoalaBear.card_eq analysis hsecure _ _
      (coe_toNNReal_δ analysis hsecure.1.2.1) coe_extractorRadius)

end CleanCompStark.KeccakShowcase
