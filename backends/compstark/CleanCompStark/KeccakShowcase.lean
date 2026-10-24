module

public import CleanCompStark.KeccakAir.Setup
public import CompStark.Security
public import Mathlib.Tactic.IntervalCases

/-!
# Plonky3's keccak-air in Clean, proved by CompStark

Plonky3's Keccak-f AIR (`p3-keccak-air`: 2633 columns, 3182 constraints, 24 rows per permutation)
is a two-row Clean component, `KeccakAir.component`, proved sound against Clean's Keccak-f
specification `Specs.Keccak256.keccakPermutation` (`KeccakAir.table_block_soundness`). CompStark
proves it as a STARK over KoalaBear's quartic extension (`stark numQueries`) with the FRI
parameters of Plonky3's example `prove_prime_field_31` but for the number of queries (`params`):
blowup `2`, folding by arity up to `8` down to a constant, `16` bits of query grinding and `10`
bits of batching grinding, and Merkle caps of height `3`. The example's own configuration has
`87` queries.

**`keccak_soundness_ro`**, in the random-oracle model, with `203` queries: on `2 ^ 12` to
`2 ^ 21` rows, a prover making at most `Q` oracle calls gets a proof accepted while the rows of
every trace close to the one it committed to fail to compute Keccak-f on some 24-row block starting
at round 0, with probability at most `(Q + verifierQueries) · 2 ^ (-100) + hashError`. The
extracted trace's blocks are correct Keccak-f evaluations, with 100 bits of security per oracle
call.

It composes:

* CompStark's knowledge soundness in the random-oracle model (`Iop.knowledgeSoundness_ro`);
* the transfer theorem: a trace satisfying the AIR is a table of the component whose constraints
  hold (`table_of_satisfied`), since the component is bridgeable (`bridgeable_component`, proved
  from the shape of the constraints);
* Clean's soundness of the component: every 24-row block starting at round 0 of such a table
  computes Keccak-f (`KeccakAir.table_block_soundness`);
* the security calculator: every round error is at most `2 ^ (-100)` (`secureRo`), from the STARK's
  shape (`shape_setup`).

**`keccak_soundness`** is the interactive version: without grinding to credit, `247` queries give
100 bits of knowledge soundness on the same trace lengths. **`keccak_soundness_ro_example`** is the
same statement as `keccak_soundness_ro` for Plonky3's example configuration, `87` queries: the
calculator proves 52 bits per oracle call.

Each query count is the smallest for which the calculator's search finds an analysis reaching the
bits on every trace length of `Sized`.
-/

@[expose] public section

namespace CleanCompStark.KeccakShowcase
open CompStark CompStark.Stark CompStark.Iop CompStark.Sound CleanCompStark.KeccakAir

/-- The FRI parameters of Plonky3's example `prove_prime_field_31` with `numQueries` queries:
blowup `2`, folding by arity up to `8` down to a constant, `16` bits of query grinding, `10` bits
of batching grinding, Merkle caps of height `3`. The example has `87` queries. -/
def params (numQueries : ℕ+) : Fri.Params where
  logBlowup := 1
  logFinalPolyLen := 0
  maxLogArity := 3
  numQueries := numQueries
  commitPowBits := 0
  queryPowBits := 16
  batchPowBits := 10
  oodPowBits := 0
  capHeight := 3

/-- The trace lengths of the theorems: `2 ^ 12` to `2 ^ 21` rows. -/
def Sized (logN : ℕ) : Prop := 12 ≤ logN ∧ logN ≤ 21

theorem paramsFit (numQueries : ℕ+) {logN : ℕ} (h : Sized logN) :
    ParamsFit (params numQueries) logN := by
  obtain ⟨h1, h2⟩ := h
  simp only [ParamsFit, params]
  exact ⟨le_rfl, by omega, by omega, by omega, numQueries.pos, by omega⟩

/-- The STARK of the Keccak-f component on `2 ^ logN` rows over KoalaBear's quartic extension,
with `numQueries` queries. -/
abbrev stark (numQueries : ℕ+) (logN : ℕ) (h : Sized logN) : Iop.Setup KoalaBear.Fast.Ext4 :=
  setup (params numQueries) logN (paramsFit numQueries h)

/-- The extractor's radius `1/4 - 2 ^ (-k)`, below the unique-decoding radius `1/4` of rate
`1/2`. -/
noncomputable def radius (k : ℕ) : NNReal := 1 / 4 - 2 ^ (-k : ℤ)

theorem coe_radius (k : ℕ) (hk : 2 ≤ k) : (radius k : ℝ) = ((1 / 4 - 1 / 2 ^ k : ℚ) : ℝ) := by
  have hpow : (2 : ℝ) ^ k ≥ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hk
  have hle : (2 : NNReal) ^ (-k : ℤ) ≤ 1 / 4 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [zpow_neg, zpow_natCast]
    rw [ge_iff_le] at hpow
    calc ((2 : ℝ) ^ k)⁻¹ ≤ (2 ^ 2)⁻¹ := inv_anti₀ (by norm_num) hpow
      _ = 1 / 4 := by norm_num
  rw [radius, NNReal.coe_sub hle]
  push_cast
  rw [zpow_neg, zpow_natCast, one_div (2 ^ k : ℝ)]

/-- The analysis per oracle answer: FRI's proximity `δ = 1/4 - 2 ^ (-11)`, the extractor's radius
`δ' = 1/4 - 2 ^ (-13)`, a proximity loss of `2 ^ (-60)` per fold. -/
def roAnalysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 11, 1 / 4 - 1 / 2 ^ 13, 1 / 2 ^ 60⟩

/-- The interactive analysis: `δ = 1/4 - 2 ^ (-10)`, `δ' = 1/4 - 2 ^ (-12)`, a proximity loss of
`2 ^ (-16)` per fold. -/
def analysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 10, 1 / 4 - 1 / 2 ^ 12, 1 / 2 ^ 16⟩

/-- **100 bits per oracle answer.** The calculator certifies every round error of the Keccak-f
STARK with `203` queries on `2 ^ 12` to `2 ^ 21` rows to be at most `2 ^ (-100)`. -/
theorem secureRo (logN : ℕ) (h : Sized logN) :
    (stark 203 logN h).SecureRo KoalaBear.fieldSize roAnalysis 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _) ?_
  have h1 := h.1
  have h2 := h.2
  interval_cases logN <;> obtain rfl : h = ⟨by decide, by decide⟩ := rfl <;> decide +kernel

/-- **100 bits of knowledge soundness.** Without grinding to credit, the calculator certifies the
knowledge error of the Keccak-f STARK with `247` queries on `2 ^ 12` to `2 ^ 21` rows to be at
most `2 ^ (-100)`. -/
theorem secure (logN : ℕ) (h : Sized logN) :
    (stark 247 logN h).Secure KoalaBear.fieldSize analysis 100 := by
  refine secure_of_shape _ (shape_setup _ _ _) ?_
  have h1 := h.1
  have h2 := h.2
  interval_cases logN <;> obtain rfl : h = ⟨by decide, by decide⟩ := rfl <;> decide +kernel

/-- **52 bits per oracle answer at Plonky3's example configuration.** The calculator certifies
every round error of the Keccak-f STARK with `87` queries on `2 ^ 12` to `2 ^ 21` rows to be at
most `2 ^ (-52)`. -/
theorem example_secureRo (logN : ℕ) (h : Sized logN) :
    (stark 87 logN h).SecureRo KoalaBear.fieldSize roAnalysis 52 := by
  refine secureRo_of_shape _ (shape_setup _ _ _) ?_
  have h1 := h.1
  have h2 := h.2
  interval_cases logN <;> obtain rfl : h = ⟨by decide, by decide⟩ := rfl <;> decide +kernel

/-- Knowledge soundness in the random-oracle model of the Keccak-f STARK with `numQueries` queries
from the calculator's certificate of `bits` bits per oracle answer at `roAnalysis`. -/
theorem soundness_ro_of_secureRo {numQueries : ℕ+} {bits logN : ℕ} (h : Sized logN)
    (hsecure : (stark numQueries logN h).SecureRo KoalaBear.fieldSize roAnalysis bits) (Q : ℕ)
    (prover : NIProver (stark numQueries logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark numQueries logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark numQueries logN h) (radius 13)
            (committedTrace (stark numQueries logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark numQueries logN h).verifierQueries) * (2 ^ bits)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark numQueries logN h).verifierQueries) := by
  have hradius := coe_radius 13 (by norm_num)
  refine (KeccakAir.knowledgeSoundness_ro (stark numQueries logN h) rfl
    (Real.toNNReal roAnalysis.δ) (radius 13)
    (lt_one_sub_rate _ roAnalysis hsecure.1.1 _ hradius) Q prover hQ).trans ?_
  refine add_le_add (mul_le_mul_right ?_ _) le_rfl
  exact roundError_le_of_secureRo _ KoalaBear.card_eq roAnalysis hsecure _ _
    (coe_toNNReal_δ roAnalysis hsecure.1.1) hradius

/-- **Plonky3's keccak-air proved by CompStark, in the random-oracle model.** On `2 ^ logN` rows,
`2 ^ 12` to `2 ^ 21`, with `203` queries, a prover making at most `Q` oracle calls gets a proof
accepted while the rows read off every trace within `δ' = 1/4 - 2 ^ (-13)` of the one it committed
to fail to compute Keccak-f (`Specs.Keccak256.keccakPermutation`) on some 24-row block starting at
round 0, with probability at most `q · 2 ^ (-100) + hashError q`, `q = Q + verifierQueries`. -/
theorem keccak_soundness_ro (logN : ℕ) (h : Sized logN) (Q : ℕ)
    (prover : NIProver (stark 203 logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark 203 logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark 203 logN h) (radius 13)
            (committedTrace (stark 203 logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark 203 logN h).verifierQueries) * (2 ^ 100)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark 203 logN h).verifierQueries) :=
  soundness_ro_of_secureRo h (secureRo logN h) Q prover hQ

/-- **Plonky3's keccak-air proved by CompStark, interactively.** On `2 ^ logN` rows, `2 ^ 12` to
`2 ^ 21`, with `247` queries, unless the rows read off some trace within `δ' = 1/4 - 2 ^ (-12)` of
the prover's committed trace compute Keccak-f on every 24-row block starting at round 0, the
verifier accepts with probability at most `2 ^ (-100)`. -/
theorem keccak_soundness (logN : ℕ) (h : Sized logN) (prover : Prover (stark 247 logN h)) :
    (∀ trace ∈ closeTraces (stark 247 logN h) (radius 12) prover.trace,
      ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)) →
      acceptance [] prover ≤ (2 ^ 100)⁻¹ := fun hfar => by
  have hsecure := secure logN h
  have hradius := coe_radius 12 (by norm_num)
  exact (KeccakAir.knowledgeSoundness (stark 247 logN h) rfl prover (Real.toNNReal analysis.δ)
    (radius 12) (lt_one_sub_rate _ analysis hsecure.1.1 _ hradius) hfar).trans
    (knowledgeError_le_of_secure _ KoalaBear.card_eq analysis hsecure _ _
      (coe_toNNReal_δ analysis hsecure.1.1) hradius)

/-- **Plonky3's example configuration, in the random-oracle model.** With the `87` queries of
Plonky3's example `prove_prime_field_31`, on `2 ^ 12` to `2 ^ 21` rows, the statement of
`keccak_soundness_ro` holds with `2 ^ (-52)` per oracle call. -/
theorem keccak_soundness_ro_example (logN : ℕ) (h : Sized logN) (Q : ℕ)
    (prover : NIProver (stark 87 logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark 87 logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark 87 logN h) (radius 13)
            (committedTrace (stark 87 logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark 87 logN h).verifierQueries) * (2 ^ 52)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark 87 logN h).verifierQueries) :=
  soundness_ro_of_secureRo h (example_secureRo logN h) Q prover hQ

end CleanCompStark.KeccakShowcase
