module

public import CleanCompStark.KeccakAir.Setup
public import CompStark.Security
public import Mathlib.Tactic.IntervalCases

/-!
# Plonky3's keccak-air in Clean, proved by CompStark

Plonky3's Keccak-f AIR (`p3-keccak-air`: 2633 columns, 3182 constraints, 24 rows per permutation)
is a two-row Clean component, `KeccakAir.component`, proved sound against Clean's Keccak-f
specification `Specs.Keccak256.keccakPermutation` (`KeccakAir.table_block_soundness`). CompStark
proves it as a STARK over KoalaBear's quartic extension (`stark numQueries g`) with the FRI
parameters of Plonky3's example `prove_prime_field_31` but for the number of queries and the
grinding `g` (`params`): blowup `2`, folding by arity up to `8` down to a constant, `16` bits of
query grinding, and Merkle caps of height `3`. The example's own configuration has `87` queries
and `10` bits of batching grinding (`Grinding.plonky3`).

**`keccak_soundness_ro`**, in the random-oracle model, with `188` queries and `2`, `24` and `12`
bits of grinding before `ζ`, the batching challenge and each fold (`Grinding.johnson`): on
`2 ^ 12` to `2 ^ 21` rows, a prover making at most `Q` oracle calls gets a proof accepted while the
rows of every trace close to the one it committed to fail to compute Keccak-f on some 24-row block
starting at round 0, with probability at most `(Q + verifierQueries) · 2 ^ (-100) + hashError`.
The extracted trace's blocks are correct Keccak-f evaluations, with 100 bits of security per
oracle call.

It composes:

* CompStark's knowledge soundness in the random-oracle model (`Iop.knowledgeSoundness_ro`);
* the transfer theorem: a trace satisfying the AIR is a table of the component whose constraints
  hold (`table_of_satisfied`), since the component is bridgeable (`bridgeable_component`, proved
  from the shape of the constraints);
* Clean's soundness of the component: every 24-row block starting at round 0 of such a table
  computes Keccak-f (`KeccakAir.table_block_soundness`);
* the security calculator: every round error is at most `2 ^ (-100)` (`secureRo`), from the STARK's
  shape (`shape_setup`), with the MCA bound up to the Johnson radius
  (`McaBound.uniqueOrJohnson_holds`), so that FRI's proximity goes beyond the unique-decoding
  radius.

**`keccak_soundness`** is the interactive version: without grinding to credit, `247` queries give
100 bits of knowledge soundness on the same trace lengths. **`keccak_soundness_ro_example`** is the
same statement as `keccak_soundness_ro` for Plonky3's example configuration, `87` queries: the
calculator proves 59 bits per oracle call.

Each query count is the smallest for which the calculator's search finds an analysis reaching the
bits on every trace length of `Sized`.
-/

@[expose] public section

namespace CleanCompStark.KeccakShowcase
open CompStark CompStark.Stark CompStark.Iop CompStark.Sound CleanCompStark.KeccakAir

/-- The bits of grinding before `ζ`, the batching challenge and each FRI fold. -/
structure Grinding where
  ood : ℕ
  batch : ℕ
  commit : ℕ

/-- Plonky3's example's grinding: `10` bits before the batching challenge. -/
def Grinding.plonky3 : Grinding := ⟨0, 10, 0⟩

/-- The grinding of `keccak_soundness_ro`: `2`, `24` and `12` bits before `ζ`, the batching
challenge and each fold. Beyond the unique-decoding radius the Johnson list size multiplies the
out-of-domain, batching and fold terms, which these bits bring to `2 ^ (-100)`. -/
def Grinding.johnson : Grinding := ⟨2, 24, 12⟩

/-- The FRI parameters of Plonky3's example `prove_prime_field_31` with `numQueries` queries and
the grinding `g` before `ζ`, the batching challenge and each fold: blowup `2`, folding by arity
up to `8` down to a constant, `16` bits of query grinding, Merkle caps of height `3`. The example
is `params 87 .plonky3`. -/
def params (numQueries : ℕ+) (g : Grinding) : Fri.Params where
  logBlowup := 1
  logFinalPolyLen := 0
  maxLogArity := 3
  numQueries := numQueries
  commitPowBits := g.commit
  queryPowBits := 16
  batchPowBits := g.batch
  oodPowBits := g.ood
  capHeight := 3

/-- The trace lengths of the theorems: `2 ^ 12` to `2 ^ 21` rows. -/
def Sized (logN : ℕ) : Prop := 12 ≤ logN ∧ logN ≤ 21

theorem paramsFit (numQueries : ℕ+) (g : Grinding) {logN : ℕ} (h : Sized logN) :
    ParamsFit (params numQueries g) logN := by
  obtain ⟨h1, h2⟩ := h
  simp only [ParamsFit, params]
  exact ⟨le_rfl, by omega, by omega, by omega, numQueries.pos, by omega⟩

/-- The STARK of the Keccak-f component on `2 ^ logN` rows over KoalaBear's quartic extension,
with `numQueries` queries and the grinding `g`. -/
abbrev stark (numQueries : ℕ+) (g : Grinding) (logN : ℕ) (h : Sized logN) :
    Iop.Setup KoalaBear.Fast.Ext4 :=
  setup (params numQueries g) logN (paramsFit numQueries g h)

/-- The analysis of `keccak_soundness_ro`, per oracle answer: FRI's proximity
`δ = 1118851 / 2 ^ 22 ≈ 0.2668` and the extractor's radius `δ' = 4585033 / 2 ^ 24 ≈ 0.2733`, beyond
the unique-decoding radius `1/4` of rate `1/2` and below the Johnson radius `1 - √(1/2) ≈ 0.2929`,
a proximity loss of `2 ^ (-16)` per fold. -/
def roAnalysis : Analysis := ⟨1118851 / 4194304, 4585033 / 16777216, 1 / 2 ^ 16⟩

/-- The interactive analysis: `δ = 1/4 - 2 ^ (-10)`, `δ' = 1/4 - 2 ^ (-12)`, a proximity loss of
`2 ^ (-16)` per fold. -/
def analysis : Analysis := ⟨1 / 4 - 1 / 2 ^ 10, 1 / 4 - 1 / 2 ^ 12, 1 / 2 ^ 16⟩

/-- The analysis of Plonky3's example, per oracle answer: `δ = 611429 / 2 ^ 21 ≈ 0.2916`,
`δ' = 2448527 / 2 ^ 23 ≈ 0.2919`, a proximity loss of `2 ^ (-60)` per fold. -/
def exampleRoAnalysis : Analysis := ⟨611429 / 2097152, 2448527 / 8388608, 1 / 2 ^ 60⟩

theorem coe_roRadius : ((4585033 / 16777216 : NNReal) : ℝ) = roAnalysis.δ' := by
  norm_num [roAnalysis]

theorem coe_exampleRadius : ((2448527 / 8388608 : NNReal) : ℝ) = exampleRoAnalysis.δ' := by
  norm_num [exampleRoAnalysis]

/-- **100 bits per oracle answer.** With the MCA bound up to the Johnson radius, the calculator
certifies every round error of the Keccak-f STARK with `188` queries and the grinding
`Grinding.johnson` on `2 ^ 12` to `2 ^ 21` rows to be at most `2 ^ (-100)`. -/
theorem secureRo (logN : ℕ) (h : Sized logN) :
    (stark 188 .johnson logN h).SecureRo KoalaBear.fieldSize .uniqueOrJohnson roAnalysis 100 := by
  refine secureRo_of_shape _ (shape_setup _ _ _) ?_
  have h1 := h.1
  have h2 := h.2
  interval_cases logN <;> obtain rfl : h = ⟨by decide, by decide⟩ := rfl <;> decide +kernel

/-- **100 bits of knowledge soundness.** Without grinding to credit, the calculator certifies the
knowledge error of the Keccak-f STARK with `247` queries on `2 ^ 12` to `2 ^ 21` rows to be at
most `2 ^ (-100)`. -/
theorem secure (logN : ℕ) (h : Sized logN) :
    (stark 247 .plonky3 logN h).Secure KoalaBear.fieldSize .uniqueOrJohnson analysis 100 := by
  refine secure_of_shape _ (shape_setup _ _ _) ?_
  have h1 := h.1
  have h2 := h.2
  interval_cases logN <;> obtain rfl : h = ⟨by decide, by decide⟩ := rfl <;> decide +kernel

/-- **59 bits per oracle answer at Plonky3's example configuration.** The calculator certifies
every round error of the Keccak-f STARK with `87` queries and Plonky3's grinding on `2 ^ 12` to
`2 ^ 21` rows to be at most `2 ^ (-59)`. -/
theorem example_secureRo (logN : ℕ) (h : Sized logN) :
    (stark 87 .plonky3 logN h).SecureRo KoalaBear.fieldSize .uniqueOrJohnson exampleRoAnalysis
      59 := by
  refine secureRo_of_shape _ (shape_setup _ _ _) ?_
  have h1 := h.1
  have h2 := h.2
  interval_cases logN <;> obtain rfl : h = ⟨by decide, by decide⟩ := rfl <;> decide +kernel

/-- Knowledge soundness in the random-oracle model of the Keccak-f STARK with `numQueries` queries
and the grinding `g` from the calculator's certificate of `bits` bits per oracle answer at the
analysis `A`, with the extractor at `δ' = A.δ'`. -/
theorem soundness_ro_of_secureRo {numQueries : ℕ+} {g : Grinding} {bits logN : ℕ}
    (h : Sized logN) (A : Analysis)
    (hsecure : (stark numQueries g logN h).SecureRo KoalaBear.fieldSize .uniqueOrJohnson A bits)
    (δ' : NNReal) (hδ' : (δ' : ℝ) = A.δ') (Q : ℕ)
    (prover : NIProver (stark numQueries g logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark numQueries g logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark numQueries g logN h) δ'
            (committedTrace (stark numQueries g logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark numQueries g logN h).verifierQueries) * (2 ^ bits)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark numQueries g logN h).verifierQueries) := by
  refine (KeccakAir.knowledgeSoundness_ro (stark numQueries g logN h) rfl
    (Real.toNNReal A.δ) δ' (lt_one_sub_rate _ A hsecure.1.1 _ hδ') Q prover hQ).trans ?_
  refine add_le_add (mul_le_mul_right ?_ _) le_rfl
  exact roundError_le_of_secureRo _ KoalaBear.card_eq McaBound.uniqueOrJohnson_holds A hsecure _ _
    (coe_toNNReal_δ A hsecure.1.1) hδ'

/-- **Plonky3's keccak-air proved by CompStark, in the random-oracle model.** On `2 ^ logN` rows,
`2 ^ 12` to `2 ^ 21`, with `188` queries and the grinding `Grinding.johnson`, a prover making at
most `Q` oracle calls gets a proof accepted while the rows read off every trace within
`δ' = 4585033 / 2 ^ 24 ≈ 0.2733` of the one it committed to fail to compute Keccak-f
(`Specs.Keccak256.keccakPermutation`) on some 24-row block starting at round 0, with probability at
most `q · 2 ^ (-100) + hashError q`, `q = Q + verifierQueries`. -/
theorem keccak_soundness_ro (logN : ℕ) (h : Sized logN) (Q : ℕ)
    (prover : NIProver (stark 188 .johnson logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark 188 .johnson logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark 188 .johnson logN h) (4585033 / 16777216)
            (committedTrace (stark 188 .johnson logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark 188 .johnson logN h).verifierQueries) * (2 ^ 100)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark 188 .johnson logN h).verifierQueries) :=
  soundness_ro_of_secureRo h roAnalysis (secureRo logN h) _ coe_roRadius Q prover hQ

/-- **Plonky3's keccak-air proved by CompStark, interactively.** On `2 ^ logN` rows, `2 ^ 12` to
`2 ^ 21`, with `247` queries, unless the rows read off some trace within
`δ' = 1023 / 4096 = 1/4 - 2 ^ (-12)` of the prover's committed trace compute Keccak-f on every
24-row block starting at round 0, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem keccak_soundness (logN : ℕ) (h : Sized logN)
    (prover : Prover (stark 247 .plonky3 logN h)) :
    (∀ trace ∈ closeTraces (stark 247 .plonky3 logN h) (1023 / 4096) prover.trace,
      ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)) →
      acceptance [] prover ≤ (2 ^ 100)⁻¹ := fun hfar => by
  have hsecure := secure logN h
  have hradius : ((1023 / 4096 : NNReal) : ℝ) = analysis.δ' := by norm_num [analysis]
  exact (KeccakAir.knowledgeSoundness (stark 247 .plonky3 logN h) rfl prover
    (Real.toNNReal analysis.δ) _ (lt_one_sub_rate _ analysis hsecure.1.1 _ hradius) hfar).trans
    (knowledgeError_le_of_secure _ KoalaBear.card_eq McaBound.uniqueOrJohnson_holds analysis
      hsecure _ _ (coe_toNNReal_δ analysis hsecure.1.1) hradius)

/-- **Plonky3's example configuration, in the random-oracle model.** With the `87` queries and
the grinding of Plonky3's example `prove_prime_field_31`, on `2 ^ 12` to `2 ^ 21` rows, the
statement of `keccak_soundness_ro` holds with the extractor at `δ' = 2448527 / 2 ^ 23 ≈ 0.2919`
and `2 ^ (-59)` per oracle call. -/
theorem keccak_soundness_ro_example (logN : ℕ) (h : Sized logN) (Q : ℕ)
    (prover : NIProver (stark 87 .plonky3 logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark 87 .plonky3 logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark 87 .plonky3 logN h) (2448527 / 8388608)
            (committedTrace (stark 87 .plonky3 logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark 87 .plonky3 logN h).verifierQueries) * (2 ^ 59)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark 87 .plonky3 logN h).verifierQueries) :=
  soundness_ro_of_secureRo h exampleRoAnalysis (example_secureRo logN h) _ coe_exampleRadius Q
    prover hQ

end CleanCompStark.KeccakShowcase
