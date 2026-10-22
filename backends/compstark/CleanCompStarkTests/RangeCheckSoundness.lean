module

public import CleanCompStarkTests.RangeCheck

@[expose] public section

/-!
# Knowledge soundness of the range check's batch STARK

The batch of `RangeCheck` on 16 queries, as a `Batch.Setup` (`toBatchSetup`), and its knowledge
soundness: unless every query read off some pair of traces close to the committed ones is a byte,
the verifier accepts with probability at most the knowledge error.
-/

namespace CleanCompStarkTests.RangeCheck
open CleanCompStark CompStark CompStark.Stark CompStark.Iop Air.Flat

local notation "EF" => _root_.BabyBear.Fast.Ext4

/-- The queries on `2 ^ 4` rows, the bytes on `2 ^ 8`. -/
def logN (i : Fin (ensemble 16).tables.length) : ℕ := if i.val = 0 then 4 else 8

theorem valid_air (A : Air K) (logN : ℕ) (hcols : A.ColsInWidth)
    (hsize : A.preprocessed.size = 2 ^ logN * A.preprocessedWidth) (hperiodic : A.periodic = [])
    (hdegree : A.DegreeFits logN) (hlog : logN ≤ 25) (hchunks : A.logQuotientChunks logN ≤ 2)
    (hpos : 0 < logN) : ValidConfig params A logN where
  colsInWidth := hcols
  preprocessedSize := hsize
  periodicFits := by simp [Air.periodicFits, hperiodic]
  degreeFits := hdegree
  twoAdic := by simp only [params, BabyBear.twoAdicity_eq]; omega
  chunksFit := hchunks
  folds := by decide
  finalPolyFits := by simp only [params]; omega
  queries := by decide
  blowup := by decide

theorem valid_queries : ValidConfig params (toAir babyBear (queries 16) 4) 4 :=
  valid_air _ 4 (by unfold Air.ColsInWidth; decide +kernel) (by decide +kernel) rfl
    (by unfold Air.DegreeFits Air.DegreeFitsAt; decide +kernel) (by norm_num)
    (by decide +kernel) (by norm_num)

theorem valid_bytes : ValidConfig params (toAir babyBear (bytes (p := p)).component 8) 8 :=
  valid_air _ 8 (by unfold Air.ColsInWidth; decide +kernel) (by decide +kernel) rfl
    (by unfold Air.DegreeFits Air.DegreeFitsAt; decide +kernel) (by norm_num)
    (by decide +kernel) (by norm_num)

theorem lookupsValid_of (A : Air K) (logN : ℕ) (ls : List (Stark.Lookup K))
    (hchunks : A.logQuotientChunksWith logN (Lookup.logUpConstraints ls) ≤ params.logBlowup)
    (hfits : ∀ l ∈ ls,
      l.Fits A.width A.mainNextWidth A.preprocessedWidth A.preprocessedNextWidth) :
    LookupsValid params A logN ls := by
  cases ls with
  | nil => trivial
  | cons l ls => exact ⟨hchunks, hfits⟩

theorem lookupsValid_queries : LookupsValid params (toAir babyBear (queries 16) 4) 4
    (Batch.instanceLookups true (toAir babyBear (queries 16) 4) 4) :=
  lookupsValid_of _ _ _ (by decide +kernel) (by unfold Stark.Lookup.Fits; decide +kernel)

theorem lookupsValid_bytes : LookupsValid params (toAir babyBear (bytes (p := p)).component 8) 8
    (Batch.instanceLookups true (toAir babyBear (bytes (p := p)).component 8) 8) :=
  lookupsValid_of _ _ _ (by decide +kernel) (by unfold Stark.Lookup.Fits; decide +kernel)

/-- The batch STARK of the range check on 16 queries. -/
def setup : Batch.Setup EF :=
  toBatchSetup babyBear (ensemble 16) params logN
    (fun i => match i with | ⟨0, _⟩ => valid_queries | ⟨1, _⟩ => valid_bytes)
    (fun i => match i with
      | ⟨0, _⟩ => show 0 < 4 by decide
      | ⟨1, _⟩ => show 0 < 8 by decide) (fun _ => Nat.zero_le _) (by decide)
    (fun i => match i with | ⟨0, _⟩ => lookupsValid_queries | ⟨1, _⟩ => lookupsValid_bytes)
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem bridgeable_ensemble : EnsembleBridgeable (ensemble 16) where
  components := by
    simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨by decide +kernel, by decide +kernel⟩
  verifier := rfl
  names := by simp [ensemble]
  channels := by
    simp [circuit_norm, ensemble, queries, query, bytes, Lookup.component, Lookup.provider]

theorem proves : ProvesEnsemble babyBear setup (ensemble 16) :=
  provesEnsemble_toBatchSetup babyBear _ _ _ _ _ _ _ _ _

theorem fits (i : Fin setup.k) :
    Fits (K := K) (componentAt (ensemble 16) proves.length i) (setup.logN i) := by
  match i with
  | ⟨0, _⟩ => exact ⟨show 4 ≤ twoAdicity K by rw [BabyBear.twoAdicity_eq]; norm_num,
      show 4 ≤ 64 by norm_num, by rintro _ ⟨⟩; rfl⟩
  | ⟨1, _⟩ => exact ⟨show 8 ≤ twoAdicity K by rw [BabyBear.twoAdicity_eq]; norm_num,
      show 8 ≤ 64 by norm_num, by rintro _ ⟨⟩; rfl⟩

theorem interactionCount_lt :
    interactionCount (ensemble 16) proves.length setup.logN < ringChar (F p) := by
  rw [ZMod.ringChar_zmod_n]
  decide +kernel

/-- **Knowledge soundness of the range check's batch STARK.** Unless every query read off some
pair of traces, each within `δ'` of its instance's committed trace, is a byte, the verifier
accepts with probability at most the knowledge error. -/
theorem knowledgeSoundness (prover : Batch.Prover setup) (δ δ' : NNReal)
    (hδ' : (δ' : ℝ) < 1 - setup.rate) :
    (∀ traces ∈ Batch.closeTraces setup δ' prover.trace, ¬ QueriesInRange
      (List.ofFn fun i => toRows babyBear (componentAt (ensemble 16) proves.length i)
        (setup.logN i) (traces i))) →
      Batch.acceptance (fun _ => []) prover ≤ Batch.knowledgeError setup δ δ' :=
  batchKnowledgeSoundness_of_witnessSound babyBear proves bridgeable_ensemble fits
    interactionCount_lt (witnessSound 16) () _ prover δ δ' hδ'

/--
info: 'CleanCompStarkTests.RangeCheck.knowledgeSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms knowledgeSoundness

end CleanCompStarkTests.RangeCheck
