import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Specs.Pallas

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/lookup_range_check.rs`
- `LookupRangeCheckConfig<F, K>` (lines 63-70)
- `configure` (lines 313-387)
- `load_range_check_table` (lines 434-450)
- `short_range_check` (lines 455-490)

The first lookup-consuming gadget ported to Halo2-Clean. Mirrors the `AddIncomplete`
/`WitnessPoint` template: a `Config` holding exactly the Rust `Config` fields, the lookup
argument and the bitshift gate as standalone pure defs of the config pieces (referenced by
`configure`, `synthesize` and the proofs), and the `FormalRegionCircuit` bundle for
`short_range_check`. The table loader is a plain `Circuit … Unit` with a standalone
table-contents theorem (packaging discussion below).

Genericity over `K`: the Rust is `LookupRangeCheckConfig<F, const K>`; the Orchard
instantiation uses `K = 10`. We keep the `Config`, `configure`, gate/argument defs, loader
and `short_range_check` generic over `K : ℕ`. The value-level range arithmetic needs
`2^K · 2^K < |Fp|`; rather than hardcode `K = 10`, the value lemmas take that field-card
bound as an explicit hypothesis, so the whole port stays `K`-generic (the Orchard `K = 10`
discharges the bound by `norm_num`). See `lookup-design.md` §4.

The pure field-arithmetic core (the `2^(K−num_bits)` shift argument) is lifted from the
phase-one donor `Clean/Orchard/Utilities.lean`, namespace `LookupRangeCheck` — restated
`K`-generically here.
-/

namespace Zcash.Circuits.LookupRangeCheck

open Halo2
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- Rust `LookupRangeCheckConfig<F, K>` (`lookup_range_check.rs:63-70`).
`qLookup`, `qRunning` are complex selectors (they appear inside a lookup input, where
simple selectors are banned — `lookup-design.md` §1.1); `qBitshift` is a simple selector
(it only guards an ordinary gate). -/
structure Config (K : ℕ) where
  qLookup : Selector
  qRunning : Selector
  qBitshift : Selector
  runningSum : Column .advice
  tableIdx : TableColumn

/-! ## The lookup argument and the bitshift gate as standalone defs

Both are pure functions of the config pieces, so they are known at every use site
(the `configure` registration, `synthesize`, and the proofs all reference these same
defs — the established gate/argument pattern). -/

/-- The range-check lookup argument, ported verbatim from `configure`
(`lookup_range_check.rs:334-366`; `lookup-design.md` §1.4). The single `(input, table)`
pair is

  `q_lookup · (q_running · (z_cur − 2^K·z_next) + (1 − q_running) · z_cur)  ↦  table_idx`

where the table side is `table_idx`'s rotation-0 fixed query. Which word the gated input
reduces to depends on which selectors are enabled at the row (running-sum vs short row). -/
@[query_correct, circuit_norm]
def rangeCheckInputFor (K : ℕ) (qLookup qRunning : Selector)
    (runningSum : Column .advice) : Expression Fp Query :=
  let qL : Expression Fp Query := querySelector qLookup
  let qR : Expression Fp Query := querySelector qRunning
  let zCur : Expression Fp Query := queryAdvice runningSum 0
  let zNext : Expression Fp Query := queryAdvice runningSum 1
  -- Rust builds `z_cur - z_next * F::from(1 << K)` (`lookup_range_check.rs:347`): the
  -- `2^K` is a FIELD scalar on the RIGHT of `z_next` (`impl Mul<F>`), so the AST is
  -- `.scaled z_next 2^K`, NOT `product(const, z_next)`. Spell it `zNext * (2^K : Fp)`.
  qL * (qR * (zCur - zNext * (2 ^ K : Fp)) + (1 - qR) * zCur)

@[query_correct, circuit_norm]
def rangeCheckInput (K : ℕ) (cfg : Config K) : Expression Fp Query :=
  rangeCheckInputFor K cfg.qLookup cfg.qRunning cfg.runningSum

@[query_correct, circuit_norm]
def rangeCheckLookupFor (K : ℕ) (qLookup qRunning : Selector)
    (runningSum : Column .advice) (tableIdx : TableColumn) : LookupArgument Fp where
  masterSelector := qLookup
  inputs := [rangeCheckInputFor K qLookup qRunning runningSum]
  tables := [queryFixed tableIdx.inner]
  tablesFree := by simp [Expression.SelectorFree, queryFixed]
  arity := rfl

@[query_correct]
def rangeCheckLookup (K : ℕ) (cfg : Config K) : LookupArgument Fp :=
  rangeCheckLookupFor K cfg.qLookup cfg.qRunning cfg.runningSum cfg.tableIdx

@[configure_selector_norm, keygen_norm] theorem delta_rangeCheckLookup_lookups
    (K : ℕ) (qLookup qRunning : Selector)
    (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    ((lookup [queryAdvice runningSum 0, queryAdvice runningSum 1]
      qLookup [(rangeCheckInputFor K qLookup qRunning runningSum, tableIdx)]).delta
        counts).lookups =
      [rangeCheckLookupFor K qLookup qRunning runningSum tableIdx] := by
  unfold Halo2.lookup rangeCheckLookupFor
  rfl

@[circuit_norm, synthesis_summary_norm, keygen_norm]
theorem rangeCheckLookup_masterSelector (K : ℕ) (cfg : Config K) :
    (rangeCheckLookup K cfg).masterSelector = cfg.qLookup := rfl

@[keygen_norm]
theorem qLookup_mem_rangeCheckLookup_selectorIndices (K : ℕ) (cfg : Config K) :
    cfg.qLookup.index ∈ (rangeCheckLookup K cfg).selectorIndices := by
  simpa only [rangeCheckLookup_masterSelector] using
    (rangeCheckLookup K cfg).masterSelector_mem_selectorIndices

@[keygen_norm]
theorem qRunning_mem_rangeCheckLookup_selectorIndices (K : ℕ) (cfg : Config K) :
    cfg.qRunning.index ∈ (rangeCheckLookup K cfg).selectorIndices := by
  rw [LookupArgument.selectorIndices, List.mem_cons]
  by_cases hmaster : cfg.qRunning.index = cfg.qLookup.index
  · exact Or.inl hmaster
  · right
    rw [LookupArgument.auxiliarySelectorIndices, List.mem_filter]
    exact ⟨by
      simp only [rangeCheckLookup]
      tauto,
      by simpa [rangeCheckLookup_masterSelector] using hmaster⟩

@[keygen_norm]
theorem qRunning_declared_by_rangeCheckLookup (K : ℕ) (cfg : Config K) :
    cfg.qRunning.index = cfg.qLookup.index ∨
      cfg.qRunning.index ∈ (rangeCheckLookup K cfg).auxiliarySelectorIndices := by
  simpa only [rangeCheckLookup_masterSelector, LookupArgument.selectorIndices,
    List.mem_cons] using
    qRunning_mem_rangeCheckLookup_selectorIndices K cfg

/-- The "Short lookup bitshift" gate, ported verbatim from `configure`
(`lookup_range_check.rs:370-384`). Reads `word` at `Rotation::prev()` (−1), `shifted_word`
at `Rotation::cur()` (0), `inv_two_pow_s` at `Rotation::next()` (+1); the single constraint
is `word · 2^K · inv_two_pow_s − shifted_word`. -/
def bitshiftGate (K : ℕ) (cfg : Config K) : Gate Fp :=
  let word : Expression Fp Query := queryAdvice cfg.runningSum (-1)
  let shiftedWord : Expression Fp Query := queryAdvice cfg.runningSum 0
  let invTwoPowS : Expression Fp Query := queryAdvice cfg.runningSum 1
  Gate.withSelector "Short lookup bitshift" cfg.qBitshift
    [word, shiftedWord, invTwoPowS]
    [("bitshift", word * (2 ^ K : Fp) * invTwoPowS - shiftedWord)]

@[circuit_norm, keygen_norm] theorem bitshiftGate_selector (K : ℕ) (cfg : Config K) :
    (bitshiftGate K cfg).selector = cfg.qBitshift := rfl

/-- Rust `configure` (`lookup_range_check.rs:313-387`): enable equality on `running_sum`,
allocate the two complex selectors and the simple `q_bitshift`, take the handed-down
`table_idx` lookup column, register the lookup argument and the bitshift gate. -/
def configure (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn) :
    Configure Fp (Config K) := do
  enableEquality runningSum.toAny
  let qLookup ← complexSelector
  let qRunning ← complexSelector
  let qBitshift ← selector
  let cfg : Config K := { qLookup, qRunning, qBitshift, runningSum, tableIdx }
  -- register the lookup: one (input, table) pair, verbatim §1.4
  lookup [queryAdvice runningSum 0, queryAdvice runningSum 1] qLookup
    [(rangeCheckInputFor K qLookup qRunning runningSum, tableIdx)]
  -- register the bitshift gate
  createGate (bitshiftGate K cfg)
  return cfg

@[configure_selector_norm, keygen_norm] theorem configure_output_qLookup_index
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    ((configure K runningSum tableIdx).output counts).qLookup.index =
      counts.numSelectors := by
  simp [configure, keygen_norm]

@[configure_selector_norm, keygen_norm] theorem configure_output_qRunning_index
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    ((configure K runningSum tableIdx).output counts).qRunning.index =
      counts.numSelectors + 1 := by
  simp [configure, keygen_norm]

@[configure_selector_norm, keygen_norm] theorem configure_output_qBitshift_index
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    ((configure K runningSum tableIdx).output counts).qBitshift.index =
      counts.numSelectors + 2 := by
  simp [configure, keygen_norm]

@[configure_selector_norm, keygen_norm]
theorem configure_output_lookup_auxiliarySelectorIndices
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    (rangeCheckLookup K
      ((configure K runningSum tableIdx).output counts)).auxiliarySelectorIndices =
      [counts.numSelectors + 1, counts.numSelectors + 1] := by
  simp [rangeCheckLookup, rangeCheckLookupFor, rangeCheckInputFor,
    LookupArgument.auxiliarySelectorIndices, Expression.selectorIndices,
    Expression.selectorIndices_querySelector,
    Expression.selectorIndices_queryAdvice, keygen_norm]

@[configure_selector_norm, keygen_norm]
theorem configure_output_lookup_selectorIndices
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    (rangeCheckLookup K
      ((configure K runningSum tableIdx).output counts)).selectorIndices =
      [counts.numSelectors, counts.numSelectors + 1,
        counts.numSelectors + 1] := by
  simp [LookupArgument.selectorIndices, rangeCheckLookup_masterSelector, keygen_norm]

@[configure_selector_norm, keygen_norm] theorem configure_finalCounts_numSelectors
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    ((configure K runningSum tableIdx).finalCounts counts).numSelectors =
      counts.numSelectors + 3 := by
  simp [configure]

theorem gate_lookupSelectorsCompatible_configure_output
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) (gate : Gate Fp)
    (hgate : gate.selector.index < counts.numSelectors) :
    gate.LookupSelectorsCompatible
      (rangeCheckLookup K ((configure K runningSum tableIdx).output counts)) := by
  rw [Gate.LookupSelectorsCompatible,
    configure_output_lookup_auxiliarySelectorIndices]
  simp only [List.forall_cons, List.forall_nil, and_true]
  constructor <;> omega

@[configure_selector_norm, keygen_norm] theorem configure_delta_lookups (K : ℕ)
    (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    ((configure K runningSum tableIdx).delta counts).lookups =
      [rangeCheckLookup K ((configure K runningSum tableIdx).output counts)] := by
  unfold configure lookup
  rfl

@[configure_selector_norm, keygen_norm] theorem configure_delta_gates (K : ℕ)
    (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    ((configure K runningSum tableIdx).delta counts).gates =
      [bitshiftGate K ((configure K runningSum tableIdx).output counts)] := by
  unfold configure
  rfl

@[reducible] private def configureInferred
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn) :
    ElaboratedConfigure (configure K runningSum tableIdx) := by
  unfold configure
  infer_instance

private theorem configure_selectorRequirements
    (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn) (counts) :
    (configureInferred K runningSum tableIdx).selectorRequirements counts := by
  dsimp only [configureInferred, configure]
  simp only [configure_selector_norm]
  simp [configure_selector_norm, ConfigureDelta.LookupSelectorsCrossCompatible,
    Gate.LookupSelectorsCompatible]
  simp [keygen_norm, rangeCheckLookupFor, rangeCheckInputFor,
    lookupInputSelectorBound, LookupArgument.inputSelectorBound,
    LookupArgument.auxiliarySelectorIndices,
    Expression.selectorIndices]
  simp [Expression.selectorBound]

instance (K : ℕ) (runningSum : Column .advice) (tableIdx : TableColumn) :
    ElaboratedConfigure (configure K runningSum tableIdx) :=
  (configureInferred K runningSum tableIdx).closeSelectorRequirements
    (configure_selectorRequirements K runningSum tableIdx)

/-! ## The table loader

Packaging decision: a plain `def load … : Circuit Fp Unit` emitting the single `loadTable`
op, plus a standalone table-contents theorem proven from its `Constraints`. We do NOT wrap
it in a `FormalCircuit` (the design sketch's suggestion): the layouter-level formal-circuit
`call`/forward-lemma machinery is not yet ported (only `FormalRegionCircuit` proofs exist
in the Ironwood tree, and `FormalCircuit` has no `_iff` helpers landed), and the loader's
sole content IS the table-contents fact, which the theorem below states directly from the
`loadTable` `Constraints`. This keeps the loader usable by consumers today with no
dependence on unported layouter-level formal-circuit plumbing. -/

private theorem pow_two_pos (n : ℕ) : 0 < 2 ^ n := pow_pos (by norm_num) n

/-- Rust `load_range_check_table` (`lookup_range_check.rs:434-450`): fill `table_idx` with
`0, 1, …, 2^K − 1`. Emits the single `loadTable` layouter op. -/
def load (K : ℕ) (cfg : Config K) : Circuit Fp Unit :=
  loadTable cfg.tableIdx ((List.range (2 ^ K)).map Nat.cast)

/-- The table-contents predicate a lookup-user gadget's `EnvAssumptions` references. Three
conjuncts (see `load_tableLoaded` below for the discharge from a real `load`):

1. **Domain-size fact** — the table's explicit block fits in the usable rows,
   `2^K ≤ env.usableRows`. Pure layout data (the circuit's `k` must accommodate the
   table); the `loadTable` constraints do not force it (the default-fill conjunct is
   vacuous when `usableRows < 2^K`), so it lives here as an env fact — exactly what
   `EnvAssumptions` is for. Completeness needs it to bound its membership witnesses.
2. **Usable-rows range bound** — every usable row of `table_idx` holds a value `< 2^K`.
   Soundness consumes this: the membership existential's witness is bounded by
   `env.usableRows` (`Operations.lean`; faithful to `lookup/prover.rs:573-585`), so the
   bound on usable rows suffices. Provable from `load`'s constraints alone (explicit block
   on `[0, 2^K)`, default row-0 value `0 < 2^K` on the fill).
3. **Block exact contents** — row `r ∈ [0, 2^K)` holds exactly `↑r`. Completeness consumes
   this to *witness* the membership existential: the honest word `w < 2^K` sits at row
   `w.val` as `↑(w.val) = w` (usable by conjunct 1).

This is the `TableLoaded` of the design sketch; consumers share it. -/
def TableLoaded (K : ℕ) (cfg : Config K) (env : Environment Fp) : Prop :=
  2 ^ K ≤ env.usableRows ∧
  (∀ r : ℕ, r < env.usableRows → (env.fixed cfg.tableIdx.inner (r : ℤ)).val < 2 ^ K) ∧
  (∀ r : ℕ, r < 2 ^ K → env.fixed cfg.tableIdx.inner (r : ℤ) = (r : Fp))

/-- **Membership-consumption helper** (C2a #5). Turn a lookup-membership existential (the
`enableLookup` constraint's `∃ tableRow < usableRows, value = env.fixed tableIdx tableRow`) plus
the `TableLoaded` usable-rows bound (`TableLoaded`'s second conjunct — `hTableLt`) into the value
bound `value.val < 2^K`, in one application. This is the "two `obtain`s + application, same shape
everywhere" pattern (`hMemWord`/`hMemShift` in `short_range_check` soundness, mirrored in every
lookup consumer) collapsed to a single `exact`. -/
theorem mem_usableRows_val_lt {K : ℕ} {cfg : Config K} {env : Environment Fp} {v : Fp}
    (hTableLt : ∀ r : ℕ, r < env.usableRows → (env.fixed cfg.tableIdx.inner (r : ℤ)).val < 2 ^ K)
    (hMem : ∃ tableRow : ℕ, tableRow < env.usableRows
      ∧ v = env.fixed cfg.tableIdx.inner (tableRow : ℤ)) :
    v.val < 2 ^ K := by
  obtain ⟨r, hr, hrv⟩ := hMem
  rw [hrv]; exact hTableLt r hr

/-- Exact table-contents theorem: from the `loadTable`'s `Constraints`, every row in the
explicit block `[0, 2^K)` holds the field element `↑r`. Proven from the explicit-block
conjunct only, so it holds regardless of `usableRows`. `hK : 2^K ≤ |Fp|` is needed to
know the load values `↑0, …, ↑(2^K−1)` are distinct field elements (it is what makes
`(↑r).val = r`); the Orchard `K = 10` discharges it by `norm_num`. -/
theorem load_tableIdx_eq (K : ℕ) (cfg : Config K) (place : RegionIndex → ℕ)
    (env : Environment Fp) (i : RegionIndex)
    (h : Halo2.Constraints place env ((load K cfg).operations i) i) :
    ∀ r : ℕ, r < 2 ^ K → env.fixed cfg.tableIdx.inner (r : ℤ) = (r : Fp) := by
  -- unfold `load` to expose the `loadTable` op, but keep `List.map` intact (don't let
  -- `circuit_norm` rewrite it to `flatMap`)
  simp only [load, Circuit.operations, loadTable, Halo2.Constraints] at h
  obtain ⟨hexplicit, _hfill⟩ := h
  intro r hr
  have hlen : r < ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp)).length := by
    simpa using hr
  have hval : ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp))[r]! = (r : Fp) := by
    rw [getElem!_pos _ r hlen, List.getElem_map, List.getElem_range]
  rw [hexplicit r hlen, hval]

/-- Range table-contents theorem: every row in the explicit block `[0, 2^K)` holds a value
`< 2^K`. The bound `short_range_check` soundness consumes. -/
theorem load_tableIdx_lt (K : ℕ) (cfg : Config K) (place : RegionIndex → ℕ)
    (env : Environment Fp) (i : RegionIndex)
    (hK : 2 ^ K ≤ PALLAS_BASE_CARD)
    (h : Halo2.Constraints place env ((load K cfg).operations i) i) :
    ∀ r : ℕ, r < 2 ^ K → (env.fixed cfg.tableIdx.inner (r : ℤ)).val < 2 ^ K := by
  intro r hr
  rw [load_tableIdx_eq K cfg place env i h r hr]
  rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le hr hK)]
  exact hr

/-- **`load` ⇒ `TableLoaded`**: the loader's `Constraints` discharge the whole `TableLoaded`
predicate. The usable-rows range bound (conjunct 2) needs no extra assumption: rows
`[0, 2^K)` come from the explicit block, rows `[2^K, usableRows)` from the default-fill
(row-0 value `0`, and `0 < 2^K`). Only the domain-size fact `2^K ≤ env.usableRows`
(conjunct 1) is a hypothesis — it is layout data the load constraints cannot force (the
default-fill conjunct is vacuous when `usableRows < 2^K`); the top-level statement
discharges it from the floor planner's `k`. -/
theorem load_tableLoaded (K : ℕ) (cfg : Config K) (place : RegionIndex → ℕ)
    (env : Environment Fp) (i : RegionIndex)
    (hK : 2 ^ K ≤ PALLAS_BASE_CARD)
    (hUsable : 2 ^ K ≤ env.usableRows)
    (h : Halo2.Constraints place env ((load K cfg).operations i) i) :
    TableLoaded K cfg env := by
  refine ⟨hUsable, ?_, load_tableIdx_eq K cfg place env i h⟩
  -- the usable-rows bound: explicit block below 2^K, default-fill (value 0) above
  intro r hr
  by_cases hblock : r < 2 ^ K
  · exact load_tableIdx_lt K cfg place env i hK h r hblock
  · -- default-fill row: value is the row-0 load value, `↑0 = 0`
    simp only [load, Circuit.operations, loadTable, Halo2.Constraints] at h
    obtain ⟨_hexplicit, hfill, -⟩ := h
    have hne : ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp)) ≠ [] := by
      simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
      exact (pow_two_pos K).ne'
    have hlen : ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp)).length ≤ r := by
      simpa using Nat.le_of_not_lt hblock
    rw [hfill hne r hlen hr]
    have h0 : ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp))[0]! = (0 : Fp) := by
      have hlen0 : 0 < ((List.range (2 ^ K)).map (Nat.cast : ℕ → Fp)).length := by
        simp [pow_two_pos K]
      rw [getElem!_pos _ 0 hlen0, List.getElem_map, List.getElem_range]
      norm_num
    rw [h0]
    simp [pow_two_pos K]

/-! ## The pure value-math core of `short_range_check` soundness

Lifted from the phase-one donor `Clean/Orchard/Utilities.lean`,
`LookupRangeCheck.shortRange_soundness_aux`, restated `K`-generically with the field-card
bound as an explicit hypothesis. Zero framework vocabulary — pure `Fp`/`ℕ` arithmetic:
`element·2^(K−num_bits) < 2^K ∧ element < 2^K ⇒ element < 2^num_bits`. -/

/-- The shift argument (donor `shortRange_soundness_aux`). If the word and its shift by
`2^(K−num_bits)` are both `< 2^K`, then the word is `< 2^num_bits`. The card bound
`2^K · 2^K < |Fp|` licenses reading the product `word.val · 2^(K−num_bits)` off the field
element `shifted`. -/
theorem shortRange_soundness_aux (K numBits : ℕ) (hNumBits : numBits ≤ K)
    (hCard : 2 ^ K * 2 ^ K < PALLAS_BASE_CARD)
    (word shifted : Fp)
    (hWord : word.val < 2 ^ K)
    (hShifted : shifted.val < 2 ^ K)
    (hEq : shifted = word * (2 ^ (K - numBits) : Fp)) :
    word.val < 2 ^ numBits := by
  have hProdLtCard : word.val * 2 ^ (K - numBits) < PALLAS_BASE_CARD := by
    calc
      word.val * 2 ^ (K - numBits) < 2 ^ K * 2 ^ K :=
        Nat.mul_lt_mul_of_lt_of_le hWord
          (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le K numBits)) (pow_two_pos _)
      _ < PALLAS_BASE_CARD := hCard
  have hShiftedVal : shifted.val = word.val * 2 ^ (K - numBits) := by
    rw [hEq, ← ZMod.natCast_zmod_val word]
    have hPowCast : (2 ^ (K - numBits) : Fp) = ((2 ^ (K - numBits) : ℕ) : Fp) := by norm_num
    rw [hPowCast, ← Nat.cast_mul, ZMod.val_natCast_of_lt word.val_lt]
    exact ZMod.val_natCast_of_lt hProdLtCard
  by_contra h
  have hge : 2 ^ numBits ≤ word.val := Nat.le_of_not_gt h
  have hle : 2 ^ K ≤ word.val * 2 ^ (K - numBits) := by
    calc
      2 ^ K = 2 ^ numBits * 2 ^ (K - numBits) := by
        rw [Nat.mul_comm, ← pow_add]; congr 1; omega
      _ ≤ word.val * 2 ^ (K - numBits) := Nat.mul_le_mul_right _ hge
  rw [hShiftedVal] at hShifted
  exact Nat.not_lt_of_ge hle hShifted

/-- Completeness shift-bound (donor `shortRange_completeness_shifted`): if `word < 2^num_bits`
then its shift by `2^(K−num_bits)` is `< 2^K`. -/
theorem shortRange_completeness_shifted (K numBits : ℕ) (hNumBits : numBits ≤ K)
    (hCard : 2 ^ K < PALLAS_BASE_CARD)
    (word : Fp) (hWord : word.val < 2 ^ numBits) :
    (word * (2 ^ (K - numBits) : Fp)).val < 2 ^ K := by
  have hProdLt : word.val * 2 ^ (K - numBits) < 2 ^ K := by
    calc
      word.val * 2 ^ (K - numBits) < 2 ^ numBits * 2 ^ (K - numBits) :=
        Nat.mul_lt_mul_of_pos_right hWord (pow_two_pos _)
      _ = 2 ^ K := by rw [Nat.mul_comm, ← pow_add]; congr 1; omega
  have hProdLtCard : word.val * 2 ^ (K - numBits) < PALLAS_BASE_CARD := lt_trans hProdLt hCard
  rw [← ZMod.natCast_zmod_val word]
  have hPowCast : (2 ^ (K - numBits) : Fp) = ((2 ^ (K - numBits) : ℕ) : Fp) := by norm_num
  rw [hPowCast, ← Nat.cast_mul, ZMod.val_natCast_of_lt hProdLtCard]
  exact hProdLt

/-! ## `short_range_check` — the region-level gadget

Rust `LookupRangeCheckConfig::short_range_check` (`lookup_range_check.rs:455-490`). Given
`element` (which must already be assignable at `running_sum` offset 0), it:
- copies `element` into `running_sum` at `offset` and enables `q_lookup` there (a short
  lookup — `q_running` OFF — forcing `element ∈ [0, 2^K)`);
- assigns `element · 2^(K−num_bits)` into `running_sum` at `offset + 1` and enables
  `q_lookup` there too (forcing the shifted word `∈ [0, 2^K)`);
- assigns `2^(−num_bits)` (as a constant) into `running_sum` at `offset + 2`;
- enables `q_bitshift` at `offset + 1`, tying `shifted = word · 2^K · 2^(−num_bits)`.

Membership at the two short rows + the loaded table (`EnvAssumptions := TableLoaded`) give
`word, shifted < 2^K`; the bitshift gate gives `shifted = word · 2^(K−num_bits)`; the shift
argument (`shortRange_soundness_aux`) then yields `element.val < 2^num_bits`. -/

/-- Single-field input: the `element` to be range-checked (an already-assigned cell) — the
input of the running-sum `rangeCheck`/`copyCheck` (Rust copies the element in there). -/
structure Inputs (F : Type) where
  element : F
deriving ProvableStruct

/-- The word at `offset+2`: `2^(−num_bits) = (2^num_bits)⁻¹`, assigned as a constant. -/
def invTwoPowS (numBits : ℕ) : Fp := (2 ^ numBits : Fp)⁻¹

-- `cellAt` (naming a cell at a fixed row) lives in the framework (`Basic.lean`).

/-- Exact reduced footprint of a positional short range check. -/
def shortRangeCheckSynthesisSummary {K : ℕ} (cfg : Config K)
    (offset : ℕ) : FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.qLookup.index, .column .advice cfg.runningSum.index,
      .selector cfg.qLookup.index, .column .advice cfg.runningSum.index,
      .selector cfg.qBitshift.index]
    (offset + 3) 1

/-- Rust `short_range_check` (`lookup_range_check.rs:455-490`), POSITIONAL: the element
"must have been assigned to `running_sum` at `offset`" by the caller (no copy — Rust has no
copy-in short check; `witness_short_check` is the caller-side `assign_advice` + this).
The returned cell is the positional element cell (Rust hands the witnessed cell out for
downstream copies). -/
def shortRangeCheck (K numBits : ℕ) :
    FormalRegionCircuit Fp (Config K) (Config K) unit field where
  configure := fun cfg => pure cfg

  synthesize cfg offset _ := do
    -- the caller-assigned `element` at `offset`; short lookup there (q_running OFF)
    let elt ← cellAt cfg.runningSum offset
    (rangeCheckLookup K cfg).enable [] offset
    -- assign shifted = element · 2^(K − num_bits) at `offset + 1`; short lookup there too
    let _shifted ← assignAdvice cfg.runningSum (offset + 1)
      (.ofFExpr ((.expr elt) * (.const (2 ^ (K - numBits) : Fp))))
    (rangeCheckLookup K cfg).enable [] (offset + 1)
    -- assign 2^(−num_bits) as a constant at `offset + 2`
    let invCell ← assignAdvice cfg.runningSum (offset + 2) (.ofFExpr (.const (invTwoPowS numBits)))
    constrainConstant invCell (invTwoPowS numBits)
    -- bitshift gate at `offset + 1`
    (bitshiftGate K cfg).enable (offset + 1)
    return elt

  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [bitshiftGate K cfg]
          lookups cfg _ := [rangeCheckLookup K cfg]
          permutationColumns cfg _ := [cfg.runningSum] }
      synthesisSummary cfg offset _ _ :=
        shortRangeCheckSynthesisSummary cfg offset
      synthesisSummary_eq := by
        intro _ _ _ _
        apply FloorPlanner.RegionSynthesisSummary.ext
        · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [shortRangeCheckSynthesisSummary, circuit_norm,
            List.flatMap_cons, List.flatMap_nil,
            FloorPlanner.regionOperationShapeColumns, List.map_cons, List.map_nil,
            List.singleton_append, List.append_nil,
            FloorPlanner.RegionSynthesisSummary.ofColumns_columns]
        · simp only [shortRangeCheckSynthesisSummary, circuit_norm,
            FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
          omega
        · simp only [shortRangeCheckSynthesisSummary, circuit_norm,
            FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]
      registered := by keygen_registration }

  -- Ambient preconditions discharged by the caller: (1) the table is loaded — every usable
  -- table row holds a value `< 2^K`, the block holds exact contents, and the block fits the
  -- domain (`TableLoaded`; discharged by `load_tableLoaded`); (2) config well-formedness —
  -- `q_lookup` and `q_running` are *distinct* selectors (they are allocated separately in
  -- `configure`, so `configure`-produced configs satisfy it), which is what makes the short
  -- rows here (`q_running` OFF) read `z_cur` and not the running word. The framework note on
  -- `FormalRegionCircuit` anticipates exactly such a `ConfigWF` hypothesis; `EnvAssumptions`
  -- (now config-aware) is the available slot for it.
  EnvAssumptions cfg env :=
    TableLoaded K cfg env.env ∧ cfg.qLookup.index ≠ cfg.qRunning.index
  -- Rust comment: `element` must be `< 2^num_bits` for `num_bits ≤ K`; we carry `num_bits ≤ K`
  -- (and the field-card bound, needed for the value arithmetic) as an assumption. The
  -- `Inputs` value is not otherwise constrained.
  Assumptions _ := numBits ≤ K ∧ 2 ^ K * 2 ^ K < PALLAS_BASE_CARD

  -- the positional element cell (the output), as extraction data
  Witness := field
  extract cfg offset _ self env :=
    eval env (AssignedCell.of self offset cfg.runningSum : Var field Fp)

  Spec := fun _ (out : Fp) _ => out.val < 2 ^ numBits

  -- honest-prover precondition: the witnessed element really is a `num_bits` word (Rust's
  -- caller guarantees this — `witness_short_check` is only sound *and* complete on such
  -- elements). Stated on the extraction data (the positional cell's value).
  ProverAssumptions _ wit _ := wit.val < 2 ^ numBits

  ProverSpec _ output wit _ := output = wit

  soundness := by
    circuit_proof_start [rangeCheckLookup, bitshiftGate, invTwoPowS]
    obtain ⟨⟨_hUsable, hTableLt, _hTableEq⟩, hDistinct⟩ := _hE
    obtain ⟨hNumBits, hCard⟩ := hA
    -- the short-row valuation: `q_running ∉ [q_lookup]` (distinct indices), so the gated
    -- input reduces to `z_cur` at both rows
    rw [if_neg (fun h => hDistinct h.symm)] at hc
    -- destructure: two memberships (the element cell IS the output — positional), the
    -- `invTwoPowS` constant, the bitshift gate
    obtain ⟨hMemWord, hMemShift, hInvConst, hGate⟩ := hc
    simp only [List.cons.injEq, and_true, one_mul, zero_mul, sub_zero,
      zero_add] at hMemWord hMemShift
    have hWordLt : output.val < 2 ^ K :=
      mem_usableRows_val_lt hTableLt hMemWord
    have hShiftLt :
        (env.advice cfg.runningSum ↑(place self + (offset + 1))).val < 2 ^ K :=
      mem_usableRows_val_lt hTableLt hMemShift
    set shifted := env.advice cfg.runningSum ↑(place self + (offset + 1))
      with hshift_def
    let word : Fp := output
    have hword : word = output := rfl
    have hPowLtCard : 2 ^ numBits < PALLAS_BASE_CARD :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hNumBits)
        (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (pow_two_pos K)) hCard)
    have hPowNe : (2 ^ numBits : Fp) ≠ 0 := by
      intro hzero
      have hzero' : ((2 ^ numBits : ℕ) : Fp) = 0 := by simpa using hzero
      have hdiv := (ZMod.natCast_eq_zero_iff (2 ^ numBits) PALLAS_BASE_CARD).mp hzero'
      exact (Nat.not_dvd_of_pos_of_lt (pow_two_pos _) hPowLtCard) hdiv
    have hEqShift : shifted = word * (2 ^ (K - numBits) : Fp) := by
      -- the gate poly `word · 2^K · invTwoPowS − shifted = 0` with the constant landed
      rw [hInvConst] at hGate
      have hb : shifted = word * (2 ^ K : Fp) * ((2 ^ numBits : Fp))⁻¹ := by
        rw [← sub_eq_zero]; linear_combination -hGate
      rw [hb]
      have hPowSplitFp : (2 ^ K : Fp) = (2 ^ (K - numBits) : Fp) * (2 ^ numBits : Fp) := by
        rw [← pow_add]; congr 1; omega
      rw [hPowSplitFp]; field_simp
    exact shortRange_soundness_aux K numBits hNumBits hCard word shifted
      hWordLt hShiftLt hEqShift

  completeness := by
    circuit_proof_start [rangeCheckLookup, bitshiftGate, invTwoPowS]
    obtain ⟨⟨hUsable, _hTableLt, hTableEq⟩, hDistinct⟩ := _hE
    obtain ⟨hNumBits, hCard⟩ := hA
    simp only [Placed.toEnvironment_env] at hTableEq hUsable
    -- `q_running` OFF (distinct selectors): the gated rows read `z_cur` (the plain element)
    rw [if_neg (fun h => hDistinct h.symm)]
    -- the caller-assigned element's `.val` bound, off the honest-prover assumption on the
    -- extraction data (the positional cell's verifier-view value = the advice read)
    have hEltLt : (env.advice cfg.runningSum
        ((place self + offset : ℕ) : ℤ)).val < 2 ^ numBits := hPA
    have hOut : env.advice cfg.runningSum ((place self + offset : ℕ) : ℤ)
        = output := h_output
    set elt := env.advice cfg.runningSum ((place self + offset : ℕ) : ℤ)
      with helt_def
    have hEltLtK : elt.val < 2 ^ K :=
      lt_of_lt_of_le hEltLt (Nat.pow_le_pow_right (by norm_num) hNumBits)
    have hCardK : 2 ^ K < PALLAS_BASE_CARD :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (pow_two_pos K)) hCard
    have hE_cast : ((elt.val : ℕ) : Fp) = elt := ZMod.natCast_zmod_val _
    have hShiftedLtK : (elt * (2 ^ (K - numBits) : Fp)).val < 2 ^ K :=
      shortRange_completeness_shifted K numBits hNumBits hCardK elt hEltLt
    have hShift_cast :
        (((elt * (2 ^ (K - numBits) : Fp)).val : ℕ) : Fp)
          = elt * (2 ^ (K - numBits) : Fp) :=
      ZMod.natCast_zmod_val _
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- membership @offset: witness row `elt.val`
      refine ⟨elt.val, lt_of_lt_of_le hEltLtK hUsable, ?_⟩
      simp only [one_mul, zero_mul, sub_zero, zero_add, List.cons.injEq, and_true]
      rw [hTableEq elt.val hEltLtK]
      exact hE_cast.symm
    · -- membership @(offset+1): witness row `shifted.val`
      refine ⟨(elt * (2 ^ (K - numBits) : Fp)).val,
        lt_of_lt_of_le hShiftedLtK hUsable, ?_⟩
      simp only [one_mul, zero_mul, sub_zero, zero_add, List.cons.injEq, and_true]
      rw [hTableEq _ hShiftedLtK]
      exact hShift_cast.symm
    · -- bitshift gate
      have hPowLtCard : 2 ^ numBits < PALLAS_BASE_CARD :=
        lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hNumBits) hCardK
      have hPowNe : (2 ^ numBits : Fp) ≠ 0 := by
        intro hzero
        have hzero' : ((2 ^ numBits : ℕ) : Fp) = 0 := by simpa using hzero
        have hdiv := (ZMod.natCast_eq_zero_iff (2 ^ numBits) PALLAS_BASE_CARD).mp hzero'
        exact (Nat.not_dvd_of_pos_of_lt (pow_two_pos _) hPowLtCard) hdiv
      have hPowSplitFp : (2 ^ K : Fp) = (2 ^ (K - numBits) : Fp) * (2 ^ numBits : Fp) := by
        rw [← pow_add]; congr 1; omega
      rw [hPowSplitFp]; field_simp; ring
    · -- the honest-prover contract: the output IS the extraction cell
      exact hOut.symm

@[synthesis_summary_norm]
theorem shortRangeCheck_synthesisSummary_eq
    (K numBits : ℕ) (cfg : Config K) (offset : ℕ) (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        (((shortRangeCheck K numBits).synthesize cfg offset ()).operations region) =
      shortRangeCheckSynthesisSummary cfg offset :=
  (shortRangeCheck K numBits).elaborated.synthesisSummary_eq cfg offset () region |>.symm

@[synthesis_summary_norm]
theorem shortRangeCheck_elaborated_synthesisSummary_eq
    (K numBits : ℕ) (cfg : Config K) (offset : ℕ) (region : RegionIndex) :
    (shortRangeCheck K numBits).elaborated.synthesisSummary cfg offset () region =
      shortRangeCheckSynthesisSummary cfg offset := rfl

/-- A short range check requests one deferred constant cell for the inverse
power-of-two value. -/
@[synthesis_summary_norm]
theorem shortRangeCheck_synthesisSummary_constantSiteCount
    (K numBits : ℕ) (config : Config K) (offset : ℕ)
    (region : RegionIndex) :
    ((shortRangeCheck K numBits).elaborated.synthesisSummary
      config offset () region).constantSiteCount = 1 := by
  rw [ElaboratedRegionCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [shortRangeCheck, circuit_norm]

/-- The short range check registers exactly its running-sum column for equality. -/
@[keygen_norm]
theorem shortRangeCheck_configured_permutationColumns_eq
    (K numBits : ℕ) {cfg : Config K}
    (configured : (shortRangeCheck K numBits).Configured cfg) :
    configured.permutationColumns = [cfg.runningSum.toAny] := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [keygen_norm, FormalRegionCircuit.Configured.permutationColumns,
    FormalRegionCircuit.keygenRequirements, ElaboratedRegionCircuit.keygenRequirements,
    shortRangeCheck, List.singleton_append]

/-! ## The pure telescoping algebra for `range_check`

Lifted `K`-generically from the phase-one donor `Clean/Orchard/Utilities.lean`,
`LookupRangeCheck.CopyCheck.{chain_telescope, element_lt}` (there `K` is fixed at `10`; here
it is a parameter). Zero framework vocabulary — a running-sum chain `f : ℕ → Fp` with each
step a `K`-bit word telescopes to `f 0 = lo + 2^{K·k}·f k` with `lo < 2^{K·k}`. -/

/-- Telescoping a `K`-bit running-sum chain (donor `CopyCheck.chain_telescope`, `K`-generic):
`f 0` splits into `K·k` low bits and `2^{K·k}·f k`. -/
theorem chain_telescope (K : ℕ) (f : ℕ → Fp) :
    ∀ k : ℕ,
    (∀ i, i < k → ∃ w : ℕ, w < 2 ^ K ∧ f i = 2 ^ K * f (i + 1) + (w : Fp)) →
    ∃ lo : ℕ, lo < 2 ^ (K * k) ∧ f 0 = (lo : Fp) + 2 ^ (K * k) * f k
  | 0, _ => ⟨0, by norm_num, by norm_num⟩
  | k + 1, h => by
    obtain ⟨lo, hlt, heq⟩ := chain_telescope K f k fun i hi => h i (by omega)
    obtain ⟨w, hw, hstep⟩ := h k (by omega)
    refine ⟨lo + w * 2 ^ (K * k), ?_, ?_⟩
    · have hsplit : (2 : ℕ) ^ (K * (k + 1)) = 2 ^ K * 2 ^ (K * k) := by
        rw [← pow_add]; ring_nf
      have hbound : lo + w * 2 ^ (K * k) < (w + 1) * 2 ^ (K * k) := by
        have := Nat.two_pow_pos (K * k); nlinarith
      have : (w + 1) * 2 ^ (K * k) ≤ 2 ^ K * 2 ^ (K * k) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [heq, hstep]
      push_cast
      rw [show K * (k + 1) = K * k + K from by ring, pow_add]
      ring

/-- A fully-decomposed chain (`f numWords = 0`) bounds `f 0` below `2^{K·numWords}`
(donor `CopyCheck.element_lt`, `K`-generic). The card bound `2^{K·numWords} ≤ |Fp|` reads
the low part off the field element. -/
theorem chain_element_lt (K numWords : ℕ) (hCard : 2 ^ (K * numWords) ≤ PALLAS_BASE_CARD)
    (f : ℕ → Fp)
    (hchain : ∀ i, i < numWords → ∃ w : ℕ, w < 2 ^ K ∧ f i = 2 ^ K * f (i + 1) + (w : Fp))
    (htop : f numWords = 0) :
    (f 0).val < 2 ^ (K * numWords) := by
  obtain ⟨lo, hlo, htel⟩ := chain_telescope K f numWords hchain
  rw [htop, mul_zero, _root_.add_zero] at htel
  rw [htel, ZMod.val_natCast_of_lt (lt_of_lt_of_le hlo hCard)]
  exact hlo

/-- The honest running word `z_idx − 2^K·z_{idx+1}` with `z_idx = ↑(b)`,
`z_{idx+1} = ↑(b / 2^K)` is the low `K`-bit chunk of `b`, hence `< 2^K`.
Donor `CopyCheck.word_val_lt`, `K`-generic (needs `2^K ≤ |Fp|`). -/
theorem honest_word_val_lt (K : ℕ) (hCard : 2 ^ K ≤ PALLAS_BASE_CARD) (b : ℕ) :
    ZMod.val ((b : Fp) - 2 ^ K * ((b / 2 ^ K : ℕ) : Fp)) < 2 ^ K := by
  have hsub : (b : Fp) - 2 ^ K * ((b / 2 ^ K : ℕ) : Fp) = ((b % 2 ^ K : ℕ) : Fp) := by
    have h := congrArg (Nat.cast (R := Fp)) (Nat.mod_add_div b (2 ^ K))
    push_cast at h; linear_combination -h
  rw [hsub, ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (pow_two_pos K)) hCard)]
  exact Nat.mod_lt _ (pow_two_pos K)

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD) in
/-- A fully-decomposed chain pins each running sum to the exact shift of the element:
`(f k).val = (f 0).val / 2^(K·k)` (donor `CopyCheck.read`, chain-language). -/
theorem chain_read (K numWords : ℕ) (hpow : K * numWords ≤ 254) (f : ℕ → Fp)
    (hchain : ∀ i, i < numWords → ∃ w : ℕ, w < 2 ^ K ∧ f i = 2 ^ K * f (i + 1) + (w : Fp))
    (htop : f numWords = 0) (k : ℕ) (hk : k ≤ numWords) :
    (f k).val = (f 0).val / 2 ^ (K * k) := by
  have hcard : ∀ m : ℕ, m ≤ 254 → (2 : ℕ) ^ m < PALLAS_BASE_CARD := fun m hm =>
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hm) (by norm_num [PALLAS_BASE_CARD])
  have hsubpow : K * (numWords - k) ≤ 254 :=
    le_trans (Nat.mul_le_mul_left K (Nat.sub_le numWords k)) hpow
  obtain ⟨lok, hlok, htelk⟩ := chain_telescope K f k fun i hi => hchain i (by omega)
  obtain ⟨lo', hlo', hzk⟩ := chain_telescope K (fun i => f (k + i)) (numWords - k)
    fun i hi => by
      obtain ⟨w, hw, hstep⟩ := hchain (k + i) (by omega)
      exact ⟨w, hw, by
        show f (k + i) = 2 ^ K * f (k + (i + 1)) + (w : Fp)
        rw [show k + (i + 1) = k + i + 1 from by omega]; exact hstep⟩
  simp only [show k + (numWords - k) = numWords from by omega, htop, mul_zero,
    _root_.add_zero] at hzk
  have hsum_lt : lok + 2 ^ (K * k) * lo' < 2 ^ (K * numWords) := by
    have hab : 2 ^ (K * k) * 2 ^ (K * (numWords - k)) = 2 ^ (K * numWords) := by
      rw [← pow_add]; congr 1; rw [← Nat.mul_add]; congr 1; omega
    calc lok + 2 ^ (K * k) * lo'
        < 2 ^ (K * k) + 2 ^ (K * k) * lo' := by omega
      _ = 2 ^ (K * k) * (lo' + 1) := by ring
      _ ≤ 2 ^ (K * k) * 2 ^ (K * (numWords - k)) := by gcongr; omega
      _ = 2 ^ (K * numWords) := hab
  have hzkval : (f k).val = lo' := by
    rw [hzk]; exact ZMod.val_natCast_of_lt (lt_trans hlo' (hcard _ hsubpow))
  have helem : f 0 = (((lok + 2 ^ (K * k) * lo' : ℕ)) : Fp) := by
    rw [htelk, hzk]; push_cast; ring
  have helemval : (f 0).val = lok + 2 ^ (K * k) * lo' := by
    rw [helem]; exact ZMod.val_natCast_of_lt (lt_trans hsum_lt (hcard _ hpow))
  rw [hzkval, helemval, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ (K * k)),
    Nat.div_eq_of_lt hlok, Nat.zero_add]

/-! ## `range_check` — the running-sum decomposition gadget (the loop)

Rust `LookupRangeCheckConfig::range_check` (`lookup_range_check.rs:171-241`), reached via
`copy_check`/`witness_check` (lines 124-162). Given `element` (already assigned at
`running_sum` offset 0), decompose it into `numWords` `K`-bit words by a running sum:

  `z_0 = element`,  `z_{i+1} = (z_i − a_i)/2^K`,  word `a_i = z_i − 2^K·z_{i+1}`,

enabling BOTH `q_lookup` and `q_running` at each word row `i` (`lookup_range_check.rs:213-215`),
so the lookup input reduces to the running word `a_i` (`lookup-design.md` §1.4), forcing
`a_i ∈ [0, 2^K)`. With `strict = true` the final `z_{numWords}` is constrained to `0`
(`lines 235-238`), so `element < 2^{K·numWords}`; with `strict = false` (what the Orchard
action circuit uses at both call sites — `ecc/chip/mul/overflow.rs:200`,
`mul_fixed/base_field_elem.rs:278`) the tail is unconstrained and carries the high bits.

**This is the first gadget with a LOOP in `synthesize`.** The loop is a structurally
recursive `RegionCircuit` def over `numWords` whose `operations` is, by `rfl` (from the
monad's append-bind, `Lemmas.lean`), the concatenation of per-round op lists:
`(loop (n+1)).operations self = (loop n).operations self ++ (round n).operations self`.
That append shape is what lets the z-chain invariant be proven by induction over rounds
(`rangeCheck_loop_word_bounds` below), and the telescoping algebra (lifted `K`-generically
from the donor `Clean/Orchard/Utilities.lean`, `CopyCheck.chain_telescope`) then reads the
decomposition off the chain. -/

/-- The output of `range_check`: the first (`z_0 = element`) and last (`z_{numWords}`)
running sums, as assigned cells. Rust returns the whole `RunningSum<F>` vector; the two
callers use only `zs.last()` (the high tail) — plus `z_0` here to state `z_0 = element`. -/
structure Output (F : Type) where
  z0 : F
  zLast : F
deriving ProvableStruct

/-- The honest running-sum witness value at word `idx`: `z_idx = element ≫ (K·idx)`
(donor `CopyCheck.main`). As a witgen program over the `element` cell: cast to ℕ (`.val`),
shift right by `K·idx` bits (`.div` by `2^(K·idx)`), cast back to the field (`.ofNat`). -/
def zWitness (K idx : ℕ) (element : AssignedCell Fp) : WitgenIR Fp 1 :=
  .ofFExpr (.ofNat (.div (.val (.expr element)) (.const (2 ^ (K * idx)))))

/-- One round of the running sum (Rust loop body, `lookup_range_check.rs:211-233`), at
word `idx` inside the ambient region starting at base row `row` (`= offset + idx`): enable
`q_lookup` AND `q_running` at `row` — so the lookup input is the running word
`z_idx − 2^K·z_{idx+1}` — and assign `z_{idx+1}` at `row + 1`.

Cells are addressed by their absolute row, not threaded through the monad, so round `idx` is
independent of the others — exactly the forEach shape `RegionCircuit.forRange'` captures. -/
def rangeCheckRound (K : ℕ) (cfg : Config K) (element : AssignedCell Fp) (idx row : ℕ) :
    RegionCircuit Fp Unit := do
  -- running-sum row: both q_lookup and q_running on (§1.4 → input = running word a_idx)
  (rangeCheckLookup K cfg).enable [cfg.qRunning] row
  -- assign z_{idx+1} = element ≫ (K·(idx+1)) at row + 1
  let _z ← assignAdvice cfg.runningSum (row + 1) (zWitness K (idx + 1) element)
  return ()

theorem rangeCheckRound_synthesisSummary (K : ℕ) (cfg : Config K)
    (element : AssignedCell Fp) (idx row : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((rangeCheckRound K cfg element idx row).operations self) =
      .ofColumns
        [.selector cfg.qLookup.index, .selector cfg.qRunning.index,
          .column .advice cfg.runningSum.index]
        (row + 2) 0 := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
    simp only [rangeCheckRound, circuit_norm, List.flatMap_cons,
      List.flatMap_nil, FloorPlanner.regionOperationShapeColumns,
      List.map_cons, List.map_nil, List.singleton_append, List.append_nil,
      FloorPlanner.RegionSynthesisSummary.ofColumns_columns]
  · simp only [rangeCheckRound, circuit_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
    omega
  · simp only [rangeCheckRound, circuit_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]

/-- The running-sum loop: `numWords` independent rounds via `RegionCircuit.forRange'` (stride 1,
round `idx` at base row `offset + idx`). Its `RegionOperations.Constraints` / `ExtendsWitnesses`
split, under `circuit_norm`, into `∀ i : Fin numWords, <round i's predicate>` (the framework
`forRange'_constraints` / `forRange'_extendsWitnesses`), replacing the hand-written
`rangeCheckLoop_operations_succ` recursion the loop lemmas used to induct over. -/
def rangeCheckLoop (K : ℕ) (cfg : Config K) (element : AssignedCell Fp) (offset numWords : ℕ) :
    RegionCircuit Fp Unit :=
  RegionCircuit.forRange' offset 1 numWords (fun idx row => rangeCheckRound K cfg element idx row)

/-- Reduced synthesis footprint of the running-sum loop. -/
def rangeCheckLoopSummary (K : ℕ) (cfg : Config K) (offset numWords : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    (if numWords = 0 then [] else
      [.selector cfg.qLookup.index, .selector cfg.qRunning.index,
        .column .advice cfg.runningSum.index])
    (if numWords = 0 then 0 else offset + numWords + 1)
    0

@[synthesis_summary_norm]
theorem rangeCheckLoop_synthesisSummary (K : ℕ) (cfg : Config K)
    (element : AssignedCell Fp) (offset numWords : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((rangeCheckLoop K cfg element offset numWords).operations self) =
      rangeCheckLoopSummary K cfg offset numWords := by
  induction numWords with
  | zero =>
      apply FloorPlanner.RegionSynthesisSummary.ext
      · simp [rangeCheckLoop, RegionCircuit.forRange', RegionCircuit.loopAux,
          RegionCircuit.operations_pure, rangeCheckLoopSummary,
          FloorPlanner.regionSynthesisSummary_nil_columns,
          FloorPlanner.RegionSynthesisSummary.ofColumns_columns,
          FloorPlanner.unionColumns]
      · simp [rangeCheckLoop, RegionCircuit.forRange', RegionCircuit.loopAux,
          RegionCircuit.operations_pure, rangeCheckLoopSummary,
          FloorPlanner.regionSynthesisSummary_nil_rowCount,
          FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
      · simp [rangeCheckLoop, RegionCircuit.forRange', RegionCircuit.loopAux,
          RegionCircuit.operations_pure, rangeCheckLoopSummary,
          FloorPlanner.regionSynthesisSummary_nil_constantSiteCount,
          FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]
  | succ n inductionHypothesis =>
      rw [rangeCheckLoop, RegionCircuit.forRange',
        RegionCircuit.loopAux_operations_succ,
        FloorPlanner.regionSynthesisSummary_append]
      rw [show RegionCircuit.loopAux (fun i => offset + i * 1)
          (fun idx row => rangeCheckRound K cfg element idx row) n =
          rangeCheckLoop K cfg element offset n from rfl,
        inductionHypothesis]
      rw [rangeCheckRound_synthesisSummary]
      apply FloorPlanner.RegionSynthesisSummary.ext
      · simp only [FloorPlanner.RegionSynthesisSummary.combine_columns,
          FloorPlanner.RegionSynthesisSummary.ofColumns_columns]
        by_cases hn : n = 0
        · subst n
          simp only [rangeCheckLoopSummary, ↓reduceIte, Nat.succ_ne_zero,
            FloorPlanner.RegionSynthesisSummary.ofColumns_columns]
          exact FloorPlanner.unionColumns_normalized_nil_left _
        · simp only [rangeCheckLoopSummary, if_neg hn, Nat.succ_ne_zero,
            FloorPlanner.RegionSynthesisSummary.ofColumns_columns,
            if_false]
          exact FloorPlanner.unionColumns_self _
      · by_cases hn : n = 0
        · subst n
          simp [rangeCheckLoopSummary,
            FloorPlanner.RegionSynthesisSummary.combine_rowCount,
            FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
        · simp [rangeCheckLoopSummary, hn,
            FloorPlanner.RegionSynthesisSummary.combine_rowCount,
            FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
          omega
      · simp [rangeCheckLoopSummary,
          FloorPlanner.RegionSynthesisSummary.combine_constantSiteCount,
          FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]

/-- The running sum read off the environment: `z_j = env.advice runningSum` at absolute
row `place self + (offset + j)`. The chain the telescoping algebra runs over. -/
def zChain (K : ℕ) (cfg : Config K) (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment Fp) (offset : ℕ) (j : ℕ) : Fp :=
  env.advice cfg.runningSum ((place self + (offset + j) : ℕ) : ℤ)

/-- **The round-invariant / z-chain lemma (soundness).** If the loop's constraints hold and the
table is loaded, then every word `z_i − 2^K·z_{i+1}` (`i < numWords`) is a `K`-bit value — the
hypothesis `chain_telescope`/`chain_element_lt` consume.

No loop-structure induction: the framework `forRange'_constraints` split (via `circuit_norm`)
turns the loop's `Constraints` straight into `∀ i : Fin numWords, <round i's constraints>`, and
each round's membership existential (both `q_lookup`, `q_running` on) delivers a usable table row
holding the word; `TableLoaded`'s usable-rows bound makes it `< 2^K`. -/
theorem rangeCheck_loop_word_bounds (K : ℕ) (cfg : Config K) (element : AssignedCell Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset : ℕ)
    (hTableLt : ∀ r : ℕ, r < env.usableRows → (env.fixed cfg.tableIdx.inner (r : ℤ)).val < 2 ^ K)
    (numWords : ℕ)
    (hLoop : ∀ i : Fin numWords, RegionOperations.Constraints place self env
      ((rangeCheckRound K cfg element i (offset + i * 1)).operations self)) :
    ∀ i, i < numWords → ∃ w : ℕ, w < 2 ^ K ∧
      zChain K cfg place self env offset i
        = 2 ^ K * zChain K cfg place self env offset (i + 1) + (w : Fp) := by
  -- per-round normalization under the pipeline's canonical ∀-chunk
  simp only [rangeCheckRound, circuit_norm, rangeCheckLookup, mul_one,
    List.map_cons, List.map_nil, List.cons.injEq, and_true, one_mul, zero_mul, add_zero,
    sub_self] at hLoop
  intro i hi
  -- round `i`: its membership existential (running word `z_i − 2^K·z_{i+1}`)
  obtain ⟨rW, hrWlt, hrW⟩ := hLoop ⟨i, hi⟩
  refine ⟨(env.fixed cfg.tableIdx.inner (rW : ℤ)).val, hTableLt rW hrWlt, ?_⟩
  rw [ZMod.natCast_zmod_val]
  simp only [zChain]
  rw [show offset + (i + 1) = offset + i + 1 from by omega]
  linear_combination hrW

/-- **Completeness z-value lemma.** The honest prover's `ExtendsWitnesses` of the loop pins each
interior running sum to the canonical shift `z_j = ↑(element.val ≫ (K·j))` for `1 ≤ j ≤ numWords`
(`zWitness` = that shift). The `j = 0` sum is `element`, pinned by the copy outside the loop.

The framework `forRange'_extendsWitnesses` split turns the loop's `ExtendsWitnesses` into
`∀ i : Fin numWords, <round i's witness>`; round `j-1`'s own `assignAdvice` pins `z_j`. -/
theorem rangeCheck_loop_zvalues (K : ℕ) (cfg : Config K) (element : AssignedCell Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset : ℕ)
    (numWords : ℕ)
    (hLoop : ∀ i : Fin numWords, RegionOperations.ExtendsWitnesses place self env
      ((rangeCheckRound K cfg element i (offset + i * 1)).operations self)) :
    ∀ j, 1 ≤ j → j ≤ numWords →
      zChain K cfg place self env.toEnvironment offset j
        = ((element.eval place env.toEnvironment).val / 2 ^ (K * j) : ℕ) := by
  simp only [rangeCheckRound, circuit_norm, zWitness, mul_one] at hLoop
  intro j hj1 hj2
  -- round `j-1`'s `assignAdvice` pins `z_j` at row `offset + (j-1) + 1`
  have hRound := hLoop ⟨j - 1, by omega⟩
  simp only [zChain]
  rw [show offset + j = offset + (j - 1) + 1 from by omega,
    show K * j = K * (j - 1 + 1) from by rw [Nat.sub_add_cancel hj1]]
  convert hRound using 2

/-- **Completeness loop-constraints lemma.** Given the honest running-sum values
`z_j = ↑(a ≫ (K·j))` (`hz`, for `a := element.val`) and the loaded table (block contents
`hTableEq`, domain bound `hUsable`), the loop's `Constraints` hold: the membership at each round
`i` is witnessed by the honest word `a_i`'s value (`< 2^K ≤ usableRows`, holding `↑a_i = a_i`).

The framework `forRange'_constraints` split reduces the goal to `∀ i : Fin numWords, <round i's
membership>`; each round is discharged from `hz i`/`hz (i+1)`. -/
theorem rangeCheck_loop_constraints_complete (K : ℕ) (cfg : Config K) (element : AssignedCell Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset : ℕ) (a : ℕ)
    (hKcard : 2 ^ K ≤ PALLAS_BASE_CARD)
    (hUsable : 2 ^ K ≤ env.usableRows)
    (hTableEq : ∀ r : ℕ, r < 2 ^ K → env.fixed cfg.tableIdx.inner (r : ℤ) = (r : Fp))
    (numWords : ℕ)
    (hz : ∀ j, j ≤ numWords → zChain K cfg place self env offset j = ((a / 2 ^ (K * j) : ℕ) : Fp)) :
    ∀ i : Fin numWords, RegionOperations.Constraints place self env
      ((rangeCheckRound K cfg element i (offset + i * 1)).operations self) := by
  simp only [rangeCheckRound, circuit_norm, rangeCheckLookup, mul_one,
    List.map_cons, List.map_nil, List.cons.injEq, and_true, one_mul, zero_mul, add_zero, sub_self]
  intro i
  obtain ⟨n, hi⟩ := i
  -- round `n` uses `hz n` and `hz (n+1)` (both ≤ numWords since `n < numWords`)
  · have hzn := hz n (by omega)
    have hzn1 := hz (n + 1) (by omega)
    -- The gate now builds `z_next * 2^K` (field scalar on the RIGHT, `.scaled` — VK-faithful),
    -- so the membership word is `z_cur − z_next · 2^K` (the `2^K` on the right of `z_{n+1}`).
    -- the honest word, rewritten to `↑b − ↑(b/2^K)·2^K` with `b = a ≫ (K·n)`
    have hword : zChain K cfg place self env offset n
          - zChain K cfg place self env offset (n + 1) * 2 ^ K
        = ((a / 2 ^ (K * n) : ℕ) : Fp) - (((a / 2 ^ (K * n) / 2 ^ K : ℕ)) : Fp) * 2 ^ K := by
      rw [hzn, hzn1]
      congr 2
      rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
    have hwordval :
        (zChain K cfg place self env offset n
          - zChain K cfg place self env offset (n + 1) * 2 ^ K).val < 2 ^ K := by
      rw [hword, mul_comm (((a / 2 ^ (K * n) / 2 ^ K : ℕ)) : Fp) ((2 : Fp) ^ K)]
      exact honest_word_val_lt K hKcard (a / 2 ^ (K * n))
    refine ⟨(zChain K cfg place self env offset n
        - zChain K cfg place self env offset (n + 1) * 2 ^ K).val,
      lt_of_lt_of_le hwordval hUsable, ?_⟩
    -- the running word equals the table cell at row `word.val`
    rw [hTableEq _ hwordval, ZMod.natCast_zmod_val]
    simp only [zChain, show offset + n + 1 = offset + (n + 1) from by omega]

-- `cellAt` (naming a cell at a fixed row) now lives in the framework (`Basic.lean`).

/-- Exact reduced footprint of a copied-in word-wise range check. -/
def rangeCheckSynthesisSummary (K numWords : ℕ) (strict : Bool)
    (cfg : Config K) (offset : ℕ) : FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    ([.column .advice cfg.runningSum.index] ++
      if numWords = 0 then [] else
        [.selector cfg.qLookup.index, .selector cfg.qRunning.index,
          .column .advice cfg.runningSum.index])
    (offset + numWords + 1) (if strict then 1 else 0)

/-- The `range_check` gadget (`lookup_range_check.rs:171-241`), region-level, parameterized
by `numWords` and `strict`. Copies `element` into `running_sum` at `offset` (`z_0`), runs the
`numWords`-round running-sum loop, and — when `strict` — constrains the final `z_{numWords}`
to `0` (`lines 235-238`).

`strict = false` (the Orchard action-circuit variant): `Spec` is the telescoping
decomposition `element = lo + 2^{K·numWords}·z_last`, `lo < 2^{K·numWords}` — the only fact
soundly available (the tail is unconstrained). `strict = true`: additionally
`element.val < 2^{K·numWords}` (`z_last = 0`). -/
def rangeCheck (K numWords : ℕ) (strict : Bool) :
    FormalRegionCircuit Fp (Config K) (Config K) Inputs Output where
  configure := fun cfg => pure cfg

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    -- copy `element` into `running_sum` at `offset` as `z_0` (Rust `copy_check`/`witness_check`)
    let _z0 ← copyAdvice input.element cfg.runningSum offset
    -- the running-sum loop: `numWords` rounds
    rangeCheckLoop K cfg input.element offset numWords
    let zLast ← cellAt cfg.runningSum (offset + numWords)
    -- strict mode: constrain the final running sum to 0
    if strict then constrainConstant zLast (0 : Fp)
    let z0 ← cellAt cfg.runningSum offset
    return { z0, zLast }

  elaborated :=
    { keygenRequirements :=
        { lookups cfg _ := [rangeCheckLookup K cfg]
          permutationColumns cfg _ := [cfg.runningSum]
          inputPermutationColumns _ _ input := [input.element.cell.column] }
      synthesisSummary cfg offset _ _ :=
        rangeCheckSynthesisSummary K numWords strict cfg offset
      synthesisSummary_eq := by
        intro cfg offset input self
        apply FloorPlanner.RegionSynthesisSummary.ext
        all_goals
          simp only [circuit_norm, synthesis_summary_norm]
          by_cases hn : numWords = 0 <;> cases strict <;>
            simp [rangeCheckSynthesisSummary, rangeCheckLoopSummary, hn, circuit_norm,
              synthesis_summary_norm]
      registered := by keygen_registration }

  -- Same env-level preconditions as `shortRangeCheck`: the table is loaded (`TableLoaded`),
  -- and `q_lookup`/`q_running` are distinct selectors (they are allocated separately in
  -- `configure`). The running-sum rows here have BOTH selectors on, so the distinctness is
  -- not consumed by the word-bound induction; it is kept for uniformity with the two-variant
  -- lookup semantics (a short-row consumer would need it).
  EnvAssumptions cfg env :=
    TableLoaded K cfg env.env ∧ cfg.qLookup.index ≠ cfg.qRunning.index
  -- Field-capacity bound: `num_words · K` must fit the field (Rust `assert!`,
  -- `lookup_range_check.rs:179`). We carry `2^{K·numWords} ≤ |Fp|` (reads the low part of the
  -- decomposition off the field element) and the per-word `2^K ≤ |Fp|` (each `K`-bit lookup;
  -- for `numWords ≥ 1` the former implies it, but `numWords = 0` needs it separately).
  Assumptions _ := 2 ^ (K * numWords) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD

  Spec input output _ :=
    output.z0 = input.element ∧
    (∃ lo : ℕ, lo < 2 ^ (K * numWords) ∧
      input.element = (lo : Fp) + ((2 ^ (K * numWords) : ℕ) : Fp) * output.zLast) ∧
    -- strict: the final running sum is 0, so element fits in K·numWords bits
    (strict = true → output.zLast = 0 ∧ input.element.val < 2 ^ (K * numWords))

  -- honest-prover precondition: in `strict` mode the element genuinely fits in `K·numWords`
  -- bits (the assertion precondition — the honest prover can only satisfy `z_last = 0` then).
  -- Non-strict imposes nothing. Established assertion-gadget pattern (cf. donor `Decomposed`).
  ProverAssumptions input _ _ := strict = true → input.element.val < 2 ^ (K * numWords)

  -- honest-prover postcondition (C6): the high-tail cell `zLast` holds the honest NATURAL-NUMBER
  -- decomposition `↑(element.val / 2^{K·numWords})` — the shift-right of `element` past the
  -- decomposed low bits. This is the fact a decomposition consumer needs but the verifier `Spec`
  -- (a field equation) does not expose (e.g. `MulOverflow`, which concludes `zLast = 0` when the
  -- high half vanishes). It now flows through the engine's `h_spec_i` derived statement like any
  -- other contract field — replacing the retired boundary-leaking `rangeCheck_call_zLast_value`.
  ProverSpec input output _ _ :=
    output.zLast = ((input.element.val / 2 ^ (K * numWords) : ℕ) : Fp)

  soundness := by
    -- loop-based composite: `circuit_proof_start` runs the universal prefix (intro + `soundness_iff`
    -- + house names + constraints peel over the peel lemmas below); the loop's folded `Constraints`
    -- chunk keeps the state composite, so the leaf-only finish is skipped and `hc`/`h_input`/
    -- `h_output` survive for the word-bound induction that follows.
    -- empty unfold list: the cell-naming lemmas (`output_cellAt`/`operations_cellAt`) and the
    -- bind/append/copy composition lemmas are all `@[circuit_norm]` and fire from the set — nothing
    -- gadget-specific is needed to reach the loop's folded chunk (maintainer's blocks criterion).
    circuit_proof_start
    obtain ⟨hTable, _hDistinct⟩ := _hE
    obtain ⟨hUsable, hTableLt, _hTableEq⟩ := hTable
    obtain ⟨hCopy, hLoop, _hTailC⟩ := hc
    -- (`input`/`output` are already destructured to `input_element` / `output_z0` /
    -- `output_zLast` by the prefix's `provable_type_simp`)
    -- the running-sum chain read off the env; the word-bound induction over the loop chunk
    set f := zChain K cfg place self env offset with hf_def
    have hwords := rangeCheck_loop_word_bounds K cfg input_var_element place self env
      offset hTableLt numWords hLoop
    -- z_0 = element (copy)
    have hz0 : f 0 = input_element := by
      simp only [hf_def, zChain, add_zero]; rw [hCopy]
    -- the telescoping decomposition (soundly available regardless of `strict`)
    obtain ⟨lo, hlo, htel⟩ := chain_telescope K f numWords hwords
    -- resolve the output cells (case on `strict` to compute the tail ops)
    rcases hbstrict : strict with _ | _ <;>
      simp only [hbstrict, circuit_norm,
        Bool.false_eq_true, if_true, if_false] at _hTailC h_output ⊢ <;>
      obtain ⟨hOz0, hOzLast⟩ := h_output <;>
      -- output_z0 = advice runningSum offset = f 0 ; output_zLast = advice … = f numWords
      rw [show output_z0 = f 0 from by rw [← hOz0]; simp only [hf_def, zChain, add_zero],
          show output_zLast = f numWords from by rw [← hOzLast]; simp only [hf_def, zChain]]
    · -- strict = false: telescoped decomposition, strict conjunct already discharged by simp
      exact ⟨hz0, lo, hlo, by rw [← hz0]; push_cast; exact htel⟩
    · -- strict = true: the tail's `constrainConstant` gives f numWords = 0
      have hzLast0 : f numWords = 0 := by simp only [hf_def, zChain]; exact _hTailC
      refine ⟨hz0, ⟨lo, hlo, ?_⟩, hzLast0, ?_⟩
      · rw [← hz0]; push_cast; exact htel
      · rw [← hz0]; exact chain_element_lt K numWords hA.1 f hwords hzLast0

  completeness := by
    -- loop-based composite: the universal prefix peels the witness list over the peel lemmas below;
    -- the loop's folded `ExtendsWitnesses` chunk keeps the state composite, so the leaf-only finish
    -- is skipped and `hwit`/`h_input`/`hPA` survive for the manual continuation.
    -- empty unfold list: `operations_cellAt` and the bind/append/copy composition lemmas are all
    -- `@[circuit_norm]` and fire from the set (maintainer's blocks criterion — nothing
    -- gadget-specific reaches the loop's folded chunk).
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    obtain ⟨hUsable, _hTableLt, hTableEq⟩ := hTable
    simp only [Placed.toEnvironment_env] at hTableEq hUsable
    obtain ⟨hCopyWit, hLoopWit, hTailWit⟩ := hwit
    obtain ⟨hCardN, hKcard⟩ := hA
    -- the element cell value (`input_var_element`'s eval); by `h_input` it is `input_element`, and
    -- `input_element.val` is the decomposed nat `a`. The prefix's `provable_type_simp` already
    -- destructured `input_var` to `input_var_element`, so we work with the cell spelling directly.
    set eCell := env.get input_var_element.cell.column
      ↑(place input_var_element.cell.regionIndex + input_var_element.cell.rowOffset) with heCell
    have heInput : eCell = input_element := h_input
    -- z_0 = element cell (from the copy's assignAdvice witness)
    have hz0 : zChain K cfg place self env.toEnvironment offset 0 = eCell := by
      simp only [zChain, add_zero, heInput, hCopyWit]
    -- the honest z-chain up to numWords: `z_j = ↑(eCell.val ≫ (K·j))`
    have hz : ∀ j, j ≤ numWords → zChain K cfg place self env.toEnvironment offset j
        = ((eCell.val / 2 ^ (K * j) : ℕ) : Fp) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp only [Nat.mul_zero, pow_zero, Nat.div_one, hz0, ZMod.natCast_zmod_val]
      · exact rangeCheck_loop_zvalues K cfg input_var_element place self env offset
          numWords hLoopWit j hjpos hj
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- the loop's Constraints (membership at each round), via the completeness loop lemma
      exact rangeCheck_loop_constraints_complete K cfg input_var_element place self
        env.toEnvironment offset eCell.val hKcard hUsable hTableEq numWords hz
    · -- the tail: strict ⇒ `constrainConstant zLast 0` (⇒ z_last = 0); else nothing
      rcases hbstrict : strict with _ | _
      · -- strict = false: no tail constraint
        simp only [circuit_norm]
      · -- strict = true: prove `zLast = 0` from the honest value (element < 2^{K·numWords})
        simp only [circuit_norm]
        have hzn := hz numWords le_rfl
        simp only [zChain] at hzn
        have heInputLt : eCell.val < 2 ^ (K * numWords) := by
          rw [heInput]; exact hPA hbstrict
        rw [hzn, Nat.div_eq_of_lt heInputLt, Nat.cast_zero]
    · -- ProverSpec (C6): `output_zLast = ↑(input_element.val / 2^{K·numWords})`. The output `zLast`
      -- cell sits at `offset + numWords`, so its prover eval is the honest chain value `hz numWords`;
      -- `input_element.val = eCell.val` by `h_input`. Case on `strict` (the `if` blocks the
      -- `.output` reduction, but the output literal `{ z0, zLast }` is identical in both branches).
      have hzn := hz numWords le_rfl
      simp only [zChain] at hzn
      -- `input_element.val = eCell.val`; the honest `zLast` cell (`offset + numWords`) is `hzn`
      rw [← heInput, ← hzn]
      -- reduce `h_output` to its component equations (the `if` on `strict` blocks `.output`, but the
      -- output literal `{ z0, zLast }` is identical in both branches) and read off `output_zLast`
      cases strict <;>
        · simp only [circuit_norm, Bool.false_eq_true, if_false, if_true] at h_output
          exact h_output.2.symm

@[synthesis_summary_norm]
theorem rangeCheck_synthesisSummary_eq
    (K numWords : ℕ) (strict : Bool) (cfg : Config K) (offset : ℕ)
    (input : Var Inputs Fp) (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        (((rangeCheck K numWords strict).synthesize cfg offset input).operations region) =
      rangeCheckSynthesisSummary K numWords strict cfg offset :=
  (rangeCheck K numWords strict).elaborated.synthesisSummary_eq
    cfg offset input region |>.symm

@[synthesis_summary_norm]
theorem rangeCheck_elaborated_synthesisSummary_eq
    (K numWords : ℕ) (strict : Bool) (cfg : Config K) (offset : ℕ)
    (input : Var Inputs Fp) (region : RegionIndex) :
    (rangeCheck K numWords strict).elaborated.synthesisSummary
        cfg offset input region =
      rangeCheckSynthesisSummary K numWords strict cfg offset := rfl

/-- Exact reduced footprint of a positional word-wise range check. -/
def rangeCheckAtSynthesisSummary (K numWords : ℕ) (strict : Bool)
    (cfg : Config K) (offset : ℕ) : FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    (if numWords = 0 then [] else
      [.selector cfg.qLookup.index, .selector cfg.qRunning.index,
        .column .advice cfg.runningSum.index])
    (if numWords = 0 then 0 else offset + numWords + 1)
    (if strict then 1 else 0)

/-- Rust `witness_check`'s check body (`lookup_range_check.rs:142-162`), POSITIONAL: the
element "must have been assigned to `running_sum` at `offset`" by the caller (Rust
`witness_check` does the `assign_advice` itself; the Lean caller witnesses the cell and
composes this check — the `witnessShortCheck` pattern). Contracts mirror `rangeCheck`,
with the copied-in element replaced by the positional cell (the extraction data, following
`shortRangeCheck`). -/
def rangeCheckAt (K numWords : ℕ) (strict : Bool) :
    FormalRegionCircuit Fp (Config K) (Config K) unit Output where
  configure := fun cfg => pure cfg

  synthesize cfg offset _ := do
    -- the caller-assigned `element` at `offset` (`z_0`)
    let z0 ← cellAt cfg.runningSum offset
    -- the running-sum loop: `numWords` rounds
    rangeCheckLoop K cfg z0 offset numWords
    let zLast ← cellAt cfg.runningSum (offset + numWords)
    -- strict mode: constrain the final running sum to 0
    if strict then constrainConstant zLast (0 : Fp)
    return { z0, zLast }

  elaborated :=
    { keygenRequirements :=
        { lookups cfg _ := [rangeCheckLookup K cfg]
          permutationColumns cfg _ := [cfg.runningSum] }
      synthesisSummary cfg offset _ _ :=
        rangeCheckAtSynthesisSummary K numWords strict cfg offset
      synthesisSummary_eq := by
        intro cfg offset input self
        apply FloorPlanner.RegionSynthesisSummary.ext
        all_goals
          simp only [circuit_norm, synthesis_summary_norm]
          by_cases hn : numWords = 0 <;> cases strict <;>
            simp [rangeCheckAtSynthesisSummary, rangeCheckLoopSummary, hn, circuit_norm,
              synthesis_summary_norm]
      registered := by keygen_registration }

  EnvAssumptions cfg env :=
    TableLoaded K cfg env.env ∧ cfg.qLookup.index ≠ cfg.qRunning.index
  Assumptions _ := 2 ^ (K * numWords) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD

  -- the positional element cell (`z_0`), as extraction data
  Witness := field
  extract cfg offset _ self env :=
    eval env (AssignedCell.of self offset cfg.runningSum : Var field Fp)

  Spec _ output elt :=
    output.z0 = elt ∧
    (∃ lo : ℕ, lo < 2 ^ (K * numWords) ∧
      elt = (lo : Fp) + ((2 ^ (K * numWords) : ℕ) : Fp) * output.zLast) ∧
    (strict = true → output.zLast = 0 ∧ elt.val < 2 ^ (K * numWords))

  -- honest-prover precondition, on the extraction data (mirror of `rangeCheck`'s, which
  -- states it on the copied input)
  ProverAssumptions _ elt _ := strict = true → elt.val < 2 ^ (K * numWords)

  ProverSpec _ output elt _ :=
    output.z0 = elt ∧ output.zLast = ((elt.val / 2 ^ (K * numWords) : ℕ) : Fp)

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, _hDistinct⟩ := _hE
    obtain ⟨hUsable, hTableLt, _hTableEq⟩ := hTable
    obtain ⟨hLoop, _hTailC⟩ := hc
    set f := zChain K cfg place self env offset with hf_def
    have hwords := rangeCheck_loop_word_bounds K cfg
      (AssignedCell.of self offset cfg.runningSum) place self env
      offset hTableLt numWords hLoop
    obtain ⟨lo, hlo, htel⟩ := chain_telescope K f numWords hwords
    rcases hbstrict : strict with _ | _ <;>
      simp only [hbstrict, circuit_norm,
        Bool.false_eq_true, if_true, if_false] at _hTailC h_output ⊢ <;>
      obtain ⟨hOz0, hOzLast⟩ := h_output <;>
      rw [show output_z0 = f 0 from by rw [← hOz0]; simp only [hf_def, zChain, add_zero],
        show output_zLast = f numWords from by rw [← hOzLast]; simp only [hf_def, zChain],
        show env.advice cfg.runningSum ((place self + offset : ℕ) : ℤ) = f 0
          from by simp only [hf_def, zChain, add_zero]]
    · exact ⟨rfl, lo, hlo, by push_cast; exact htel⟩
    · have hzLast0 : f numWords = 0 := by simp only [hf_def, zChain]; exact _hTailC
      refine ⟨rfl, ⟨lo, hlo, ?_⟩, hzLast0, ?_⟩
      · push_cast; exact htel
      · exact chain_element_lt K numWords hA.1 f hwords hzLast0

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    obtain ⟨hUsable, _hTableLt, hTableEq⟩ := hTable
    simp only [Placed.toEnvironment_env] at hTableEq hUsable
    obtain ⟨hLoopWit, hTailWit⟩ := hwit
    obtain ⟨hCardN, hKcard⟩ := hA
    -- the positional element cell's value (`z_0`)
    set eCell := env.advice cfg.runningSum ((place self + offset : ℕ) : ℤ)
      with heCell
    have hz0 : zChain K cfg place self env.toEnvironment offset 0 = eCell := by
      simp only [zChain, add_zero, heCell]
    have hz : ∀ j, j ≤ numWords → zChain K cfg place self env.toEnvironment offset j
        = ((eCell.val / 2 ^ (K * j) : ℕ) : Fp) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp only [Nat.mul_zero, pow_zero, Nat.div_one, hz0, ZMod.natCast_zmod_val]
      · have hv := rangeCheck_loop_zvalues K cfg
          (AssignedCell.of self offset cfg.runningSum) place self env offset
          numWords hLoopWit j hjpos hj
        rw [hv]
        simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
          Cell.of_rowOffset, Cell.of_column, Environment.get_advice, heCell]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact rangeCheck_loop_constraints_complete K cfg
        (AssignedCell.of self offset cfg.runningSum) place self
        env.toEnvironment offset eCell.val hKcard hUsable hTableEq numWords hz
    · rcases hbstrict : strict with _ | _
      · simp only [circuit_norm]
      · simp only [circuit_norm]
        have hzn := hz numWords le_rfl
        simp only [zChain] at hzn
        have heInputLt : eCell.val < 2 ^ (K * numWords) := hPA hbstrict
        rw [hzn, Nat.div_eq_of_lt heInputLt, Nat.cast_zero]
    · -- ProverSpec, first conjunct: `output_z0` is the positional cell
      cases strict <;>
        · simp only [circuit_norm, Bool.false_eq_true, if_false, if_true] at h_output
          rw [heCell]
          exact h_output.1.symm
    · -- ProverSpec, C6: `output_zLast = ↑(elt.val / 2^{K·numWords})`
      have hzn := hz numWords le_rfl
      simp only [zChain] at hzn
      rw [← hzn]
      cases strict <;>
        · simp only [circuit_norm, Bool.false_eq_true, if_false, if_true] at h_output
          exact h_output.2.symm

@[synthesis_summary_norm]
theorem rangeCheckAt_synthesisSummary_eq
    (K numWords : ℕ) (strict : Bool) (cfg : Config K) (offset : ℕ)
    (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        (((rangeCheckAt K numWords strict).synthesize cfg offset ()).operations region) =
      rangeCheckAtSynthesisSummary K numWords strict cfg offset :=
  (rangeCheckAt K numWords strict).elaborated.synthesisSummary_eq
    cfg offset () region |>.symm

@[synthesis_summary_norm]
theorem rangeCheckAt_elaborated_synthesisSummary_eq
    (K numWords : ℕ) (strict : Bool) (cfg : Config K) (offset : ℕ)
    (region : RegionIndex) :
    (rangeCheckAt K numWords strict).elaborated.synthesisSummary
        cfg offset () region =
      rangeCheckAtSynthesisSummary K numWords strict cfg offset := rfl

/-- The decomposition output cells of the strict 25-word check: `z_0`, `z_1` (the `k_1`
cell in `y_canonicity`) and `z_13`. -/
structure DecomposedOutput (F : Type) where
  z0 : F
  z1 : F
  z13 : F
deriving ProvableStruct

/-- Exact reduced footprint of a strict positional check exposing interior words. -/
def rangeCheckAtDecomposedSynthesisSummary (numWords : ℕ)
    (cfg : Config 10) (offset : ℕ) : FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.qLookup.index, .selector cfg.qRunning.index,
      .column .advice cfg.runningSum.index]
    (offset + numWords + 1) 1

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD) in
/-- The positional strict 25-word running-sum check exposing `z_1`/`z_13` (donor
`CopyCheck.Decomposed`, positional): Rust `witness_check(j, 25, true)` as consumed by
`y_canonicity` (`note_commit.rs:1997-2010`), which hands out `zs[1]` and `zs[13]`. The
strict tail derives `elt < 2^250` and pins every running sum to the exact shift. -/
def rangeCheckAtDecomposed (numWords : ℕ) (h13 : 13 ≤ numWords)
    (hpow : 10 * numWords ≤ 254) :
    FormalRegionCircuit Fp (Config 10) (Config 10) unit DecomposedOutput where
  configure := fun cfg => pure cfg

  synthesize cfg offset _ := do
    let z0 ← cellAt cfg.runningSum offset
    rangeCheckLoop 10 cfg z0 offset numWords
    let zLast ← cellAt cfg.runningSum (offset + numWords)
    constrainConstant zLast (0 : Fp)
    let z1 ← cellAt cfg.runningSum (offset + 1)
    let z13 ← cellAt cfg.runningSum (offset + 13)
    return { z0, z1, z13 }

  elaborated :=
    { keygenRequirements :=
        { lookups cfg _ := [rangeCheckLookup 10 cfg]
          permutationColumns cfg _ := [cfg.runningSum] }
      synthesisSummary cfg offset _ _ :=
        rangeCheckAtDecomposedSynthesisSummary numWords cfg offset
      synthesisSummary_eq := by
        intro cfg offset input self
        have hn : numWords ≠ 0 := by omega
        apply FloorPlanner.RegionSynthesisSummary.ext
        all_goals
          simp [rangeCheckAtDecomposedSynthesisSummary, rangeCheckLoopSummary, hn, circuit_norm,
            synthesis_summary_norm]
      registered := by keygen_registration }

  EnvAssumptions cfg env :=
    TableLoaded 10 cfg env.env ∧ cfg.qLookup.index ≠ cfg.qRunning.index

  Witness := field
  extract cfg offset _ self env :=
    eval env (AssignedCell.of self offset cfg.runningSum : Var field Fp)

  Spec _ output elt :=
    output.z0 = elt ∧ elt.val < 2 ^ (10 * numWords) ∧
    output.z1.val = elt.val / 2 ^ 10 ∧ output.z13.val = elt.val / 2 ^ 130

  ProverAssumptions _ elt _ := elt.val < 2 ^ (10 * numWords)

  ProverSpec _ output elt _ :=
    output.z0 = elt ∧ output.z1 = ((elt.val / 2 ^ 10 : ℕ) : Fp) ∧
    output.z13 = ((elt.val / 2 ^ 130 : ℕ) : Fp)

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, _hDistinct⟩ := _hE
    obtain ⟨hUsable, hTableLt, _hTableEq⟩ := hTable
    obtain ⟨hLoop, hTailC⟩ := hc
    set f := zChain 10 cfg place self env offset with hf_def
    have hwords := rangeCheck_loop_word_bounds 10 cfg
      (AssignedCell.of self offset cfg.runningSum) place self env
      offset hTableLt numWords hLoop
    have hzLast0 : f numWords = 0 := by simp only [hf_def, zChain]; exact hTailC
    have hCard : (2 : ℕ) ^ (10 * numWords) ≤ PALLAS_BASE_CARD :=
      le_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hpow)
        (by norm_num [PALLAS_BASE_CARD]))
    obtain ⟨hOz0, hOz1, hOz13⟩ := h_output
    rw [show output_z0 = f 0 from by rw [← hOz0]; simp only [hf_def, zChain, add_zero],
      show output_z1 = f 1 from by rw [← hOz1]; simp only [hf_def, zChain],
      show output_z13 = f 13 from by rw [← hOz13]; simp only [hf_def, zChain]]
    refine ⟨trivial, ?_, ?_, ?_⟩
    · exact chain_element_lt 10 numWords hCard f hwords hzLast0
    · simpa only [show (10 * 1 : ℕ) = 10 from by norm_num] using
        chain_read 10 numWords hpow f hwords hzLast0 1 (by omega)
    · simpa only [show (10 * 13 : ℕ) = 130 from by norm_num] using
        chain_read 10 numWords hpow f hwords hzLast0 13 (by omega)

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    obtain ⟨hUsable, _hTableLt, hTableEq⟩ := hTable
    simp only [Placed.toEnvironment_env] at hTableEq hUsable
    -- the positional element cell's value (`z_0`)
    set eCell := env.advice cfg.runningSum ((place self + offset : ℕ) : ℤ)
      with heCell
    have hz0 : zChain 10 cfg place self env.toEnvironment offset 0 = eCell := by
      simp only [zChain, add_zero, heCell]
    have hz : ∀ j, j ≤ numWords → zChain 10 cfg place self env.toEnvironment offset j
        = ((eCell.val / 2 ^ (10 * j) : ℕ) : Fp) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp only [Nat.mul_zero, pow_zero, Nat.div_one, hz0, ZMod.natCast_zmod_val]
      · have hv := rangeCheck_loop_zvalues 10 cfg
          (AssignedCell.of self offset cfg.runningSum) place self env offset
          numWords hwit j hjpos hj
        rw [hv]
        simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
          Cell.of_rowOffset, Cell.of_column, Environment.get_advice, heCell]
    have heInputLt : eCell.val < 2 ^ (10 * numWords) := hPA
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact rangeCheck_loop_constraints_complete 10 cfg
        (AssignedCell.of self offset cfg.runningSum) place self
        env.toEnvironment offset eCell.val (by norm_num [PALLAS_BASE_CARD])
        hUsable hTableEq numWords hz
    · have hzn := hz numWords le_rfl
      simp only [zChain] at hzn
      rw [hzn, Nat.div_eq_of_lt heInputLt, Nat.cast_zero]
    · rw [heCell]
      exact h_output.1.symm
    · have hzn := hz 1 (by omega)
      simp only [zChain] at hzn
      rw [← hzn]
      exact h_output.2.1.symm
    · have hzn := hz 13 (by omega)
      simp only [zChain] at hzn
      rw [show (130 : ℕ) = 10 * 13 from by norm_num, ← hzn]
      exact h_output.2.2.symm

@[synthesis_summary_norm]
theorem rangeCheckAtDecomposed_synthesisSummary_eq
    (numWords : ℕ) (h13 : 13 ≤ numWords) (hpow : 10 * numWords ≤ 254)
    (cfg : Config 10) (offset : ℕ) (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        (((rangeCheckAtDecomposed numWords h13 hpow).synthesize
          cfg offset ()).operations region) =
      rangeCheckAtDecomposedSynthesisSummary numWords cfg offset :=
  (rangeCheckAtDecomposed numWords h13 hpow).elaborated.synthesisSummary_eq
    cfg offset () region |>.symm

@[synthesis_summary_norm]
theorem rangeCheckAtDecomposed_elaborated_synthesisSummary_eq
    (numWords : ℕ) (h13 : 13 ≤ numWords) (hpow : 10 * numWords ≤ 254)
    (cfg : Config 10) (offset : ℕ) (region : RegionIndex) :
    (rangeCheckAtDecomposed numWords h13 hpow).elaborated.synthesisSummary
        cfg offset () region =
      rangeCheckAtDecomposedSynthesisSummary numWords cfg offset := rfl

/-- Rust `witness_check(j, 25, true)` as used by `y_canonicity`: its own
`"Witness element"` region, witnessing the element from the caller-supplied program `w`,
then the positional strict decomposed check. -/
def witnessCheckDecomposed (cfg : Config 10) (w : WitgenIR Fp 1) :
    Circuit Fp (Var DecomposedOutput Fp) :=
  assignRegion "Witness element" (do
    let _elt ← assignAdvice cfg.runningSum 0 w
    (rangeCheckAtDecomposed 25 (by norm_num) (by norm_num)).call cfg 0 ())

def witnessCheckDecomposedSynthesisSummary
    (cfg : Config 10) :
    FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (FloorPlanner.RegionSynthesisSummary.ofColumns
      [.column .advice cfg.runningSum.index,
        .selector cfg.qLookup.index,
        .selector cfg.qRunning.index,
        .column .advice cfg.runningSum.index]
      26 1)

@[synthesis_summary_norm]
theorem witnessCheckDecomposed_synthesisSummary
    (cfg : Config 10) (w : WitgenIR Fp 1) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
      ((witnessCheckDecomposed cfg w).operations region) =
        witnessCheckDecomposedSynthesisSummary cfg := by
  simp only [witnessCheckDecomposedSynthesisSummary, witnessCheckDecomposed,
    operations_assignRegion, RegionCircuit.operations_bind]
  apply congrArg FloorPlanner.SynthesisSummary.ofRegion
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [operations_assignAdvice, synthesis_summary_norm,
      rangeCheckAtDecomposedSynthesisSummary, List.singleton_append]
  · simp only [operations_assignAdvice, synthesis_summary_norm,
      rangeCheckAtDecomposedSynthesisSummary]
    norm_num
  · simp only [operations_assignAdvice, synthesis_summary_norm,
      rangeCheckAtDecomposedSynthesisSummary, Nat.zero_add]

@[circuit_norm]
theorem witnessCheckDecomposed_nextRegionIndex
    (cfg : Config 10) (w : WitgenIR Fp 1) (region : RegionIndex) :
    (witnessCheckDecomposed cfg w).nextRegionIndex region = region + 1 := by
  simp only [witnessCheckDecomposed, circuit_norm]

/-! ## `copy_check` — the layouter-level range-check wrapper

Rust `LookupRangeCheck::copy_check` (`lookup_range_check.rs:124-140`): a
`layouter.assign_region` around `range_check`, with `element` copied into the running-sum
column at offset 0 (via `range_check`'s own `copyAdvice`). It is the layouter-level entry
that `mul/overflow.rs`'s `s_minus_lo_130` (`overflow.rs:200-205`) actually calls. We realize
it as the `toFormal` lift of `rangeCheck` — the wrapping region starts the body at offset 0,
matching `copy_check`'s single `assign_region`; all contracts (including the C6 `ProverSpec`)
transfer verbatim through `toFormal`. -/

/-- Rust `copy_check` (`lookup_range_check.rs:124-140`): the layouter-level range-check that
wraps `range_check` in its own region (element copied in at offset 0). The `toFormal` lift of
`rangeCheck`. -/
def copyCheck (K numWords : ℕ) (strict : Bool) :
    FormalCircuit Fp (Config K) (Config K) Inputs Output :=
  (rangeCheck K numWords strict).toFormal
    s!"{numWords} words range check"

def copyCheckSynthesisSummary (K numWords : ℕ) (strict : Bool)
    (cfg : Config K) : FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (FloorPlanner.RegionSynthesisSummary.ofColumns
      ([.column .advice cfg.runningSum.index] ++
        if numWords = 0 then [] else
          [.selector cfg.qLookup.index,
            .selector cfg.qRunning.index,
            .column .advice cfg.runningSum.index])
      (numWords + 1) (if strict then 1 else 0))

@[synthesis_summary_norm]
theorem copyCheck_synthesisSummary_eq (K numWords : ℕ) (strict : Bool)
    (cfg : Config K) (input : Var Inputs Fp) (region : RegionIndex) :
    (copyCheck K numWords strict).elaborated.synthesisSummary cfg input region =
      copyCheckSynthesisSummary K numWords strict cfg := by
  unfold copyCheck
  rw [FormalRegionCircuit.toFormal_synthesisSummary]
  rw [rangeCheck_elaborated_synthesisSummary_eq]
  simp only [rangeCheckSynthesisSummary, copyCheckSynthesisSummary,
    Nat.zero_add]

/-- The range-check wrapper's final cell stays in the configured running-sum column. -/
@[keygen_norm]
theorem copyCheck_output_zLast_column (K numWords : ℕ) (strict : Bool)
    (cfg : Config K) (input : Var Inputs Fp) (i : RegionIndex) :
    ((copyCheck K numWords strict).output cfg input i).zLast.cell.column = cfg.runningSum := by
  unfold FormalCircuit.output
  rw [(copyCheck K numWords strict).elaborated.output_eq]
  simp only [copyCheck, FormalRegionCircuit.toFormal, rangeCheck, circuit_norm]
  split <;> rfl

/-- Rust `witness_short_check` (`lookup_range_check.rs:271-294`): its own
`"Range check {num_bits} bits"` region, witnessing the element from the caller-supplied
program `w` at `(running_sum, 0)` — NO copy — then the positional `shortRangeCheck`.
Returns the witnessed element cell (Rust hands it out for downstream copies). -/
def witnessShortCheck (K numBits : ℕ) (cfg : Config K) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp) :=
  assignRegion s!"Range check {numBits} bits" (do
    let elt ← assignAdvice cfg.runningSum 0 w
    let _ ← (shortRangeCheck K numBits).call cfg 0 ()
    pure elt)

def witnessShortCheckSynthesisSummary
    (K : ℕ) (cfg : Config K) :
    FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    ((FloorPlanner.RegionSynthesisSummary.ofColumns
      [.column .advice cfg.runningSum.index] 1 0).combine
        (FloorPlanner.RegionSynthesisSummary.ofColumns
          [.selector cfg.qLookup.index,
            .column .advice cfg.runningSum.index,
            .selector cfg.qLookup.index,
            .column .advice cfg.runningSum.index,
            .selector cfg.qBitshift.index]
          3 1))

@[synthesis_summary_norm]
theorem witnessShortCheck_synthesisSummary
    (K numBits : ℕ) (cfg : Config K) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    FloorPlanner.synthesisSummary
      ((witnessShortCheck K numBits cfg w).operations region) =
        witnessShortCheckSynthesisSummary K cfg := by
  simp only [witnessShortCheckSynthesisSummary, witnessShortCheck,
    operations_assignRegion, synthesis_summary_norm]
  apply congrArg FloorPlanner.SynthesisSummary.ofRegion
  apply FloorPlanner.RegionSynthesisSummary.ext
  all_goals simp only [shortRangeCheck, circuit_norm, synthesis_summary_norm]
  omega

@[circuit_norm]
theorem witnessShortCheck_nextRegionIndex
    (K numBits : ℕ) (cfg : Config K) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    (witnessShortCheck K numBits cfg w).nextRegionIndex region = region + 1 := by
  simp only [witnessShortCheck, circuit_norm]

/-- Witnessing a short range check preserves the child's single deferred
constant request. -/
@[synthesis_summary_norm]
theorem witnessShortCheck_synthesisSummary_constantSiteCount
    (K numBits : ℕ) (config : Config K) (w : WitgenIR Fp 1)
    (region : RegionIndex) :
    (FloorPlanner.synthesisSummary
      ((witnessShortCheck K numBits config w).operations
        region)).constantSiteCount = 1 := by
  simp only [witnessShortCheck, operations_assignRegion,
    circuit_norm]
  simp only [shortRangeCheck, circuit_norm]

/-- The cell returned by `witnessShortCheck` stays in the configured running-sum column. -/
@[keygen_norm]
theorem witnessShortCheck_output_column (K numBits : ℕ) (cfg : Config K)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    ((witnessShortCheck K numBits cfg w).output i).cell.column = cfg.runningSum := by
  simp only [witnessShortCheck, circuit_norm]

/-- Rust `witness_check` (`lookup_range_check.rs:143-161`): its own `"Witness element"`
region, witnessing the element at `(running_sum, 0)` from the caller-supplied program
`w`, then the positional word-wise `rangeCheckAt`. Returns the `(z0, zLast)` cells. -/
def witnessCheck (K numWords : ℕ) (strict : Bool) (cfg : Config K)
    (w : WitgenIR Fp 1) : Circuit Fp (Var Output Fp) :=
  assignRegion "Witness element" (do
    let _elt ← assignAdvice cfg.runningSum 0 w
    (rangeCheckAt K numWords strict).call cfg 0 ())

/-- Reduced layouter footprint of a word-wise witness check. -/
def witnessCheckSynthesisSummary (K numWords : ℕ)
    (strict : Bool) (cfg : Config K) :
    FloorPlanner.SynthesisSummary :=
  FloorPlanner.SynthesisSummary.ofRegion
    (FloorPlanner.RegionSynthesisSummary.ofColumns
      ([.column .advice cfg.runningSum.index] ++
        if numWords = 0 then [] else
          [.selector cfg.qLookup.index,
            .selector cfg.qRunning.index,
            .column .advice cfg.runningSum.index])
      (numWords + 1) (if strict then 1 else 0))

/-- `witnessCheckSynthesisSummary` is the exact summary of the helper's operation
stream. -/
@[synthesis_summary_norm]
theorem witnessCheck_synthesisSummary
    (K numWords : ℕ) (strict : Bool) (cfg : Config K)
    (w : WitgenIR Fp 1) (region : RegionIndex) :
    FloorPlanner.synthesisSummary
      ((witnessCheck K numWords strict cfg w).operations region) =
        witnessCheckSynthesisSummary K numWords strict cfg := by
  simp only [witnessCheckSynthesisSummary, witnessCheck,
    operations_assignRegion, RegionCircuit.operations_bind]
  apply congrArg FloorPlanner.SynthesisSummary.ofRegion
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [operations_assignAdvice, synthesis_summary_norm,
      rangeCheckAtSynthesisSummary, List.singleton_append]
  · simp only [operations_assignAdvice, synthesis_summary_norm,
      rangeCheckAtSynthesisSummary, Nat.zero_add]
    split <;> omega
  · simp only [operations_assignAdvice, synthesis_summary_norm,
      rangeCheckAtSynthesisSummary, Nat.zero_add]

@[circuit_norm]
theorem witnessCheck_nextRegionIndex
    (K numWords : ℕ) (strict : Bool) (cfg : Config K)
    (w : WitgenIR Fp 1) (region : RegionIndex) :
    (witnessCheck K numWords strict cfg w).nextRegionIndex region =
      region + 1 := by
  simp only [witnessCheck, circuit_norm]

/-- Every cell returned by the decomposed witness check stays in the running-sum column. -/
@[keygen_norm]
theorem witnessCheckDecomposed_output_z0_column (cfg : Config 10)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    ((witnessCheckDecomposed cfg w).output i).z0.cell.column = cfg.runningSum := by
  simp only [witnessCheckDecomposed, circuit_norm]
  unfold FormalRegionCircuit.output
  rw [(rangeCheckAtDecomposed 25 (by norm_num) (by norm_num)).elaborated.output_eq]
  simp only [rangeCheckAtDecomposed, circuit_norm]

@[keygen_norm]
theorem witnessCheckDecomposed_output_z1_column (cfg : Config 10)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    ((witnessCheckDecomposed cfg w).output i).z1.cell.column = cfg.runningSum := by
  simp only [witnessCheckDecomposed, circuit_norm]
  unfold FormalRegionCircuit.output
  rw [(rangeCheckAtDecomposed 25 (by norm_num) (by norm_num)).elaborated.output_eq]
  simp only [rangeCheckAtDecomposed, circuit_norm]

@[keygen_norm]
theorem witnessCheckDecomposed_output_z13_column (cfg : Config 10)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    ((witnessCheckDecomposed cfg w).output i).z13.cell.column = cfg.runningSum := by
  simp only [witnessCheckDecomposed, circuit_norm]
  unfold FormalRegionCircuit.output
  rw [(rangeCheckAtDecomposed 25 (by norm_num) (by norm_num)).elaborated.output_eq]
  simp only [rangeCheckAtDecomposed, circuit_norm]

/-- Both cells returned by `witnessCheck` stay in its running-sum column. -/
@[keygen_norm]
theorem witnessCheck_output_z0_column (K numWords : ℕ) (strict : Bool)
    (cfg : Config K) (w : WitgenIR Fp 1) (i : RegionIndex) :
    ((witnessCheck K numWords strict cfg w).output i).z0.cell.column = cfg.runningSum := by
  simp only [witnessCheck, circuit_norm]
  unfold FormalRegionCircuit.output
  rw [(rangeCheckAt K numWords strict).elaborated.output_eq]
  simp only [rangeCheckAt, circuit_norm]
  split <;> rfl

@[keygen_norm]
theorem witnessCheck_output_zLast_column (K numWords : ℕ) (strict : Bool)
    (cfg : Config K) (w : WitgenIR Fp 1) (i : RegionIndex) :
    ((witnessCheck K numWords strict cfg w).output i).zLast.cell.column = cfg.runningSum := by
  simp only [witnessCheck, circuit_norm]
  unfold FormalRegionCircuit.output
  rw [(rangeCheckAt K numWords strict).elaborated.output_eq]
  simp only [rangeCheckAt, circuit_norm]
  split <;> rfl

@[keygen_norm, keygen_helper]
theorem witnessShortCheck_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {permutationColumns : List AnyColumn}
    (K numBits : ℕ) (cfg : Config K) (w : WitgenIR Fp 1)
    (i : RegionIndex)
    (hgate : bitshiftGate K cfg ∈ gates)
    (hlookup : rangeCheckLookup K cfg ∈ lookups)
    (hpermutation : (cfg.runningSum : AnyColumn) ∈ permutationColumns) :
    ((witnessShortCheck K numBits cfg w).operations i).KeygenRegistered
      gates lookups permutationColumns := by
  unfold witnessShortCheck
  keygen_registration

@[keygen_norm, keygen_helper]
theorem witnessCheck_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {permutationColumns : List AnyColumn}
    (K numWords : ℕ) (strict : Bool) (cfg : Config K)
    (w : WitgenIR Fp 1) (i : RegionIndex)
    (hlookup : rangeCheckLookup K cfg ∈ lookups)
    (hpermutation : (cfg.runningSum : AnyColumn) ∈ permutationColumns) :
    ((witnessCheck K numWords strict cfg w).operations i).KeygenRegistered
      gates lookups permutationColumns := by
  unfold witnessCheck
  keygen_registration

@[keygen_norm, keygen_helper]
theorem witnessCheckDecomposed_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {permutationColumns : List AnyColumn}
    (cfg : Config 10) (w : WitgenIR Fp 1) (i : RegionIndex)
    (hlookup : rangeCheckLookup 10 cfg ∈ lookups)
    (hpermutation : (cfg.runningSum : AnyColumn) ∈ permutationColumns) :
    ((witnessCheckDecomposed cfg w).operations i).KeygenRegistered
      gates lookups permutationColumns := by
  unfold witnessCheckDecomposed
  keygen_registration

/-- A short-range-check capability exported by the shared range-check configurer. -/
def shortRangeConfigureCertificate (K numBits : ℕ)
    (runningSum : Column .advice) (tableIdx : TableColumn)
    (counts : ConfigureCounts) :
    (shortRangeCheck K numBits).ConfigurationCertificate
      ((configure K runningSum tableIdx).output counts)
      { gates := ((configure K runningSum tableIdx).delta counts).gates
        lookups := ((configure K runningSum tableIdx).delta counts).lookups
        permutationColumns :=
          ((configure K runningSum tableIdx).delta counts).permutationRequests } := by
  let cfg := (configure K runningSum tableIdx).output counts
  apply ((shortRangeCheck K numBits).configureCertificate cfg {} ()).mono
  · intro gate hgate
    simp only [shortRangeCheck, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil] at hgate
    simpa [cfg, keygen_norm] using hgate
  · intro argument hargument
    simp only [shortRangeCheck, FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil] at hargument
    simpa [cfg, keygen_norm] using hargument
  · intro column hcolumn
    simp only [keygen_norm, shortRangeCheck,
      FormalRegionCircuit.keygenRequirements,
      ElaboratedRegionCircuit.keygenRequirements, Configure.delta_pure,
      List.append_nil, List.mem_singleton] at hcolumn
    subst column
    simp only [keygen_norm, cfg, configure]

derive_contract_bridges rangeCheckAt (K numWords : ℕ) (strict : Bool) :=
  rangeCheckAt K numWords strict

derive_contract_bridges rangeCheckAtDecomposed (numWords : ℕ) (h13 : 13 ≤ numWords)
  (hpow : 10 * numWords ≤ 254) := rangeCheckAtDecomposed numWords h13 hpow

derive_contract_bridges shortRangeCheck (K numBits : ℕ) := shortRangeCheck K numBits

end Zcash.Circuits.LookupRangeCheck
