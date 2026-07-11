import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Orchard.Specs.Pallas

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

namespace Halo2.Ironwood.LookupRangeCheck

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
def rangeCheckLookup (K : ℕ) (cfg : Config K) : LookupArgument Fp where
  inputs :=
    let qL : Expression Fp Query := querySelector cfg.qLookup
    let qR : Expression Fp Query := querySelector cfg.qRunning
    let zCur : Expression Fp Query := queryAdvice cfg.runningSum 0
    let zNext : Expression Fp Query := queryAdvice cfg.runningSum 1
    [qL * (qR * (zCur - (2 ^ K : Fp) * zNext) + (1 - qR) * zCur)]
  tables := [queryFixed cfg.tableIdx.inner]

/-- The "Short lookup bitshift" gate, ported verbatim from `configure`
(`lookup_range_check.rs:370-384`). Reads `word` at `Rotation::prev()` (−1), `shifted_word`
at `Rotation::cur()` (0), `inv_two_pow_s` at `Rotation::next()` (+1); the single constraint
is `word · 2^K · inv_two_pow_s − shifted_word`. -/
def bitshiftGate (K : ℕ) (cfg : Config K) : Gate Fp where
  name := "Short lookup bitshift"
  selector := cfg.qBitshift
  constraints :=
    let word : Expression Fp Query := queryAdvice cfg.runningSum (-1)
    let shiftedWord : Expression Fp Query := queryAdvice cfg.runningSum 0
    let invTwoPowS : Expression Fp Query := queryAdvice cfg.runningSum 1
    Constraints.withSelector cfg.qBitshift
      [("bitshift", word * (2 ^ K : Fp) * invTwoPowS - shiftedWord)]

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
  lookup [((rangeCheckLookup K cfg).inputs.headI, tableIdx)]
  -- register the bitshift gate
  createGate (bitshiftGate K cfg)
  return cfg

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

/-- Single-field input: the `element` to be range-checked (an already-assigned cell). -/
structure Inputs (F : Type) where
  element : F
deriving ProvableStruct

/-- The word at `offset+2`: `2^(−num_bits) = (2^num_bits)⁻¹`, assigned as a constant. -/
def invTwoPowS (numBits : ℕ) : Fp := (2 ^ numBits : Fp)⁻¹

def shortRangeCheck (K numBits : ℕ) :
    FormalRegionCircuit Fp (Config K) (Config K) Inputs field where
  configure := fun cfg => pure cfg

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    -- copy `element` into `running_sum` at `offset`; short lookup there (q_running OFF)
    let _elt ← copyAdvice input.element cfg.runningSum offset
    (rangeCheckLookup K cfg).enable [cfg.qLookup] offset
    -- assign shifted = element · 2^(K − num_bits) at `offset + 1`; short lookup there too
    let _shifted ← assignAdvice cfg.runningSum (offset + 1)
      (.ofFExpr ((.expr input.element) * (.const (2 ^ (K - numBits) : Fp))))
    (rangeCheckLookup K cfg).enable [cfg.qLookup] (offset + 1)
    -- assign 2^(−num_bits) as a constant at `offset + 2`
    let invCell ← assignAdvice cfg.runningSum (offset + 2) (.ofFExpr (.const (invTwoPowS numBits)))
    constrainConstant invCell (invTwoPowS numBits)
    -- bitshift gate at `offset + 1`
    (bitshiftGate K cfg).enable (offset + 1)
    return input.element

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

  Spec input _ _ := input.element.val < 2 ^ numBits

  -- honest-prover precondition: `element` really is a `num_bits` word (Rust's caller
  -- guarantees this — `short_range_check` is only sound *and* complete on such elements).
  ProverAssumptions input _ := input.element.val < 2 ^ numBits

  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output hE hA hc
    simp only [circuit_norm, rangeCheckLookup, bitshiftGate, invTwoPowS,
      Constraints.withSelector] at hc
    provable_type_simp
    obtain ⟨⟨_hUsable, hTableLt, _hTableEq⟩, hDistinct⟩ := hE
    obtain ⟨hNumBits, hCard⟩ := hA
    -- the short-row valuation: `q_running ∉ [q_lookup]` (distinct indices), so the gated
    -- input reduces to `z_cur` at both rows
    rw [if_neg (fun h => hDistinct h.symm)] at hc
    -- destructure: copy (element ↦ runningSum@offset), two memberships, bitshift gate
    obtain ⟨hCopy, hMemWord, hMemShift, hBitshift⟩ := hc
    -- ACCEPTANCE (C2a #5): consume each membership existential + `TableLoaded`'s usable-rows
    -- bound into a value bound via `mem_usableRows_val_lt` — the mechanized "two obtains + apply"
    -- pattern, collapsed to one `exact` per membership.
    simp only [List.cons.injEq, and_true, one_mul, zero_mul, sub_zero,
      zero_add] at hMemWord hMemShift
    have hWordLt : (env.env.advice cfg.runningSum ↑(env.place self + offset)).val < 2 ^ K :=
      mem_usableRows_val_lt hTableLt hMemWord
    have hShiftLt :
        (env.env.advice cfg.runningSum ↑(env.place self + (offset + 1))).val < 2 ^ K :=
      mem_usableRows_val_lt hTableLt hMemShift
    -- the copy constraint: input_element = advice runningSum @offset
    rw [← h_input, ← hCopy]
    -- bitshift gate: shifted = word · 2^K · 2^(−num_bits) = word · 2^(K−num_bits)
    -- (rearranged via the field-inverse split), so the shift lemma applies
    set word := env.env.advice cfg.runningSum ↑(env.place self + offset) with hword_def
    set shifted := env.env.advice cfg.runningSum ↑(env.place self + (offset + 1)) with hshift_def
    have hPowLtCard : 2 ^ numBits < PALLAS_BASE_CARD :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hNumBits)
        (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (pow_two_pos K)) hCard)
    have hPowNe : (2 ^ numBits : Fp) ≠ 0 := by
      intro hzero
      have hzero' : ((2 ^ numBits : ℕ) : Fp) = 0 := by simpa using hzero
      have hdiv := (ZMod.natCast_eq_zero_iff (2 ^ numBits) PALLAS_BASE_CARD).mp hzero'
      exact (Nat.not_dvd_of_pos_of_lt (pow_two_pos _) hPowLtCard) hdiv
    have hEqShift : shifted = word * (2 ^ (K - numBits) : Fp) := by
      -- hBitshift decomposes into: invTwoPowS cell = (2^num_bits)⁻¹, and the gate poly
      -- word · 2^K · invTwoPowS − shifted = 0 (with invTwoPowS the offset+2 cell). The
      -- gate's cell rows arrive normalized by `cast_row_pred`/`row_succ_succ` (Lemmas.lean).
      obtain ⟨hInvConst, hGate⟩ := hBitshift
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
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hE hA hpa
    simp only [circuit_norm, rangeCheckLookup, bitshiftGate, invTwoPowS,
      Constraints.withSelector] at hwit ⊢
    obtain ⟨⟨hUsable, _hTableLt, hTableEq⟩, hDistinct⟩ := hE
    obtain ⟨hNumBits, hCard⟩ := hA
    -- normalize the table facts to the prover env's `.env` spelling (they arrive over
    -- `env.toEnvironment.env`; `Placed.toEnvironment_env` bridges to `env.env.toEnvironment`,
    -- defeq to the `env.env.fixed` in the goal)
    simp only [Placed.toEnvironment_env] at hTableEq hUsable
    rw [if_neg (fun h => hDistinct h.symm)]
    -- land `h_input` on the element component (the cell field value = input.element)
    provable_type_simp
    obtain ⟨hCopy, hShiftWit, hInvWit⟩ := hwit
    -- the element cell's field value, and its `.val` bound from the honest-prover assumption
    set E := env.env.get input_var_element.cell.column
      ↑(env.place input_var_element.cell.regionIndex + input_var_element.cell.rowOffset) with hE_def
    have hE_input : E = input_element := by rw [hE_def]; exact h_input
    have hEltLt : E.val < 2 ^ numBits := by rw [hE_input]; exact hpa
    have hEltLtK : E.val < 2 ^ K :=
      lt_of_lt_of_le hEltLt (Nat.pow_le_pow_right (by norm_num) hNumBits)
    have hCardK : 2 ^ K < PALLAS_BASE_CARD :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (pow_two_pos K)) hCard
    -- `↑E.val = E` (E < 2^K < |Fp|)
    have hE_cast : ((E.val : ℕ) : Fp) = E := ZMod.natCast_zmod_val E
    -- the shifted word value and its `.val` bound (donor completeness lemma)
    have hShiftedLtK : (E * (2 ^ (K - numBits) : Fp)).val < 2 ^ K :=
      shortRange_completeness_shifted K numBits hNumBits hCardK E hEltLt
    have hShift_cast :
        (((E * (2 ^ (K - numBits) : Fp)).val : ℕ) : Fp) = E * (2 ^ (K - numBits) : Fp) :=
      ZMod.natCast_zmod_val _
    refine ⟨hCopy, ?_, ?_, hInvWit, ?_⟩
    · -- membership @offset: witness row `E.val` (usable: `E.val < 2^K ≤ usableRows`),
      -- which holds `↑E.val = E = z_cur`
      refine ⟨E.val, lt_of_lt_of_le hEltLtK hUsable, ?_⟩
      simp only [one_mul, zero_mul, sub_zero, zero_add, List.cons.injEq, and_true]
      rw [hCopy, hTableEq E.val hEltLtK]
      exact hE_cast.symm
    · -- membership @(offset+1): witness row `shifted.val` (usable), holding
      -- `↑shifted.val = shifted`
      refine ⟨(E * (2 ^ (K - numBits) : Fp)).val, lt_of_lt_of_le hShiftedLtK hUsable, ?_⟩
      simp only [one_mul, zero_mul, sub_zero, zero_add, List.cons.injEq, and_true]
      rw [hShiftWit, hTableEq _ hShiftedLtK]
      exact hShift_cast.symm
    · -- bitshift gate: shifted = word · 2^K · 2^(−num_bits). Cell rows arrive normalized
      -- by `cast_row_pred`/`row_succ_succ` (Lemmas.lean).
      rw [hCopy, hShiftWit, hInvWit]
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
word `idx` inside the ambient region starting at `offset`: enable `q_lookup` AND
`q_running` at row `offset+idx` — so the lookup input is the running word
`z_idx − 2^K·z_{idx+1}` — and assign `z_{idx+1}` at row `offset+idx+1`.

Cells are addressed by their absolute row (`offset+idx`), not threaded through the monad:
the running sum lives at fixed rows `offset, offset+1, …`, so round `idx` is independent of
the other rounds. That independence is exactly what makes `(loop n).operations` a clean
concatenation of `(round idx).operations`, hence inductable. -/
def rangeCheckRound (K : ℕ) (cfg : Config K) (element : AssignedCell Fp) (offset idx : ℕ) :
    RegionCircuit Fp Unit := do
  -- running-sum row: both q_lookup and q_running on (§1.4 → input = running word a_idx)
  (rangeCheckLookup K cfg).enable [cfg.qLookup, cfg.qRunning] (offset + idx)
  -- assign z_{idx+1} = element ≫ (K·(idx+1)) at row offset+idx+1
  let _z ← assignAdvice cfg.runningSum (offset + idx + 1) (zWitness K (idx + 1) element)
  return ()

/-- The running-sum loop: `numWords` rounds, structurally recursive. By the append-bind of
`RegionCircuit`, `(rangeCheckLoop … (n+1)).operations self`
`= (rangeCheckLoop … n).operations self ++ (rangeCheckRound … n).operations self` — the
per-round decomposition the induction consumes (`rangeCheckLoop_operations_succ`). -/
def rangeCheckLoop (K : ℕ) (cfg : Config K) (element : AssignedCell Fp) (offset : ℕ) :
    ℕ → RegionCircuit Fp Unit
  | 0 => pure ()
  | n + 1 => do
    rangeCheckLoop K cfg element offset n
    rangeCheckRound K cfg element offset n

/-- Per-round operations decomposition (holds by `rfl` via `operations_bind`): the crux
that makes the loop inductable. -/
theorem rangeCheckLoop_operations_succ (K : ℕ) (cfg : Config K) (element : AssignedCell Fp)
    (offset n : ℕ) (self : RegionIndex) :
    (rangeCheckLoop K cfg element offset (n + 1)).operations self
      = (rangeCheckLoop K cfg element offset n).operations self
        ++ (rangeCheckRound K cfg element offset n).operations self := rfl

/-- The running sum read off the environment: `z_j = env.advice runningSum` at absolute
row `place self + (offset + j)`. The chain the telescoping algebra runs over. -/
def zChain (K : ℕ) (cfg : Config K) (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment Fp) (offset : ℕ) (j : ℕ) : Fp :=
  env.advice cfg.runningSum ((place self + (offset + j) : ℕ) : ℤ)

/-- **The round-invariant / z-chain lemma (soundness), proven by induction over rounds.**
If the loop's constraints hold and the table is loaded, then every word `z_i − 2^K·z_{i+1}`
(`i < numWords`) is a `K`-bit value — the hypothesis `chain_telescope`/`chain_element_lt`
consume. This is the loop-shaped proof: the induction is over `numWords`, using the
per-round operations decomposition (`rangeCheckLoop_operations_succ`) and the append
splitting of `RegionOperations.Constraints`.

The membership existential at round `i` (both `q_lookup`, `q_running` on) delivers a usable
table row holding the word `z_i − 2^K·z_{i+1}`; `TableLoaded`'s usable-rows bound makes that
value `< 2^K`. -/
theorem rangeCheck_loop_word_bounds (K : ℕ) (cfg : Config K) (element : AssignedCell Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset : ℕ)
    (hTableLt : ∀ r : ℕ, r < env.usableRows → (env.fixed cfg.tableIdx.inner (r : ℤ)).val < 2 ^ K) :
    ∀ numWords : ℕ,
    RegionOperations.Constraints place self env
      ((rangeCheckLoop K cfg element offset numWords).operations self) →
    ∀ i, i < numWords → ∃ w : ℕ, w < 2 ^ K ∧
      zChain K cfg place self env offset i
        = 2 ^ K * zChain K cfg place self env offset (i + 1) + (w : Fp) := by
  intro numWords
  induction numWords with
  | zero => intro _ i hi; omega
  | succ n ih =>
    rw [rangeCheckLoop_operations_succ, RegionOperations.constraints_append]
    rintro ⟨hLoop, hRound⟩ i hi
    -- last round `n` is new; earlier rounds `i < n` come from the induction hypothesis
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact ih hLoop i hi'
    · -- the fresh round `n`: peel its membership existential. Both q_lookup and q_running
      -- are on, so the gated input reduces to the running word `z_i − 2^K·z_{i+1}`.
      simp only [rangeCheckRound, circuit_norm, rangeCheckLookup, List.map_cons, List.map_nil,
        List.cons.injEq, and_true, one_mul, zero_mul, add_zero, sub_self] at hRound
      obtain ⟨rW, hrWlt, hrW⟩ := hRound
      -- word = env.fixed tableIdx rW, whose val < 2^K (TableLoaded)
      refine ⟨(env.fixed cfg.tableIdx.inner (rW : ℤ)).val, hTableLt rW hrWlt, ?_⟩
      rw [ZMod.natCast_zmod_val]
      simp only [zChain]
      rw [show offset + (i + 1) = offset + i + 1 from by omega]
      linear_combination hrW

/-- **Completeness z-value lemma (loop-shaped, by induction over rounds).** The honest
prover's `ExtendsWitnesses` of the loop pins each interior running sum to the canonical
shift `z_j = ↑(element.val ≫ (K·j))` for `1 ≤ j ≤ numWords` (`zWitness` = that shift). The
`j = 0` sum is `element`, pinned by the copy outside the loop. -/
theorem rangeCheck_loop_zvalues (K : ℕ) (cfg : Config K) (element : AssignedCell Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset : ℕ) :
    ∀ numWords : ℕ,
    RegionOperations.ExtendsWitnesses place self env
      ((rangeCheckLoop K cfg element offset numWords).operations self) →
    ∀ j, 1 ≤ j → j ≤ numWords →
      zChain K cfg place self env.toEnvironment offset j
        = ((element.eval place env.toEnvironment).val / 2 ^ (K * j) : ℕ) := by
  intro numWords
  induction numWords with
  | zero => intro _ j hj1 hj2; omega
  | succ n ih =>
    rw [rangeCheckLoop_operations_succ, RegionOperations.extendsWitnesses_append]
    rintro ⟨hLoop, hRound⟩ j hj1 hj2
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj2) with hj' | rfl
    · -- j ≤ n: from the induction hypothesis
      exact ih hLoop j hj1 (by omega)
    · -- j = n + 1: this round's own assignAdvice pins z_{n+1}
      simp only [rangeCheckRound, circuit_norm, zWitness] at hRound
      -- hRound: env.advice runningSum (offset + n + 1) = eval of the z-witness program
      simp only [zChain]
      rw [show offset + (n + 1) = offset + n + 1 from by omega]
      -- the witgen program evaluates to ↑(element.val / 2^(K·(n+1)))
      convert hRound using 2

/-- **Completeness loop-constraints lemma (loop-shaped, by induction over rounds).** Given
the honest running-sum values `z_j = ↑(a ≫ (K·j))` (`hz`, for `a := element.val`) and the
loaded table (block contents `hTableEq`, domain bound `hUsable`), the loop's `Constraints`
hold: the membership at each round `i` is witnessed by the honest word `a_i`'s value
(`< 2^K ≤ usableRows`, holding `↑a_i = a_i` in the table). -/
theorem rangeCheck_loop_constraints_complete (K : ℕ) (cfg : Config K) (element : AssignedCell Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset : ℕ) (a : ℕ)
    (hKcard : 2 ^ K ≤ PALLAS_BASE_CARD)
    (hUsable : 2 ^ K ≤ env.usableRows)
    (hTableEq : ∀ r : ℕ, r < 2 ^ K → env.fixed cfg.tableIdx.inner (r : ℤ) = (r : Fp)) :
    ∀ numWords : ℕ,
    (∀ j, j ≤ numWords → zChain K cfg place self env offset j = ((a / 2 ^ (K * j) : ℕ) : Fp)) →
    RegionOperations.Constraints place self env
      ((rangeCheckLoop K cfg element offset numWords).operations self) := by
  intro numWords
  induction numWords with
  | zero => intro _; exact trivial
  | succ n ih =>
    intro hz
    rw [rangeCheckLoop_operations_succ, RegionOperations.constraints_append]
    refine ⟨ih (fun j hj => hz j (by omega)), ?_⟩
    -- round `n` uses `hz n` and `hz (n+1)` (both ≤ n+1)
    have hzn := hz n (by omega)
    have hzn1 := hz (n + 1) (by omega)
    -- round `n`: membership witnessed by the honest word `a_n = z_n − 2^K·z_{n+1}`
    simp only [rangeCheckRound, circuit_norm, rangeCheckLookup, List.map_cons, List.map_nil,
      List.cons.injEq, and_true, one_mul, zero_mul, add_zero, sub_self]
    -- the honest word, rewritten to `↑b − 2^K·↑(b/2^K)` with `b = a ≫ (K·n)`
    have hword : zChain K cfg place self env offset n
          - 2 ^ K * zChain K cfg place self env offset (n + 1)
        = ((a / 2 ^ (K * n) : ℕ) : Fp) - 2 ^ K * (((a / 2 ^ (K * n) / 2 ^ K : ℕ)) : Fp) := by
      rw [hzn, hzn1]
      congr 3
      rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
    have hwordval :
        (zChain K cfg place self env offset n
          - 2 ^ K * zChain K cfg place self env offset (n + 1)).val < 2 ^ K := by
      rw [hword]; exact honest_word_val_lt K hKcard (a / 2 ^ (K * n))
    refine ⟨(zChain K cfg place self env offset n
        - 2 ^ K * zChain K cfg place self env offset (n + 1)).val,
      lt_of_lt_of_le hwordval hUsable, ?_⟩
    -- the running word equals the table cell at row `word.val`
    rw [hTableEq _ hwordval, ZMod.natCast_zmod_val]
    simp only [zChain, show offset + n + 1 = offset + (n + 1) from by omega]

/-- Read the assigned cell at a known region-local row/column (no op emitted). Lets
`synthesize` name the running-sum cells `z_0` and `z_{numWords}` for the `Output`, which
live at fixed rows rather than being threaded through the loop's return value. -/
def cellAt (col : Column .advice) (row : ℕ) : RegionCircuit Fp (AssignedCell Fp) :=
  fun self => (.of self row col, [])

@[circuit_norm]
theorem operations_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).operations self = [] := rfl

@[circuit_norm]
theorem output_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).output self = .of self row col := rfl

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
  ProverAssumptions input _ := strict = true → input.element.val < 2 ^ (K * numWords)

  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output hE hA hc
    obtain ⟨hTable, _hDistinct⟩ := hE
    obtain ⟨hUsable, hTableLt, _hTableEq⟩ := hTable
    -- peel the circuit structure: copy (z_0 = element) ++ loop ++ [zLast strict] output.
    -- keep the loop's `Constraints` chunk FOLDED (do not unfold `rangeCheckLoop`); the
    -- word-bound induction consumes it as-is.
    simp only [circuit_norm,
      RegionCircuit.operations_bind, RegionCircuit.output_bind,
      operations_copyAdvice, output_cellAt,
      operations_cellAt, RegionOperations.constraints_append] at hc h_output ⊢
    obtain ⟨hCopy, hLoop, _hTailC⟩ := hc
    -- land `h_input`/copy on the element cell value (destructures to `input_element` /
    -- `output_z0` / `output_zLast`)
    provable_type_simp
    -- the running-sum chain read off the env; the word-bound induction over the loop chunk
    set f := zChain K cfg env.place self env.env offset with hf_def
    have hwords := rangeCheck_loop_word_bounds K cfg input_var_element env.place self env.env
      offset hTableLt numWords hLoop
    -- z_0 = element (copy)
    have hz0 : f 0 = input_element := by
      simp only [hf_def, zChain, add_zero]; rw [hCopy]; exact h_input
    -- the telescoping decomposition (soundly available regardless of `strict`)
    obtain ⟨lo, hlo, htel⟩ := chain_telescope K f numWords hwords
    -- resolve the output cells (case on `strict` to compute the tail ops)
    rcases hbstrict : strict with _ | _ <;>
      simp only [hbstrict, circuit_norm, output_cellAt, operations_cellAt,
        operations_constrainConstant, RegionOperations.constraints_append,
        Bool.false_eq_true, if_true, if_false, reduceCtorEq] at _hTailC h_output ⊢ <;>
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
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hE hA hpa
    obtain ⟨hTable, hDistinct⟩ := hE
    obtain ⟨hUsable, _hTableLt, hTableEq⟩ := hTable
    simp only [Placed.toEnvironment_env] at hTableEq hUsable
    -- peel the circuit into: copy witness ++ loop witness ++ tail; keep the loop chunk folded
    simp only [circuit_norm, RegionCircuit.operations_bind, operations_copyAdvice,
      operations_cellAt, RegionOperations.extendsWitnesses_append,
      RegionOperations.constraints_append] at hwit ⊢
    obtain ⟨hCopyWit, hLoopWit, hTailWit⟩ := hwit
    obtain ⟨hCardN, hKcard⟩ := hA
    -- the honest z_0 = the element cell value; `eCell.val` is the decomposed nat `a`
    set eCell := input_var.element.eval env.place env.env.toEnvironment with heCell
    -- z_0 = element cell (from the copy's assignAdvice witness)
    have hz0 : zChain K cfg env.place self env.env.toEnvironment offset 0 = eCell := by
      simp only [zChain, add_zero, heCell, AssignedCell.eval, hCopyWit]
    -- the honest z-chain up to numWords: `z_j = ↑(eCell.val ≫ (K·j))`
    have hz : ∀ j, j ≤ numWords → zChain K cfg env.place self env.env.toEnvironment offset j
        = ((eCell.val / 2 ^ (K * j) : ℕ) : Fp) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp only [Nat.mul_zero, pow_zero, Nat.div_one, hz0, ZMod.natCast_zmod_val]
      · exact rangeCheck_loop_zvalues K cfg input_var.element env.place self env.env offset
          numWords hLoopWit j hjpos hj
    refine ⟨hCopyWit, ?_, ?_⟩
    · -- the loop's Constraints (membership at each round), via the completeness loop lemma
      exact rangeCheck_loop_constraints_complete K cfg input_var.element env.place self
        env.env.toEnvironment offset eCell.val hKcard hUsable hTableEq numWords hz
    · -- the tail: strict ⇒ `constrainConstant zLast 0` (⇒ z_last = 0); else nothing
      rcases hbstrict : strict with _ | _
      · -- strict = false: no tail constraint
        simp only [circuit_norm, operations_cellAt, RegionOperations.constraints_append]
      · -- strict = true: prove `zLast = 0` from the honest value (element < 2^{K·numWords})
        simp only [circuit_norm, operations_cellAt, operations_constrainConstant,
          RegionOperations.constraints_append, AssignedCell.of_cell, Cell.of, Cell.eval,
          Cell.of_column, Cell.of_regionIndex, Cell.of_rowOffset]
        have hzn := hz numWords le_rfl
        simp only [zChain] at hzn
        have heInput : eCell.val < 2 ^ (K * numWords) := by
          have hie : input.element = eCell := by
            rw [heCell, ← h_input]; provable_type_simp
          rw [← hie]; exact hpa hbstrict
        rw [hzn, Nat.div_eq_of_lt heInput, Nat.cast_zero]

/-- **Honest `zLast` value (composition helper).** From the honest `ExtendsWitnesses` of a
`rangeCheck … false` *call*, the exposed high-tail cell `zLast` (at `offset + numWords`) holds
the canonical shift `↑(element.val ≫ (K·numWords))`. This is the child's honest NATURAL-NUMBER
decomposition, which the verifier `Spec` (a field equation) does not expose — a lookup-child
consumer whose own bookkeeping needs the tail value (e.g. `Ecc.MulOverflow`, which must conclude
`zLast = 0` when the high half vanishes) reads it here. Additive, no change to the bundle.

Peels the `.subcircuit`-wrapped `synthesize` witnesses (copy ++ loop ++ `cellAt`s) and applies
`rangeCheck_loop_zvalues` at `j = numWords`. -/
theorem rangeCheck_call_zLast_value (K numWords : ℕ) (hnw : 0 < numWords) (cfg : Config K)
    (offset : ℕ) (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (inp : Var Inputs Fp)
    (hW : RegionOperations.ExtendsWitnesses env.place self env.env
      (((rangeCheck K numWords false).call cfg offset inp).operations self)) :
    env.env.advice cfg.runningSum ((env.place self + (offset + numWords) : ℕ) : ℤ)
      = (((inp.element.eval env.place env.env.toEnvironment).val / 2 ^ (K * numWords) : ℕ) : Fp) := by
  -- the call's ops are `[.subcircuit (synthesize.operations self)]`; its `ExtendsWitnesses`
  -- reduces (definitionally) to the child's `ExtendsWitnesses` of the synthesize ops
  have hW' : RegionOperations.ExtendsWitnesses env.place self env.env
      ((rangeCheck K numWords false).synthesize cfg offset inp |>.operations self) := hW.1
  clear hW
  rename' hW' => hW
  -- peel synthesize: copy ++ loop (the `cellAt`s and the `strict=false` branch emit no ops);
  -- keep the loop chunk folded
  simp only [rangeCheck, Bool.false_eq_true, if_false, circuit_norm,
    RegionCircuit.operations_bind, operations_copyAdvice, operations_cellAt] at hW
  obtain ⟨-, hLoopWit⟩ := hW
  -- `rangeCheck_loop_zvalues` at `j = numWords` (needs `1 ≤ numWords`)
  have := rangeCheck_loop_zvalues K cfg inp.element env.place self env.env offset numWords
    hLoopWit numWords hnw le_rfl
  simpa only [zChain, AssignedCell.eval] using this

end Halo2.Ironwood.LookupRangeCheck
