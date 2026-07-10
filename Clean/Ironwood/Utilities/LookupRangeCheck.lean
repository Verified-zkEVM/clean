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
    -- TACTIC GAP (tactic-layer, mechanizable): consume each membership existential +
    -- `TableLoaded`'s usable-rows bound into a value bound. The witness `tableRow` comes
    -- bounded by `env.usableRows` (the semantics is faithful to `lookup/prover.rs:573-585`),
    -- exactly the range `TableLoaded` characterizes — here it is an `obtain` + one
    -- application per membership; a future tactic should do this mechanically.
    simp only [List.cons.injEq, and_true, one_mul, zero_mul, sub_zero,
      zero_add] at hMemWord hMemShift
    obtain ⟨rW, hrWlt, hrW⟩ := hMemWord
    obtain ⟨rS, hrSlt, hrS⟩ := hMemShift
    -- word = advice runningSum @offset (short row) ; shifted = advice runningSum @(offset+1)
    have hWordLt : (env.env.advice cfg.runningSum ↑(env.place self + offset)).val < 2 ^ K := by
      rw [hrW]; exact hTableLt rW hrWlt
    have hShiftLt :
        (env.env.advice cfg.runningSum ↑(env.place self + (offset + 1))).val < 2 ^ K := by
      rw [hrS]; exact hTableLt rS hrSlt
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

end Halo2.Ironwood.LookupRangeCheck
