import Clean.Halo2
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Utilities.RunningSum

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/utilities/decompose_running_sum.rs`
- `RunningSumConfig<F, WINDOW_NUM_BITS>` (lines 48-53)
- `configure` (lines 70-99) with the "range check" gate
- `copy_decompose` (lines 121-133) → `decompose` (lines 139-205), `strict = true`

Decomposes a field element `α` into `numWindows` windows of `W` bits each via a running
sum: `z_0 = α` (copied in), `z_{i+1} = (z_i − k_i)/2^W`, each word
`k_i = z_i − 2^W·z_{i+1}` range-checked to `W` bits by the degree-`2^W` "range check"
gate, and (strict mode — the `mul_fixed` instantiation) the final `z_numWindows`
constrained to `0` via `constrain_constant`.

The gate is registered on the `q_range_check` selector that `configure` receives from the
parent; `mul_fixed::Config::configure` registers its "Running sum coordinates check" gate
on the SAME selector (`mul_fixed.rs:115-129`), so enabling a running-sum row fires both.
In the Halo2-Clean model each gate object is enabled explicitly: `copy_decompose` enables
the range-check gate per row (Rust `decompose`, lines 161-164), and the parent's
`assign_fixed_constants` enables the coords gate per row (`mul_fixed.rs:216`) — matching
Rust's two `enable` calls per row one-for-one.

The mirror of `LookupRangeCheck.rangeCheck` (the lookup-based running sum): same loop
skeleton, but the word bound comes from the range-check *gate* instead of a table lookup,
and the whole `zs` vector is exposed (the `mul_fixed` coords rows and the
`base_field_elem` canonicity check consume interior running sums). -/

namespace Zcash.Circuits.DecomposeRunningSum

open Halo2
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Utilities.RunningSum (rangeCheckPoly rangeCheckValues InRange
  rangeCheckPoly_eq_zero_iff)

/-- Rust `RunningSumConfig<F, WINDOW_NUM_BITS>` (lines 48-53): the shared `q_range_check`
selector and the running-sum advice column `z`. -/
structure Config where
  qRangeCheck : Selector
  z : Column .advice

/-- The running-sum column registered for equality by `configure`. -/
@[keygen_norm]
def permutationColumns (config : Config) : List AnyColumn := [config.z]

/-! ## The "range check" gate -/

/-- Rust `utilities.rs::range_check(word, range)` (lines 170-174), the exact halo2 AST:
`(1..range).fold(word, |acc, i| acc * (Constant(i) − word))`. -/
@[selector_free, query_correct]
def rangeCheckExpr (range : ℕ) (word : Expression Fp Query) : Expression Fp Query :=
  ((List.range range).drop 1).foldl
    (fun acc (i : ℕ) => acc * (Expression.const (i : Fp) - word)) word

private theorem eval_foldl_rangeCheck (l : List ℕ) (acc word : Expression Fp Query)
    (f : Query → Fp) :
    (l.foldl (fun a (i : ℕ) => a * (Expression.const (i : Fp) - word)) acc).eval f
      = l.foldl (fun a (i : ℕ) => a * ((i : Fp) - word.eval f)) (acc.eval f) := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    simp [circuit_norm]

/-- The donor's `rangeCheckValues` in plain `List.map` form. -/
private theorem rangeCheckValues_eq (range : ℕ) :
    rangeCheckValues (F := Fp) range
      = ((List.range range).drop 1).map (fun i : ℕ => (i : Fp)) := by
  simp [rangeCheckValues, List.map_eq_flatMap]

/-- `rangeCheckExpr` evaluates to the donor's `rangeCheckPoly` of the evaluated word —
the bridge to the `InRange` machinery (`Utilities.RunningSum`). -/
theorem eval_rangeCheckExpr (range : ℕ) (word : Expression Fp Query) (f : Query → Fp) :
    (rangeCheckExpr range word).eval f = rangeCheckPoly range (word.eval f) := by
  unfold rangeCheckExpr rangeCheckPoly
  rw [rangeCheckValues_eq, List.foldl_map, eval_foldl_rangeCheck]

/-- Membership in `(List.range range).drop 1`: exactly `1 ≤ i < range`. -/
private theorem mem_range_drop_one {i range : ℕ} :
    i ∈ (List.range range).drop 1 ↔ 1 ≤ i ∧ i < range := by
  rcases Nat.eq_zero_or_pos range with h0 | hpos
  · subst h0; simp
  · rw [List.range_eq_range', List.drop_range']
    simp only [List.mem_range']
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨i - 1, by omega, by omega⟩

/-- `InRange` in existential-natural form (no field-cast injectivity needed in either
direction). -/
theorem inRange_iff_exists_lt (range : ℕ) (hrange : 0 < range) (word : Fp) :
    InRange range word ↔ ∃ k : ℕ, k < range ∧ word = (k : Fp) := by
  unfold InRange
  rw [rangeCheckValues_eq]
  constructor
  · rintro (h0 | ⟨i, hmem, hword⟩)
    · exact ⟨0, hrange, by simpa using h0⟩
    · simp only [List.mem_map] at hmem
      obtain ⟨k, hk, rfl⟩ := hmem
      exact ⟨k, (mem_range_drop_one.mp hk).2, hword⟩
  · rintro ⟨k, hk, hword⟩
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact Or.inl (by simp [hword, h0])
    · refine Or.inr ⟨(k : Fp), ?_, hword⟩
      simp only [List.mem_map]
      exact ⟨k, mem_range_drop_one.mpr ⟨hpos, hk⟩, rfl⟩

/-- The "range check" gate (`decompose_running_sum.rs:86-96`): on `q_range_check`, the
running word `z_cur − z_next·2^W` is `range_check`ed to `[0, 2^W)`. The word AST matches
Rust: `z_cur - z_next * F::from(1 << W)` (constant scale on the right). -/
def rangeCheckGate (W : ℕ) (cfg : Config) : Gate Fp :=
  let zCur : Expression Fp Query := queryAdvice cfg.z 0
  let zNext : Expression Fp Query := queryAdvice cfg.z 1
  let word := zCur - zNext * (((2 ^ W : ℕ) : Fp) : Expression Fp Query)
  Gate.withSelector "range check" cfg.qRangeCheck
    [zCur, zNext]
    [("range check", rangeCheckExpr (2 ^ W) word)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem rangeCheckGate_selector (W : ℕ) (cfg : Config) :
    (rangeCheckGate W cfg).selector = cfg.qRangeCheck := rfl

/-- Rust `RunningSumConfig::configure` (lines 70-99): equality on `z`, register the
range-check gate on the given selector. -/
def configure (W : ℕ) (qRangeCheck : Selector) (z : Column .advice) :
    Configure Fp Config := do
  enableEquality z
  let cfg : Config := { qRangeCheck, z }
  createGate (rangeCheckGate W cfg)
  return cfg

instance (W : ℕ) (qRangeCheck : Selector) (z : Column .advice) :
    ElaboratedConfigure (configure W qRangeCheck z) := by
  unfold configure
  infer_instance

/-! ## The `copy_decompose` gadget (strict) -/

/-- Input: the field element `α` to decompose (already assigned; `copy_decompose`). -/
structure Inputs (F : Type) where
  alpha : F
deriving ProvableStruct

/-- Output: the whole running sum `[z_0, …, z_numWindows]` (Rust `RunningSum<F>`).
Interior values are consumed by `mul_fixed`'s coords rows and `base_field_elem`'s
canonicity check. -/
structure Output (n : ℕ) (F : Type) where
  zs : Vector F n
deriving ProvableStruct

/-- The honest running-sum witness at window `idx`: `z_idx = α ≫ (W·idx)`, as a witgen
program over the `α` cell (the `LookupRangeCheck.zWitness` spelling). -/
def zWitness (W idx : ℕ) (alpha : AssignedCell Fp) : WitgenIR Fp 1 :=
  .ofFExpr (.ofNat (.div (.val (.expr alpha)) (.const (2 ^ (W * idx)))))

/-- The selector-enable loop (Rust `decompose` lines 161-164): the range-check gate on
every window row. A named def (not inline `forRange'`) so the constraints/witness chunks
stay folded through `circuit_proof_start` (the `LookupRangeCheck.rangeCheckLoop`
pattern). -/
def enableLoop (W : ℕ) (cfg : Config) (offset numWindows : ℕ) : RegionCircuit Fp Unit :=
  RegionCircuit.forRange' offset 1 numWindows (fun _ row =>
    (rangeCheckGate W cfg).enable row)

/-- The running-sum assignment loop (Rust `decompose` lines 166-196): `z_{idx+1}` at row
`offset + idx + 1`, honestly `α ≫ (W·(idx+1))`. -/
def assignLoop (W : ℕ) (cfg : Config) (alpha : AssignedCell Fp) (offset numWindows : ℕ) :
    RegionCircuit Fp Unit :=
  RegionCircuit.forRange' offset 1 numWindows (fun idx row => do
    let _z ← assignAdvice cfg.z (row + 1) (zWitness W (idx + 1) alpha)
    return ())

@[keygen_norm]
theorem enableLoop_copyCellsAssignedFrom (W : ℕ) (cfg : Config)
    (offset numWindows : ℕ) (self : RegionIndex) (available : List Cell) :
    ((enableLoop W cfg offset numWindows).operations self).CopyCellsAssignedFrom
      self available := by
  unfold enableLoop
  apply RegionCircuit.forRange'_copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
  intro i
  simp only [circuit_norm, RegionOperation.copiedCells, List.Forall]

@[keygen_norm]
theorem assignLoop_copyCellsAssignedFrom (W : ℕ) (cfg : Config)
    (alpha : AssignedCell Fp) (offset numWindows : ℕ) (self : RegionIndex)
    (available : List Cell) :
    ((assignLoop W cfg alpha offset numWindows).operations self).CopyCellsAssignedFrom
      self available := by
  unfold assignLoop
  apply RegionCircuit.forRange'_copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
  intro i
  simp only [circuit_norm, RegionOperation.copiedCells, List.Forall]

@[keygen_norm]
theorem finalCell_mem_assignLoop_assignedCellsAfter (W : ℕ) (cfg : Config)
    (alpha : AssignedCell Fp) (offset numWindows : ℕ) (self : RegionIndex)
    (available : List Cell)
    (hinitial : Cell.of self offset cfg.z ∈ available) :
    Cell.of self (offset + numWindows) cfg.z ∈
      ((assignLoop W cfg alpha offset numWindows).operations self).assignedCellsAfter
        self available := by
  rw [RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  cases numWindows with
  | zero =>
      exact Or.inl (by simpa using hinitial)
  | succ n =>
      right
      unfold assignLoop RegionCircuit.forRange'
      rw [RegionCircuit.loopAux_operations_succ]
      simp only [RegionOperations.assignedCells, List.flatMap_append, List.mem_append]
      right
      simp only [circuit_norm, RegionOperation.assignedCells,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton,
        Nat.mul_one]
      rw [Nat.add_assoc]

/-- Strict running-sum synthesis, factored so the reduced elaboration and semantic bundle
share one named operation program. -/
def body (W numWindows : ℕ) (cfg : Config) (offset : ℕ)
    (input : Inputs (AssignedCell Fp)) :
    RegionCircuit Fp (Output (numWindows + 1) (AssignedCell Fp)) := do
  let _z0 ← copyAdvice input.alpha cfg.z offset
  enableLoop W cfg offset numWindows
  assignLoop W cfg input.alpha offset numWindows
  let zLast ← cellAt cfg.z (offset + numWindows)
  constrainConstant zLast (0 : Fp)
  let zs ← cellVec cfg.z (fun j => offset + j) (numWindows + 1)
  return { zs }

def enableLoopSynthesisSummary (cfg : Config)
    (offset numWindows : ℕ) : FloorPlanner.RegionSynthesisSummary :=
  .repeatColumns [.selector cfg.qRangeCheck.index]
    offset 1 1 0 numWindows

theorem enableLoopSynthesisSummary_eq (W : ℕ) (cfg : Config)
    (offset numWindows : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((enableLoop W cfg offset numWindows).operations self) =
      enableLoopSynthesisSummary cfg offset numWindows := by
  symm
  unfold enableLoop enableLoopSynthesisSummary
  rw [RegionCircuit.forRange'_regionSynthesisSummary]
  rw [← FloorPlanner.RegionSynthesisSummary.foldr_ofColumns_eq_repeatColumns]
  apply congrArg (List.foldr FloorPlanner.RegionSynthesisSummary.combine {})
  apply congrArg List.ofFn
  funext i
  simp only [circuit_norm, rangeCheckGate_selector, Nat.mul_one]

def assignLoopSynthesisSummary (cfg : Config) (offset numWindows : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .repeatColumns [.column .advice cfg.z.index]
    offset 1 2 0 numWindows

theorem assignLoopSynthesisSummary_eq (W : ℕ) (cfg : Config)
    (alpha : AssignedCell Fp) (offset numWindows : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((assignLoop W cfg alpha offset numWindows).operations self) =
      assignLoopSynthesisSummary cfg offset numWindows := by
  symm
  unfold assignLoop assignLoopSynthesisSummary
  rw [RegionCircuit.forRange'_regionSynthesisSummary]
  rw [← FloorPlanner.RegionSynthesisSummary.foldr_ofColumns_eq_repeatColumns]
  apply congrArg (List.foldr FloorPlanner.RegionSynthesisSummary.combine {})
  apply congrArg List.ofFn
  funext i
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [circuit_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_columns]
  · simp only [circuit_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount, Nat.mul_one]
  · simp only [circuit_norm,
      FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]
  · simp only [circuit_norm, synthesis_summary_norm]

def copyDecomposeSynthesisSummary (numWindows : ℕ) (cfg : Config)
    (offset : ℕ) : FloorPlanner.RegionSynthesisSummary :=
  (FloorPlanner.RegionSynthesisSummary.ofColumns
      [.column .advice cfg.z.index] (offset + 1) 0).combine
    ((enableLoopSynthesisSummary cfg offset numWindows).combine
      ((assignLoopSynthesisSummary cfg offset numWindows).combine
        (FloorPlanner.RegionSynthesisSummary.ofColumns [] 0 1)))

@[synthesis_summary_norm]
theorem copyDecomposeSynthesisSummary_instanceRowExtent_eq
    (numWindows : ℕ) (cfg : Config) (offset : ℕ) :
    (copyDecomposeSynthesisSummary numWindows cfg offset).instanceRowExtent = 0 := by
  simp only [copyDecomposeSynthesisSummary, enableLoopSynthesisSummary,
    assignLoopSynthesisSummary, synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem copyDecomposeSynthesisSummary_constantSiteCount
    (numWindows : ℕ) (cfg : Config) (offset : ℕ) :
    (copyDecomposeSynthesisSummary numWindows cfg offset).constantSiteCount = 1 := by
  simp only [copyDecomposeSynthesisSummary,
    FloorPlanner.RegionSynthesisSummary.combine_constantSiteCount,
    FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount,
    FloorPlanner.RegionSynthesisSummary.repeatColumns_constantSiteCount,
    enableLoopSynthesisSummary, assignLoopSynthesisSummary, Nat.mul_zero,
    Nat.zero_add]

/-! ## Chain arithmetic

The backward-chain lemma: a running-sum chain with `W`-bit words ending at `0` holds
exactly the shifts of a `W·n`-bit value. Self-contained ℕ/field arithmetic (the
`copyDecompose` counterpart of `LookupRangeCheck`'s `chain_telescope`, strengthened to
pin every interior sum, which `mul_fixed`'s coords rows and `base_field_elem`'s
canonicity check read). -/

/-- The tail value at position `w` of a digit sequence: `∑_{j < n−w} ks (w+j)·2^{W·j}`. -/
private def tailVal (W n : ℕ) (ks : ℕ → ℕ) (w : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n - w), ks (w + j) * 2 ^ (W * j)

private theorem tailVal_last (W n : ℕ) (ks : ℕ → ℕ) : tailVal W n ks n = 0 := by
  simp [tailVal]

/-- Peel: `tailVal w = ks w + 2^W · tailVal (w+1)` for `w < n`. -/
private theorem tailVal_step (W n : ℕ) (ks : ℕ → ℕ) {w : ℕ} (hw : w < n) :
    tailVal W n ks w = ks w + 2 ^ W * tailVal W n ks (w + 1) := by
  unfold tailVal
  rw [show n - w = (n - (w + 1)) + 1 from by omega, Finset.sum_range_succ',
    Finset.mul_sum]
  simp only [Nat.mul_zero, pow_zero, Nat.mul_one, Nat.add_zero]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show w + (j + 1) = w + 1 + j from by omega]
  ring

private theorem tailVal_lt (W n : ℕ) (ks : ℕ → ℕ) (hks : ∀ i, i < n → ks i < 2 ^ W) :
    ∀ d w, w + d = n → tailVal W n ks w < 2 ^ (W * (n - w))
  | 0, w, hw => by
    rw [show w = n from by omega, tailVal_last]
    simp
  | d + 1, w, hw => by
    have ih := tailVal_lt W n ks hks d (w + 1) (by omega)
    have hk := hks w (by omega)
    have h2W : 0 < 2 ^ W := Nat.two_pow_pos W
    rw [tailVal_step W n ks (by omega : w < n),
      show n - w = (n - (w + 1)) + 1 from by omega, Nat.mul_succ, pow_add]
    calc ks w + 2 ^ W * tailVal W n ks (w + 1)
        < 2 ^ W * (tailVal W n ks (w + 1) + 1) := by
          have := Nat.mul_le_mul_left (2 ^ W) (Nat.zero_le (tailVal W n ks (w + 1)))
          nlinarith
      _ ≤ 2 ^ W * 2 ^ (W * (n - (w + 1))) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (W * (n - (w + 1))) * 2 ^ W := by ring

/-- Forward shift: `tailVal w = tailVal 0 / 2^{W·w}`. -/
private theorem tailVal_shift (W n : ℕ) (ks : ℕ → ℕ) (hks : ∀ i, i < n → ks i < 2 ^ W) :
    ∀ w, w ≤ n → tailVal W n ks w = tailVal W n ks 0 / 2 ^ (W * w) := by
  intro w
  induction w with
  | zero => simp
  | succ v ih =>
    intro hv
    have hvn : v < n := by omega
    have hv' := ih (by omega)
    have hstep := tailVal_step W n ks hvn
    have hk := hks v hvn
    -- tailVal (v+1) = tailVal v / 2^W
    have hdiv : tailVal W n ks (v + 1) = tailVal W n ks v / 2 ^ W := by
      rw [hstep, Nat.add_mul_div_left _ _ (Nat.two_pow_pos W),
        Nat.div_eq_of_lt hk]
      omega
    rw [hdiv, hv', Nat.div_div_eq_div_mul, ← pow_add]
    ring_nf

/-- **The backward-chain lemma.** A field chain `f` with `W`-bit words
(`f i = 2^W·f (i+1) + k_i`, `k_i < 2^W`) and `f n = 0` holds the shifts of a single
`W·n`-bit value `V`: `f w = ↑(V / 2^{W·w})` for all `w ≤ n`. -/
theorem chain_shifts (W n : ℕ) (f : ℕ → Fp)
    (hwords : ∀ i, i < n → ∃ k : ℕ, k < 2 ^ W ∧ f i = 2 ^ W * f (i + 1) + (k : Fp))
    (hlast : f n = 0) :
    ∃ V : ℕ, V < 2 ^ (W * n) ∧ ∀ w, w ≤ n → f w = ((V / 2 ^ (W * w) : ℕ) : Fp) := by
  choose ks hks hchain using hwords
  -- totalize the digit choice (only indices < n are read)
  set ks' : ℕ → ℕ := fun i => if h : i < n then ks i h else 0 with hks'
  have hks'lt : ∀ i, i < n → ks' i < 2 ^ W := fun i hi => by
    simp only [hks', dif_pos hi]; exact hks i hi
  refine ⟨tailVal W n ks' 0, by simpa using tailVal_lt W n ks' hks'lt n 0 (by omega), ?_⟩
  -- `f w = ↑(tailVal w)` by downward induction, then the shift lemma
  suffices hfw : ∀ d w, w + d = n → f w = ((tailVal W n ks' w : ℕ) : Fp) by
    intro w hw
    rw [hfw (n - w) w (by omega), tailVal_shift W n ks' hks'lt w hw]
  intro d
  induction d with
  | zero =>
    intro w hw
    rw [show w = n from by omega, tailVal_last, hlast, Nat.cast_zero]
  | succ e ih =>
    intro w hw
    have hwn : w < n := by omega
    rw [hchain w hwn, ih (w + 1) (by omega), tailVal_step W n ks' hwn]
    push_cast [hks', dif_pos hwn]
    ring

/-- The word of consecutive shift values is the base-`2^W` digit:
`↑(V/2^{W·w}) − ↑(V/2^{W·(w+1)})·2^W = ↑(V/2^{W·w} mod 2^W)` — how a consumer of
`copyDecompose`'s Spec reads the window value off two adjacent running sums (e.g. the
`mul_fixed` coords rows). -/
theorem shift_word_eq (W V w : ℕ) :
    ((V / 2 ^ (W * w) : ℕ) : Fp) - ((V / 2 ^ (W * (w + 1)) : ℕ) : Fp) * 2 ^ W
      = ((V / 2 ^ (W * w) % 2 ^ W : ℕ) : Fp) := by
  have hsplit : V / 2 ^ (W * (w + 1)) = V / 2 ^ (W * w) / 2 ^ W := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    ring_nf
  have hmoddiv : (2 ^ W * (V / 2 ^ (W * w) / 2 ^ W) + V / 2 ^ (W * w) % 2 ^ W : ℕ)
      = V / 2 ^ (W * w) := Nat.div_add_mod _ (2 ^ W)
  have hcast := congrArg (Nat.cast (R := Fp)) hmoddiv
  push_cast at hcast ⊢
  rw [hsplit]
  linear_combination -hcast

@[implicit_reducible]
def elaborated (W numWindows : ℕ) :
    ElaboratedRegionCircuit Fp (Selector × Column .advice) Config Inputs
      (Output (numWindows + 1))
      (fun (q, z) => configure W q z) (body W numWindows) :=
  { keygenRequirements :=
      { inputCells _ _ input := [input.alpha.cell] }
    synthesisSummary cfg offset _ _ :=
      copyDecomposeSynthesisSummary numWindows cfg offset
    synthesisSummary_eq := by
      intro cfg offset input self
      unfold copyDecomposeSynthesisSummary
      apply FloorPlanner.RegionSynthesisSummary.ext
      · simp only [body, circuit_norm, enableLoopSynthesisSummary_eq,
          assignLoopSynthesisSummary_eq,
          FloorPlanner.RegionSynthesisSummary.ofColumns_columns,
          FloorPlanner.unionColumns_nil_right,
          FloorPlanner.unionColumns_assoc]
      · simp only [body, circuit_norm, enableLoopSynthesisSummary_eq,
          assignLoopSynthesisSummary_eq,
          FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount,
          Nat.max_zero]
      · simp only [body, circuit_norm, enableLoopSynthesisSummary_eq,
          assignLoopSynthesisSummary_eq,
          FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount]
      · simp only [body, circuit_norm, enableLoopSynthesisSummary_eq,
          assignLoopSynthesisSummary_eq, synthesis_summary_norm]
    registered := by keygen_registration [configure, enableEquality, body]
    copyCellsAssigned := by
      keygen_registration [body]
      apply finalCell_mem_assignLoop_assignedCellsAfter
      apply RegionOperations.mem_assignedCellsAfter_of_mem
      simp
    output cfg offset _ self :=
      { zs := Vector.ofFn fun j => AssignedCell.of self (offset + j) cfg.z }
    output_eq := by
      intro cfg offset input self
      simp only [body, circuit_norm] }

/-- Strict `copy_decompose` (`decompose_running_sum.rs:121-133, 139-205`): copy `α` in as
`z_0`, enable the range-check gate on all `numWindows` rows, assign the interior running
sums, and constrain the final `z_numWindows` to `0`.

Spec (semantic contract): `α` is (a representative of) a `W·numWindows`-bit value `V`,
and every running sum holds the corresponding shift `⌊V / 2^{W·w}⌋`. Note `V` is only
unique modulo the field size when `2^{W·numWindows}` exceeds it (the `mul_fixed` case:
`2^255 > p`) — canonicity is exactly what `base_field_elem`'s canonicity gate adds. -/
def copyDecompose (W numWindows : ℕ) :
    FormalRegionCircuit Fp (Selector × Column .advice) Config Inputs (Output (numWindows + 1)) where
  configure := fun (q, z) => configure W q z
  synthesize := body W numWindows
  elaborated := elaborated W numWindows

  Assumptions _ := True

  Spec input out _ :=
    ∃ V : ℕ, V < 2 ^ (W * numWindows) ∧ input.alpha = (V : Fp) ∧
      ∀ w : Fin (numWindows + 1), out.zs[w.val] = ((V / 2 ^ (W * w.val) : ℕ) : Fp)

  -- honest-prover precondition: `α` genuinely fits in `W·numWindows` bits (the strict
  -- assertion is only satisfiable then). At the `mul_fixed` instantiation
  -- (`W·numWindows = 255`) this is automatic from `p < 2^255`.
  ProverAssumptions input _ _ := input.alpha.val < 2 ^ (W * numWindows)

  ProverSpec input out _ _ :=
    ∀ w : Fin (numWindows + 1),
      out.zs[w.val] = ((input.alpha.val / 2 ^ (W * w.val) : ℕ) : Fp)

  soundness := by
    circuit_proof_start [body]
    obtain ⟨hCopy, hEnables, hLast⟩ := hc
    simp only [enableLoop, rangeCheckGate, circuit_norm, mul_one, one_mul] at hEnables
    simp only [assignLoop, circuit_norm] at hLast
    -- the running sum read off the env
    set f : ℕ → Fp := fun j =>
      env.advice cfg.z ((place self + (offset + j) : ℕ) : ℤ) with hf
    have hwords : ∀ i, i < numWindows →
        ∃ k : ℕ, k < 2 ^ W ∧ f i = 2 ^ W * f (i + 1) + (k : Fp) := by
      intro i hi
      have h := hEnables ⟨i, hi⟩
      rw [eval_rangeCheckExpr, rangeCheckPoly_eq_zero_iff,
        inRange_iff_exists_lt _ (Nat.two_pow_pos W)] at h
      obtain ⟨k, hk, hkeq⟩ := h
      simp only [circuit_norm] at hkeq
      refine ⟨k, hk, ?_⟩
      simp only [hf]
      rw [show offset + (i + 1) = offset + i + 1 from by omega]
      push_cast at hkeq ⊢
      linear_combination hkeq
    have hlast : f numWindows = 0 := hLast
    obtain ⟨V, hV, hshifts⟩ := chain_shifts W numWindows f hwords hlast
    refine ⟨V, hV, ?_, fun w => ?_⟩
    · have h0 := hshifts 0 (by omega)
      simp only [hf, Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_zero] at h0
      rw [← hCopy]
      exact h0
    · rw [← h_output_zs w.val w.isLt]
      exact hshifts w.val (by omega)

  completeness := by
    circuit_proof_start [body]
    obtain ⟨hCopyWit, _hEnableWit, hAssignWit⟩ := hwit
    simp only [assignLoop, circuit_norm, zWitness, mul_one] at hAssignWit
    -- the honest z-chain: `z_j = ↑(α.val ≫ (W·j))`
    have hz : ∀ j, j ≤ numWindows →
        env.advice cfg.z ((place self + (offset + j) : ℕ) : ℤ)
          = ((input_alpha.val / 2 ^ (W * j) : ℕ) : Fp) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp only [Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_zero]
        rw [hCopyWit, ZMod.natCast_zmod_val]
      · have h := hAssignWit ⟨j - 1, by omega⟩
        simp only [h_input] at h
        rw [show offset + (j - 1) + 1 = offset + j from by omega,
          show W * (j - 1 + 1) = W * j from by rw [Nat.sub_add_cancel hjpos]] at h
        exact h
    simp only [assignLoop, circuit_norm]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- the range-check gate holds on every row: the honest word is `↑(b % 2^W)`
      simp only [enableLoop, rangeCheckGate, circuit_norm, mul_one, one_mul]
      intro i
      rw [eval_rangeCheckExpr, rangeCheckPoly_eq_zero_iff,
        inRange_iff_exists_lt _ (Nat.two_pow_pos W)]
      simp only [circuit_norm]
      set b := input_alpha.val / 2 ^ (W * i.val) with hb
      refine ⟨b % 2 ^ W, Nat.mod_lt _ (Nat.two_pow_pos W), ?_⟩
      have hzi := hz i.val (by omega)
      have hzi1 := hz (i.val + 1) (by omega)
      have hsplit : input_alpha.val / 2 ^ (W * (i.val + 1)) = b / 2 ^ W := by
        rw [hb, Nat.div_div_eq_div_mul, ← pow_add]
        ring_nf
      have hmoddiv : (2 ^ W * (b / 2 ^ W) + b % 2 ^ W : ℕ) = b :=
        Nat.div_add_mod b (2 ^ W)
      have hcast := congrArg (Nat.cast (R := Fp)) hmoddiv
      rw [hsplit] at hzi1
      rw [show offset + (↑i + 1) = offset + ↑i + 1 from by omega] at hzi1
      push_cast at hzi hzi1 hcast ⊢
      rw [hzi, hzi1, ← hb]
      linear_combination -hcast
    · -- strict tail: `z_last = ↑(α.val / 2^{W·n}) = 0` since `α.val < 2^{W·n}`
      rw [hz numWindows le_rfl, Nat.div_eq_of_lt hPA, Nat.cast_zero]
    · -- ProverSpec: the honest shifts
      intro w
      rw [← h_output_zs w.val w.isLt]
      exact hz w.val (by omega)

@[synthesis_summary_norm]
theorem copyDecompose_synthesisSummary_eq (W numWindows : ℕ) (cfg : Config)
    (offset : ℕ) (input : Var Inputs Fp) (self : RegionIndex) :
    (copyDecompose W numWindows).elaborated.synthesisSummary
        cfg offset input self =
      copyDecomposeSynthesisSummary numWindows cfg offset := rfl

/-- Strict decomposition has exactly one deferred constant allocation: its final
running-sum cell is constrained to zero. -/
@[synthesis_summary_norm]
theorem copyDecompose_synthesisSummary_constantSiteCount
    (W numWindows : ℕ) (config : Config) (offset : ℕ)
    (input : Inputs (AssignedCell Fp)) (region : RegionIndex) :
    ((copyDecompose W numWindows).elaborated.synthesisSummary
      config offset input region).constantSiteCount = 1 := by
  simpa only [copyDecompose] using
    copyDecomposeSynthesisSummary_constantSiteCount numWindows config offset

/-- Strict decomposition never writes a fixed column. -/
@[synthesis_summary_norm]
theorem copyDecompose_synthesisSummary_hasNoFixedColumns
    (W numWindows : ℕ) (config : Config) (offset : ℕ)
    (input : Inputs (AssignedCell Fp)) (region : RegionIndex) :
    ((copyDecompose W numWindows).elaborated.synthesisSummary
      config offset input region).HasNoFixedColumns := by
  rw [copyDecompose_synthesisSummary_eq]
  simp only [copyDecomposeSynthesisSummary,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_combine,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_repeatColumns,
    enableLoopSynthesisSummary, assignLoopSynthesisSummary]
  simp

/-- Strict decomposition registers no fixed columns. -/
@[keygen_norm]
theorem copyDecompose_configured_fixedColumns_eq_nil
    (W numWindows : ℕ) {config : Config}
    (configured : (copyDecompose W numWindows).Configured config) :
    configured.fixedColumns = [] := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [FormalRegionCircuit.Configured.fixedColumns]
  constructor

/-- The strict decomposition config registers exactly its running-sum column for equality. -/
@[keygen_norm]
theorem copyDecompose_configured_permutationColumns_eq
    (W numWindows : ℕ) {config : Config}
    (configured : (copyDecompose W numWindows).Configured config) :
    configured.permutationColumns = permutationColumns config := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [keygen_norm, FormalRegionCircuit.Configured.permutationColumns,
    FormalRegionCircuit.keygenRequirements, ElaboratedRegionCircuit.keygenRequirements,
    copyDecompose, configure, permutationColumns, List.singleton_append]

/-- The strict decomposition's only input copy comes from `alpha`. -/
@[keygen_norm]
theorem copyDecompose_configured_inputCells_eq
    (W numWindows : ℕ) {config : Config}
    (configured : (copyDecompose W numWindows).Configured config)
    (input : Var Inputs Fp) :
    configured.inputCells input = [input.alpha.cell] := by
  rfl

/-- The strict decomposition's input therefore requires equality on `alpha`'s column. -/
@[keygen_norm]
theorem copyDecompose_configured_inputPermutationColumns_eq
    (W numWindows : ℕ) {config : Config}
    (configured : (copyDecompose W numWindows).Configured config)
    (input : Var Inputs Fp) :
    configured.inputPermutationColumns input = [input.alpha.cell.column] := by
  rfl

/-- The bundle's output variable (rfl — the `loop_output` pattern): the whole running-sum
cell vector at rows `offset + j`. Keeps parents' output projections lazy (no whnf through
the symbolic loops). -/
@[circuit_norm]
theorem copyDecompose_output (W numWindows : ℕ) (cfg : Config) (o : ℕ)
    (input : Inputs (AssignedCell Fp)) (self : RegionIndex) :
    (copyDecompose W numWindows).output cfg o input self
      = { zs := Vector.ofFn (fun j => AssignedCell.of self (o + j) cfg.z) } := rfl

end Zcash.Circuits.DecomposeRunningSum
