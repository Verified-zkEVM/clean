import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.MulFixed.Theorems
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.AddIncomplete
import Clean.Ironwood.Utilities.DecomposeRunningSum

/-!
The shared core of fixed-base scalar multiplication (`H = 8`, 3-bit windows): `[scalar]B` for a
fixed base `B`, by decomposing the scalar into 3-bit windows. Per window, the window point's `x`
is interpolated by a degree-7 Lagrange polynomial in the window value over 8 fixed columns, its
`y` sign is fixed by `u² = y_p + z`, and the accumulator advances by incomplete addition; the most
significant window uses complete addition. The `full_width` / `short` / `base_field_elem` wrappers
compose this core.

`coords_check` is the per-window-row constraint: the interpolated `x_p`, the `u² = y_p + z` sign
fix, and the curve equation. It is registered on the running sum's own range-check selector, so
enabling a running-sum row fires both the range check and the coordinates check.

Reference: `halo2_gadgets/src/ecc/chip/mul_fixed.rs`.
-/

namespace Zcash.Circuits.Ecc.MulFixed

open Halo2
open Ecc.MulFixed (CoordsParams interpolate FixedBase windowPoint windowScalar)
open DecomposeRunningSum (copyDecompose)

/-- The window size, `H = 2^3`. -/
def H : ℕ := 8

/-- The number of windows in a full-width decomposition. -/
def NUM_WINDOWS : ℕ := 85

/-- The fixed-base data a synthesize needs (no invariants): the per-window fixed-column values,
and the window tables feeding the witness programs. `FixedBase` (data + the halo2 out-of-circuit
invariants) lowers to this via `toData`; proof-free consumers (the VK layout tests, which only
need concrete `params` values in the keygen view) construct it directly from dumped tables. -/
structure FixedBaseData where
  -- Per-window Lagrange-coefficient and z fixed-column values.
  params : ℕ → CoordsParams Fp
  -- The base's generator point.
  point : Point Fp
  -- Per-window, per-index u square roots (u² = y_p + z).
  u : ℕ → ℕ → Fp

/-- The data of a proven fixed base. -/
def FixedBase.toData (B : FixedBase) : FixedBaseData :=
  { params := B.params, point := B.point, u := B.u }

/-! ## Config -/

structure Config where
  -- The running-sum config for decomposing the scalar into windows.
  runningSumConfig : DecomposeRunningSum.Config
  -- The fixed Lagrange interpolation coefficients for `x_p`.
  lagrangeCoeffs : Fin 8 → Column .fixed
  -- The fixed `z` for each window such that `y + z = u²`.
  fixedZ : Column .fixed
  -- Decomposition of an `n − 1`-bit scalar into `k`-bit windows:
  -- `a = a_0 + 2^k·a_1 + 2^{2k}·a_2 + … + 2^{(n−1)k}·a_{n−1}`.
  window : Column .advice
  -- `u` such that `u² = y_p + z`.
  u : Column .advice
  -- Configuration for `add`.
  addConfig : Add.Config
  -- Configuration for `add_incomplete`.
  addIncompleteConfig : AddIncomplete.Config

/-- Fixed columns written by the per-window constants loader. -/
def fixedColumns (cfg : Config) : List (Column .fixed) :=
  List.ofFn cfg.lagrangeCoeffs ++ [cfg.fixedZ]

@[keygen_norm]
theorem lagrangeCoeffs_mem_fixedColumns (cfg : Config) (i : Fin 8) :
    cfg.lagrangeCoeffs i ∈ fixedColumns cfg := by
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

@[keygen_norm]
theorem fixedZ_mem_fixedColumns (cfg : Config) :
    cfg.fixedZ ∈ fixedColumns cfg := by
  simp [fixedColumns]

/-- The logical fixed-column roles used by fixed-base multiplication are
pairwise distinct. -/
structure Config.FixedColumnsLawful (config : Config) : Type where
  nodup : (fixedColumns config).Nodup

/-! ## The "Running sum coordinates check" gate -/

/-- `window_pow[k] = (0..k).fold(Const 1, |acc,_| acc * window)` — the exact Rust AST: `1`,
`1·w`, `(1·w)·w`, …. -/
@[selector_free, query_correct]
def windowPow (word : Expression Fp Query) (k : ℕ) : Expression Fp Query :=
  (List.range k).foldl (fun acc _ => acc * word) (Expression.const 1)

/-- The interpolated `x_p`: fold from `Const 0`, `acc + window_pow[k] · lagrange_coeffs[k]` — the
8-iteration fold written out (identical AST; keeps the eval bridge fold-free). -/
@[selector_free, query_correct]
def interpolatedX (cfg : Config) (word : Expression Fp Query) : Expression Fp Query :=
  Expression.const 0
    + windowPow word 0 * queryFixed (cfg.lagrangeCoeffs 0)
    + windowPow word 1 * queryFixed (cfg.lagrangeCoeffs 1)
    + windowPow word 2 * queryFixed (cfg.lagrangeCoeffs 2)
    + windowPow word 3 * queryFixed (cfg.lagrangeCoeffs 3)
    + windowPow word 4 * queryFixed (cfg.lagrangeCoeffs 4)
    + windowPow word 5 * queryFixed (cfg.lagrangeCoeffs 5)
    + windowPow word 6 * queryFixed (cfg.lagrangeCoeffs 6)
    + windowPow word 7 * queryFixed (cfg.lagrangeCoeffs 7)

/-- The shared per-window-row constraint list over a given window-value expression. Reads
`x_p`/`y_p` on the add config's columns at `cur`, `u` at `cur`, `fixed_z` and the 8 Lagrange
columns as rotation-0 fixed queries. Used by BOTH the running-sum coords gate (word = `z_cur −
z_next·8`) and the full-width gate (word = the raw `window` query). -/
@[selector_free, query_correct]
def coordsCheck (cfg : Config) (word : Expression Fp Query) :
    List (String × Expression Fp Query) :=
  let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP 0
  let xP : Expression Fp Query := queryAdvice cfg.addConfig.xP 0
  let z : Expression Fp Query := queryFixed cfg.fixedZ
  let u : Expression Fp Query := queryAdvice cfg.u 0
  -- check x: interpolated_x − x_p
  let xCheck := interpolatedX cfg word - xP
  -- check y: u² − y_p − z
  let yCheck := u * u - yP - z
  -- on-curve: y_p² − x_p²·x_p − b
  let onCurve := yP * yP - xP * xP * xP - (pallasB : Expression Fp Query)
  [("check x", xCheck), ("check y", yCheck), ("on-curve", onCurve)]

/-- The "Running sum coordinates check" gate, registered on the running sum's `q_range_check`
selector. The window value is derived: `word = z_cur − z_next·8` (constant scale on the
right). -/
def coordsGate (cfg : Config) : Gate Fp :=
  -- window cur/next first (word derivation), then `coords_check`'s atoms (y_p, x_p, the
  -- fixed `z`, u) and finally the eight Lagrange-coeff fixed queries from `interpolated_x`.
  Gate.withSelector "Running sum coordinates check" cfg.runningSumConfig.qRangeCheck
    [ queryAdvice cfg.window 0, queryAdvice cfg.window 1,
      queryAdvice cfg.addConfig.yP 0, queryAdvice cfg.addConfig.xP 0,
      queryFixed cfg.fixedZ, queryAdvice cfg.u 0,
      queryFixed (cfg.lagrangeCoeffs 0), queryFixed (cfg.lagrangeCoeffs 1),
      queryFixed (cfg.lagrangeCoeffs 2), queryFixed (cfg.lagrangeCoeffs 3),
      queryFixed (cfg.lagrangeCoeffs 4), queryFixed (cfg.lagrangeCoeffs 5),
      queryFixed (cfg.lagrangeCoeffs 6), queryFixed (cfg.lagrangeCoeffs 7) ] <|
    let zCur : Expression Fp Query := queryAdvice cfg.window 0
    let zNext : Expression Fp Query := queryAdvice cfg.window 1
    let word := zCur - zNext * (((H : ℕ) : Fp) : Expression Fp Query)
    coordsCheck cfg word

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem coordsGate_selector (cfg : Config) :
    (coordsGate cfg).selector = cfg.runningSumConfig.qRangeCheck := rfl

/-- The `CoordsParams` read off the environment's fixed cells at a given row — what the
coords gate's queries see. -/
def readParams (cfg : Config) (f : Query → Fp) : CoordsParams Fp where
  z := f (.fixed cfg.fixedZ 0)
  lagrange0 := f (.fixed (cfg.lagrangeCoeffs 0) 0)
  lagrange1 := f (.fixed (cfg.lagrangeCoeffs 1) 0)
  lagrange2 := f (.fixed (cfg.lagrangeCoeffs 2) 0)
  lagrange3 := f (.fixed (cfg.lagrangeCoeffs 3) 0)
  lagrange4 := f (.fixed (cfg.lagrangeCoeffs 4) 0)
  lagrange5 := f (.fixed (cfg.lagrangeCoeffs 5) 0)
  lagrange6 := f (.fixed (cfg.lagrangeCoeffs 6) 0)
  lagrange7 := f (.fixed (cfg.lagrangeCoeffs 7) 0)

/-- `interpolatedX` evaluates to `interpolate` over the read-back params — the bridge from the
gate AST to the coordinate algebra. -/
theorem eval_interpolatedX (cfg : Config) (word : Expression Fp Query) (f : Query → Fp) :
    (interpolatedX cfg word).eval f
      = Ecc.MulFixed.interpolate (readParams cfg f) (word.eval f) := by
  simp only [interpolatedX, windowPow, queryFixed, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil,
    circuit_norm, Ecc.MulFixed.interpolate, readParams]

/-- `interpolate` only depends on the params componentwise — the bridge from the
`readParams` cell reads to a known `CoordsParams` value. -/
theorem interpolate_congr_params {p q : CoordsParams Fp}
    (h0 : p.lagrange0 = q.lagrange0) (h1 : p.lagrange1 = q.lagrange1)
    (h2 : p.lagrange2 = q.lagrange2) (h3 : p.lagrange3 = q.lagrange3)
    (h4 : p.lagrange4 = q.lagrange4) (h5 : p.lagrange5 = q.lagrange5)
    (h6 : p.lagrange6 = q.lagrange6) (h7 : p.lagrange7 = q.lagrange7) (w : Fp) :
    Ecc.MulFixed.interpolate p w = Ecc.MulFixed.interpolate q w := by
  unfold Ecc.MulFixed.interpolate
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- Equality on `window` and `u`, a fresh selector for the running-sum config (whose `configure`
registers the "range check" gate and re-enables equality on `window` — a dedup no-op), a fresh
`fixed_z` column, then the coords gate on the same selector. The cross-config column identities
Rust asserts (`add.x_p = add_incomplete.x_p` etc.) hold by construction at the call site
(`EccChip::configure` hands both configs the same columns). -/
def configure (lagrangeCoeffs : Fin 8 → Column .fixed) (window u : Column .advice)
    (addConfig : Add.Config) (addIncompleteConfig : AddIncomplete.Config) :
    Configure Fp Config := do
  enableEquality window
  enableEquality u
  let qRunningSum ← selector
  let runningSumConfig ← DecomposeRunningSum.configure 3 qRunningSum window
  let fixedZ ← fixedColumn
  let cfg : Config :=
    { runningSumConfig, lagrangeCoeffs, fixedZ, window, u, addConfig, addIncompleteConfig }
  createGate (coordsGate cfg)
  return cfg

@[keygen_norm]
theorem configure_output_fixedZ_index
    (lagrangeCoeffs : Fin 8 → Column .fixed) (window u : Column .advice)
    (addConfig : Add.Config) (addIncompleteConfig : AddIncomplete.Config)
    (counts : ConfigureCounts) :
    ((configure lagrangeCoeffs window u addConfig addIncompleteConfig).output
      counts).fixedZ.index = counts.numFixedColumns := by
  simp [configure, DecomposeRunningSum.configure]

def configureOutputFixedColumnsLawful
    (lagrangeCoeffs : Fin 8 → Column .fixed) (window u : Column .advice)
    (addConfig : Add.Config) (addIncompleteConfig : AddIncomplete.Config)
    (counts : ConfigureCounts)
    (hnodup : (List.ofFn lagrangeCoeffs).Nodup)
    (hbound : ∀ column ∈ List.ofFn lagrangeCoeffs,
      column.index < counts.numFixedColumns) :
    Config.FixedColumnsLawful
      ((configure lagrangeCoeffs window u addConfig addIncompleteConfig).output
        counts) := by
  constructor
  simp only [fixedColumns, List.nodup_append]
  refine ⟨hnodup, List.nodup_singleton _, ?_⟩
  intro column hcolumn fixed hfixed
  simp only [List.mem_singleton] at hfixed
  subst fixed
  have hcolumn' : column ∈ List.ofFn lagrangeCoeffs := by
    simpa [configure] using hcolumn
  have hlt := hbound _ hcolumn'
  intro heq
  have := congrArg Column.index heq
  simp only [configure_output_fixedZ_index] at this
  omega

instance (lagrangeCoeffs : Fin 8 → Column .fixed) (window u : Column .advice)
    (addConfig : Add.Config) (addIncompleteConfig : AddIncomplete.Config) :
    ElaboratedConfigure
      (configure lagrangeCoeffs window u addConfig addIncompleteConfig) := by
  unfold configure
  infer_instance

/-! ## Shared keygen requirements -/

/-- The incomplete-addition gate already present in a shared fixed-base config. -/
def incompleteAddGate (cfg : Config) : Gate Fp :=
  let add := cfg.addIncompleteConfig
  AddIncomplete.gate add.qAddIncomplete add.xP add.yP add.xQR add.yQR

/-- The complete-addition gate already present in a shared fixed-base config. -/
def completeAddGate (cfg : Config) : Gate Fp :=
  let add := cfg.addConfig
  Add.gate add.qAdd add.lambda add.xP add.yP add.xQR add.yQR
    add.alpha add.beta add.gamma add.delta

/--
Arguments borrowed by the running-sum fixed-base inner regions: the range and coordinate
gates registered by `MulFixed.configure`, plus the shared incomplete-addition gate.
-/
@[keygen_norm]
def runningSumKeygenRequirements : KeygenRequirements Fp Config Unit where
  configLawful cfg := AddIncomplete.add.Configured cfg.addIncompleteConfig
  gates cfg configured :=
    [DecomposeRunningSum.rangeCheckGate 3 cfg.runningSumConfig, coordsGate cfg] ++
      configured.gates
  lookups _ configured := configured.lookups
  permutationColumns cfg _ :=
    DecomposeRunningSum.permutationColumns cfg.runningSumConfig ++
      ([cfg.window] : List AnyColumn) ++
        ([cfg.u] : List AnyColumn) ++
          Add.permutationColumns cfg.addConfig ++
            AddIncomplete.permutationColumns cfg.addIncompleteConfig

@[keygen_norm]
theorem configure_output_runningSumPermutationColumns
    (lagrangeCoeffs : Fin 8 → Column .fixed) (window u : Column .advice)
    (addConfig : Add.Config) (addIncompleteConfig : AddIncomplete.Config)
    (counts : ConfigureCounts)
    (configured : runningSumKeygenRequirements.configLawful
      ((configure lagrangeCoeffs window u addConfig addIncompleteConfig).output counts)) :
    runningSumKeygenRequirements.permutationColumns
        ((configure lagrangeCoeffs window u addConfig addIncompleteConfig).output counts)
        configured =
      ([window, window, u] : List AnyColumn) ++
        Add.permutationColumns addConfig ++
          AddIncomplete.permutationColumns addIncompleteConfig := by
  simp [runningSumKeygenRequirements, configure,
    DecomposeRunningSum.permutationColumns, DecomposeRunningSum.configure]

/-! ## Region-relative synthesize pieces

Offset-generic `RegionCircuit`s; the wrapper bundles compose them inside one region. -/

/-- The `k = ⌊α/8^w⌋ mod 8` window value of the scalar cell, inside a witness closure. -/
def windowVal (env : Placed ProverEnvironment Fp) (alpha : AssignedCell Fp) (w : ℕ) : ℕ :=
  (readCell env alpha).val / 8 ^ w % 8

/-- Witness program for `x_p` of window `w`: the window-table point's x-coordinate at the
scalar's window value. The 8 candidate coordinates are precomputed per window (from the base's
own scalar-kind-specific window formula — hence the table parameter `tbl`: `windowPoint point`
for the 85-window kinds, `Short.windowPoint point` for short). -/
def xPWit (tbl : ℕ → ℕ → Point Fp) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (tbl w k.val).x)[windowVal env alpha w]!)]

/-- Witness program for `y_p` of window `w`. -/
def yPWit (tbl : ℕ → ℕ → Point Fp) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (tbl w k.val).y)[windowVal env alpha w]!)]

/-- Witness program for `u` of window `w`: `u² = y_p + z`. -/
def uWit (B : FixedBaseData) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => B.u w k.val)[windowVal env alpha w]!)]

/-- One window row: enable the coords-check toggle gate (the coords gate for the running-sum
wrappers, the full-width gate for `full_width`), then the 8 Lagrange coefficients and the `z`
value into the fixed columns. -/
def fixedConstantsWindow (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config) (w row : ℕ) :
    RegionCircuit Fp Unit := do
  toggle.enable row
  let p := B.params w
  let _ ← assignFixed (cfg.lagrangeCoeffs 0) row p.lagrange0
  let _ ← assignFixed (cfg.lagrangeCoeffs 1) row p.lagrange1
  let _ ← assignFixed (cfg.lagrangeCoeffs 2) row p.lagrange2
  let _ ← assignFixed (cfg.lagrangeCoeffs 3) row p.lagrange3
  let _ ← assignFixed (cfg.lagrangeCoeffs 4) row p.lagrange4
  let _ ← assignFixed (cfg.lagrangeCoeffs 5) row p.lagrange5
  let _ ← assignFixed (cfg.lagrangeCoeffs 6) row p.lagrange6
  let _ ← assignFixed (cfg.lagrangeCoeffs 7) row p.lagrange7
  let _ ← assignFixed cfg.fixedZ row p.z
  return ()

private def fixedConstantAssignments (B : FixedBaseData) (cfg : Config)
    (w : ℕ) : List (Column .fixed × Fp) :=
  let p := B.params w
  [(cfg.lagrangeCoeffs 0, p.lagrange0),
    (cfg.lagrangeCoeffs 1, p.lagrange1),
    (cfg.lagrangeCoeffs 2, p.lagrange2),
    (cfg.lagrangeCoeffs 3, p.lagrange3),
    (cfg.lagrangeCoeffs 4, p.lagrange4),
    (cfg.lagrangeCoeffs 5, p.lagrange5),
    (cfg.lagrangeCoeffs 6, p.lagrange6),
    (cfg.lagrangeCoeffs 7, p.lagrange7),
    (cfg.fixedZ, p.z)]

private theorem value_eq_of_map_fst_nodup
    {pairs : List (Column .fixed × Fp)}
    (hnodup : (pairs.map Prod.fst).Nodup)
    {column : Column .fixed} {left right : Fp}
    (hleft : (column, left) ∈ pairs) (hright : (column, right) ∈ pairs) :
    left = right := by
  induction pairs with
  | nil => simp at hleft
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright
      · exact congrArg Prod.snd (hleft.trans hright.symm)
      · have hmem : column ∈ tail.map Prod.fst := List.mem_map_of_mem hright
        have heq := congrArg Prod.fst hleft
        exact False.elim (hnodup.1 (heq ▸ hmem))
      · have hmem : column ∈ tail.map Prod.fst := List.mem_map_of_mem hleft
        have heq := congrArg Prod.fst hright
        exact False.elim (hnodup.1 (heq ▸ hmem))
      · exact ih hnodup.2 hleft hright

/-- The per-window fixed columns and coords-toggle enables, one row per window, before any
advice assignment. -/
def fixedConstantsLoop (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (offset numWindows : ℕ) : RegionCircuit Fp Unit :=
  RegionCircuit.forRange' offset 1 numWindows
    (fun w row => fixedConstantsWindow toggle B cfg w row)

theorem fixedConstantsWindow_assignFixed_row
    (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (w base : ℕ) (self : RegionIndex) (column : Column .fixed)
    (row : ℕ) (value : Fp)
    (hassignment : .assignFixed column row value ∈
      (fixedConstantsWindow toggle B cfg w base).operations self) :
    row = base := by
  simp only [fixedConstantsWindow, circuit_norm, List.mem_cons,
    List.not_mem_nil, or_false] at hassignment
  aesop

theorem fixedConstantsWindow_fixedAssignmentsAgree
    (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (hlawful : cfg.FixedColumnsLawful) (w row : ℕ)
    (self : RegionIndex) :
    ((fixedConstantsWindow toggle B cfg w row).operations self)
      |>.FixedAssignmentsAgree := by
  unfold RegionOperations.FixedAssignmentsAgree
  intro column assignmentRow left right hleft hright
  have hleft' : (column, left) ∈ fixedConstantAssignments B cfg w := by
    simp [fixedConstantsWindow, circuit_norm] at hleft
    simp only [fixedConstantAssignments, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq]
    aesop
  have hright' : (column, right) ∈ fixedConstantAssignments B cfg w := by
    simp [fixedConstantsWindow, circuit_norm] at hright
    simp only [fixedConstantAssignments, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq]
    aesop
  have hcolumns :
      (fixedConstantAssignments B cfg w).map Prod.fst = fixedColumns cfg := by
    rfl
  apply value_eq_of_map_fst_nodup (hcolumns ▸ hlawful.nodup) hleft' hright'

theorem fixedConstantsLoop_fixedAssignmentsAgree
    (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (hlawful : cfg.FixedColumnsLawful) (offset numWindows : ℕ)
    (self : RegionIndex) :
    ((fixedConstantsLoop toggle B cfg offset numWindows).operations self)
      |>.FixedAssignmentsAgree := by
  apply RegionCircuit.forRange'_fixedAssignmentsAgree
  · intro i
    exact fixedConstantsWindow_fixedAssignmentsAgree
      toggle B cfg hlawful i.val (offset + i.val * 1) self
  · intro i column row value hassignment
    exact fixedConstantsWindow_assignFixed_row
      toggle B cfg i.val (offset + i.val * 1) self column row value hassignment

/-- Reduced footprint of one fixed-table row. -/
def fixedConstantsWindowSynthesisSummary
    (toggle : Gate Fp) (cfg : Config) (row : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  (FloorPlanner.RegionSynthesisSummary.ofColumns
    [.selector toggle.selector.index,
      .column .fixed (cfg.lagrangeCoeffs 0).index,
      .column .fixed (cfg.lagrangeCoeffs 1).index,
      .column .fixed (cfg.lagrangeCoeffs 2).index,
      .column .fixed (cfg.lagrangeCoeffs 3).index,
      .column .fixed (cfg.lagrangeCoeffs 4).index,
      .column .fixed (cfg.lagrangeCoeffs 5).index,
      .column .fixed (cfg.lagrangeCoeffs 6).index,
      .column .fixed (cfg.lagrangeCoeffs 7).index,
      .column .fixed cfg.fixedZ.index]
    (row + 1) 0).withSelectorActivations [(toggle.selector.index, row)]

/-- Reduced footprint of the fixed-table loop, composed from its row summaries. -/
def fixedConstantsLoopSynthesisSummary
    (toggle : Gate Fp) (cfg : Config) (offset numWindows : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .repeatColumnsWithSelector toggle.selector.index
    [.selector toggle.selector.index,
      .column .fixed (cfg.lagrangeCoeffs 0).index,
      .column .fixed (cfg.lagrangeCoeffs 1).index,
      .column .fixed (cfg.lagrangeCoeffs 2).index,
      .column .fixed (cfg.lagrangeCoeffs 3).index,
      .column .fixed (cfg.lagrangeCoeffs 4).index,
      .column .fixed (cfg.lagrangeCoeffs 5).index,
      .column .fixed (cfg.lagrangeCoeffs 6).index,
      .column .fixed (cfg.lagrangeCoeffs 7).index,
      .column .fixed cfg.fixedZ.index]
    offset 1 1 0 numWindows

@[synthesis_summary_norm]
theorem fixedConstantsLoopSynthesisSummary_lookupActivationCount
    (toggle : Gate Fp) (cfg : Config) (offset numWindows : ℕ) :
    (fixedConstantsLoopSynthesisSummary toggle cfg offset numWindows).lookupActivationCount = 0 := by
  simp only [fixedConstantsLoopSynthesisSummary, synthesis_summary_norm,
    Nat.mul_zero]

@[synthesis_summary_norm]
theorem fixedConstantsLoopSynthesisSummary_instanceRowExtent_eq
    (toggle : Gate Fp) (cfg : Config) (offset numWindows : ℕ) :
    (fixedConstantsLoopSynthesisSummary toggle cfg offset numWindows).instanceRowExtent = 0 := by
  simp only [fixedConstantsLoopSynthesisSummary, synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem fixedConstantsWindow_synthesisSummary_eq
    (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (w row : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((fixedConstantsWindow toggle B cfg w row).operations self) =
      fixedConstantsWindowSynthesisSummary toggle cfg row := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [fixedConstantsWindowSynthesisSummary, fixedConstantsWindow,
      circuit_norm]
  · simp only [fixedConstantsWindowSynthesisSummary, fixedConstantsWindow,
      circuit_norm]
    omega
  · simp only [fixedConstantsWindowSynthesisSummary, fixedConstantsWindow,
      circuit_norm]
  · simp only [fixedConstantsWindowSynthesisSummary, fixedConstantsWindow,
      circuit_norm, synthesis_summary_norm]
  · simp only [fixedConstantsWindowSynthesisSummary, fixedConstantsWindow,
      circuit_norm, synthesis_summary_norm]
  · simp only [fixedConstantsWindowSynthesisSummary, fixedConstantsWindow,
      circuit_norm, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem fixedConstantsLoop_synthesisSummary_eq
    (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (offset numWindows : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((fixedConstantsLoop toggle B cfg offset numWindows).operations self) =
      fixedConstantsLoopSynthesisSummary toggle cfg offset numWindows := by
  unfold fixedConstantsLoopSynthesisSummary
  simp only [fixedConstantsLoop, fixedConstantsWindowSynthesisSummary,
    RegionCircuit.forRange'_regionSynthesisSummary, synthesis_summary_norm,
    Nat.mul_one]
  simpa [Nat.add_assoc] using
    (FloorPlanner.RegionSynthesisSummary.foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector
      toggle.selector.index
      [.selector toggle.selector.index,
        .column .fixed (cfg.lagrangeCoeffs 0).index,
        .column .fixed (cfg.lagrangeCoeffs 1).index,
        .column .fixed (cfg.lagrangeCoeffs 2).index,
        .column .fixed (cfg.lagrangeCoeffs 3).index,
        .column .fixed (cfg.lagrangeCoeffs 4).index,
        .column .fixed (cfg.lagrangeCoeffs 5).index,
        .column .fixed (cfg.lagrangeCoeffs 6).index,
        .column .fixed (cfg.lagrangeCoeffs 7).index,
        .column .fixed cfg.fixedZ.index]
      offset 1 1 0 numWindows)

@[synthesis_summary_norm]
theorem fixedConstantsLoopSynthesisSummary_constantSiteCount
    (toggle : Gate Fp) (cfg : Config) (offset numWindows : ℕ) :
    (fixedConstantsLoopSynthesisSummary toggle cfg offset
      numWindows).constantSiteCount = 0 := by
  cases numWindows <;> rfl

@[keygen_norm, keygen_helper]
theorem fixedConstantsLoop_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {targetFixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (offset numWindows : ℕ) (self : RegionIndex)
    (htoggle : toggle ∈ gates)
    (hfixedColumns : ∀ column ∈ fixedColumns cfg,
      column ∈ targetFixedColumns) :
    ((fixedConstantsLoop toggle B cfg offset numWindows).operations self).Forall
      (RegionOperation.KeygenRegistered gates lookups targetFixedColumns
        permutationColumns) := by
  have hlagrange (i : Fin 8) : cfg.lagrangeCoeffs i ∈ targetFixedColumns :=
    hfixedColumns _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hfixedZ : cfg.fixedZ ∈ targetFixedColumns :=
    hfixedColumns _ (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [fixedConstantsLoop, RegionCircuit.forRange'_forall]
  intro i
  unfold fixedConstantsWindow
  keygen_registration

/-- Fixed-table loading assigns cells and selectors but introduces no copy endpoints. -/
@[keygen_norm, keygen_helper]
theorem fixedConstantsLoop_copyCellsAssignedFrom
    (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (offset numWindows : ℕ) (self : RegionIndex) (available : List Cell) :
    ((fixedConstantsLoop toggle B cfg offset numWindows).operations self)
      |>.CopyCellsAssignedFrom self available := by
  apply RegionCircuit.forRange'_copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
  intro i
  unfold fixedConstantsWindow
  keygen_registration

/-- Assigning the per-window fixed data requests no deferred constants. -/
@[synthesis_summary_norm]
theorem fixedConstantsLoop_synthesisSummary_constantSiteCount
    (toggle : Gate Fp) (B : FixedBaseData) (config : Config)
    (offset numWindows : ℕ) (region : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((fixedConstantsLoop toggle B config offset numWindows).operations
        region)).constantSiteCount = 0 := by
  apply FloorPlanner.regionSynthesisSummary_constantSiteCount_eq_zero_of_forall
  simp only [fixedConstantsLoop, RegionCircuit.forRange'_forall]
  intro i
  simp only [fixedConstantsWindow, circuit_norm]

/-- Witness `[window_scalar]B`'s coordinates into the add config's `x_p`/`y_p` at the window row,
and the `u` value. Returns the window-point cells. -/
def processWindow (B : FixedBaseData) (tbl : ℕ → ℕ → Point Fp) (cfg : Config)
    (alpha : AssignedCell Fp) (w row : ℕ) :
    RegionCircuit Fp (Point (AssignedCell Fp)) := do
  let x ← assignAdvice cfg.addConfig.xP row (xPWit tbl alpha w)
  let y ← assignAdvice cfg.addConfig.yP row (yPWit tbl alpha w)
  let _u ← assignAdvice cfg.u row (uWit B alpha w)
  return { x, y }

/-- Reduced footprint of one fixed-base window witness. -/
def processWindowSynthesisSummary (cfg : Config) (row : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.column .advice cfg.addConfig.xP.index,
      .column .advice cfg.addConfig.yP.index,
      .column .advice cfg.u.index]
    (row + 1) 0

def windowStepColumns (cfg : Config) : List FloorPlanner.RegionColumn :=
  [.column .advice cfg.addConfig.xP.index,
    .column .advice cfg.addConfig.yP.index,
    .column .advice cfg.u.index,
    .selector cfg.addIncompleteConfig.qAddIncomplete.index,
    .column .advice cfg.addIncompleteConfig.xP.index,
    .column .advice cfg.addIncompleteConfig.yP.index,
    .column .advice cfg.addIncompleteConfig.xQR.index,
    .column .advice cfg.addIncompleteConfig.yQR.index,
    .column .advice cfg.addIncompleteConfig.xQR.index,
    .column .advice cfg.addIncompleteConfig.yQR.index]

def windowStepSynthesisSummary (cfg : Config) (row : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  (FloorPlanner.RegionSynthesisSummary.ofColumns
    (windowStepColumns cfg) (row + 2) 0).withSelectorActivations
      [(cfg.addIncompleteConfig.qAddIncomplete.index, row)]

@[synthesis_summary_norm]
theorem processWindow_combine_addIncomplete_synthesisSummary
    (cfg : Config) (row : ℕ) :
    (processWindowSynthesisSummary cfg row).combine
        (AddIncomplete.synthesisSummary cfg.addIncompleteConfig row) =
      windowStepSynthesisSummary cfg row := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp [processWindowSynthesisSummary, AddIncomplete.synthesisSummary,
      windowStepSynthesisSummary, windowStepColumns, synthesis_summary_norm]
  · simp only [processWindowSynthesisSummary, AddIncomplete.synthesisSummary,
      windowStepSynthesisSummary,
      FloorPlanner.RegionSynthesisSummary.combine_rowCount,
      FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount,
      FloorPlanner.RegionSynthesisSummary.withSelectorActivations_rowCount]
    omega
  · simp only [processWindowSynthesisSummary, AddIncomplete.synthesisSummary,
      windowStepSynthesisSummary,
      FloorPlanner.RegionSynthesisSummary.combine_constantSiteCount,
      FloorPlanner.RegionSynthesisSummary.ofColumns_constantSiteCount,
      FloorPlanner.RegionSynthesisSummary.withSelectorActivations_constantSiteCount,
      Nat.zero_add]
  · simp only [processWindowSynthesisSummary, AddIncomplete.synthesisSummary,
      windowStepSynthesisSummary, synthesis_summary_norm]
  · simp only [processWindowSynthesisSummary, AddIncomplete.synthesisSummary,
      windowStepSynthesisSummary, synthesis_summary_norm]
  · simp only [processWindowSynthesisSummary, AddIncomplete.synthesisSummary,
      windowStepSynthesisSummary,
      FloorPlanner.RegionSynthesisSummary.combine_selectorActivations,
      FloorPlanner.RegionSynthesisSummary.withSelectorActivations_selectorActivations,
      FloorPlanner.RegionSynthesisSummary.ofColumns_selectorActivations,
      List.nil_append]

@[synthesis_summary_norm]
theorem reduced_windowStep_synthesisSummary (cfg : Config) (row : ℕ) :
    (FloorPlanner.RegionSynthesisSummary.ofColumns
        ([.column .advice cfg.addConfig.xP.index,
          .column .advice cfg.addConfig.yP.index,
          .column .advice cfg.u.index] ++
        [.selector cfg.addIncompleteConfig.qAddIncomplete.index,
          .column .advice cfg.addIncompleteConfig.xP.index,
          .column .advice cfg.addIncompleteConfig.yP.index,
          .column .advice cfg.addIncompleteConfig.xQR.index,
          .column .advice cfg.addIncompleteConfig.yQR.index,
          .column .advice cfg.addIncompleteConfig.xQR.index,
          .column .advice cfg.addIncompleteConfig.yQR.index])
        (max (row + 1) (row + 2)) (0 + 0)).withSelectorActivations
          [(cfg.addIncompleteConfig.qAddIncomplete.index, row)] =
      windowStepSynthesisSummary cfg row := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · rfl
  · simp only [windowStepSynthesisSummary,
      FloorPlanner.RegionSynthesisSummary.withSelectorActivations_rowCount,
      FloorPlanner.RegionSynthesisSummary.ofColumns_rowCount]
    omega
  · rfl
  · simp only [windowStepSynthesisSummary,
      FloorPlanner.RegionSynthesisSummary.withSelectorActivations_instanceRowExtent,
      FloorPlanner.RegionSynthesisSummary.ofColumns_instanceRowExtent]
  · rfl
  · rfl

@[synthesis_summary_norm]
theorem processWindow_synthesisSummary_eq
    (B : FixedBaseData) (tbl : ℕ → ℕ → Point Fp) (cfg : Config)
    (alpha : AssignedCell Fp) (w row : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((processWindow B tbl cfg alpha w row).operations self) =
      processWindowSynthesisSummary cfg row := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [processWindowSynthesisSummary, processWindow, circuit_norm]
  · simp only [processWindowSynthesisSummary, processWindow, circuit_norm]
    omega
  · simp only [processWindowSynthesisSummary, processWindow, circuit_norm]
  · simp only [processWindowSynthesisSummary, processWindow, circuit_norm,
      synthesis_summary_norm]
  · simp only [processWindowSynthesisSummary, processWindow, circuit_norm,
      synthesis_summary_norm]
  · simp only [processWindowSynthesisSummary, processWindow, circuit_norm,
      synthesis_summary_norm]

@[keygen_norm, keygen_output_norm]
theorem processWindow_output_x_column (B : FixedBaseData)
    (table : ℕ → ℕ → Point Fp) (cfg : Config) (alpha : AssignedCell Fp)
    (w row : ℕ) (self : RegionIndex) :
    ((processWindow B table cfg alpha w row).output self).x.cell.column =
      cfg.addConfig.xP := by
  simp only [processWindow, circuit_norm]

@[keygen_norm, keygen_output_norm]
theorem processWindow_output_y_column (B : FixedBaseData)
    (table : ℕ → ℕ → Point Fp) (cfg : Config) (alpha : AssignedCell Fp)
    (w row : ℕ) (self : RegionIndex) :
    ((processWindow B table cfg alpha w row).output self).y.cell.column =
      cfg.addConfig.yP := by
  simp only [processWindow, circuit_norm]

/-- A window witness only assigns cells; it introduces no copy endpoints. -/
@[keygen_norm, keygen_helper]
theorem processWindow_copyCellsAssignedFrom (B : FixedBaseData)
    (table : ℕ → ℕ → Point Fp) (cfg : Config) (alpha : AssignedCell Fp)
    (w row : ℕ) (self : RegionIndex) (available : List Cell) :
    ((processWindow B table cfg alpha w row).operations self)
      |>.CopyCellsAssignedFrom self available := by
  simp only [processWindow, circuit_norm, keygen_norm, keygen_spine]

/-- Both coordinates returned by a window witness were assigned by that witness. -/
theorem processWindow_output_cells_assigned (B : FixedBaseData)
    (table : ℕ → ℕ → Point Fp) (cfg : Config) (alpha : AssignedCell Fp)
    (w row : ℕ) (self : RegionIndex) (available : List Cell) :
    let output := (processWindow B table cfg alpha w row).output self
    output.x.cell ∈
        ((processWindow B table cfg alpha w row).operations self
          |>.assignedCellsAfter self available) ∧
      output.y.cell ∈
        ((processWindow B table cfg alpha w row).operations self
          |>.assignedCellsAfter self available) := by
  simp only [processWindow, circuit_norm, AssignedCell.of_cell,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  constructor <;> right <;>
    simp only [RegionOperations.assignedCells, List.flatMap_cons,
      RegionOperation.assignedCells, List.singleton_append,
      List.flatMap_nil, List.mem_cons, true_or, or_true]

/-- One serial middle-window step: witness the next table point, then add it to the
accumulator written by the preceding step. -/
abbrev windowChainStep (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (i row : ℕ) : RegionCircuit Fp Unit := do
  let mulB ← processW (i + 2) row
  let qx ← cellAt cfg.addIncompleteConfig.xQR row
  let qy ← cellAt cfg.addIncompleteConfig.yQR row
  let _ ← AddIncomplete.add.call cfg.addIncompleteConfig row
    ⟨mulB, { x := qx, y := qy }⟩
  return ()

/-- The shared window chain: `initialize_accumulator` (window 0), the incomplete-addition loop
over windows `1..numWindows−2` (window 1's accumulator q-copy is REAL — the window-0 point; later
windows' are self-copies of the previous round's output), and `process_msb` (window
`numWindows−1`, no addition). Generic over the per-window witness function (cell-scalar for the
running-sum wrappers, hint-driven for `full_width`). Returns `(acc, mul_b)`. -/
def windowChain (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (offset numWindows : ℕ) :
    RegionCircuit Fp (Point (AssignedCell Fp) × Point (AssignedCell Fp)) := do
  let acc0 ← processW 0 offset
  let mulB1 ← processW 1 (offset + 1)
  let _a1 ← AddIncomplete.add.call cfg.addIncompleteConfig (offset + 1) ⟨mulB1, acc0⟩
  RegionCircuit.forRange' (offset + 2) 1 (numWindows - 3)
    (windowChainStep cfg processW)
  let mulB ← processW (numWindows - 1) (offset + (numWindows - 1))
  let accX ← cellAt cfg.addIncompleteConfig.xQR (offset + (numWindows - 1))
  let accY ← cellAt cfg.addIncompleteConfig.yQR (offset + (numWindows - 1))
  return ({ x := accX, y := accY }, mulB)

private theorem windowChainStep_copyCellsAssignedFrom
    (cfg : Config) (hconfigured : AddIncomplete.add.Configured cfg.addIncompleteConfig)
    (self : RegionIndex)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (hprocess : ∀ w row available,
      ((processW w row).operations self).CopyCellsAssignedFrom self available)
    (hprocessOutput : ∀ w row available,
      let output := (processW w row).output self
      output.x.cell ∈
          ((processW w row).operations self).assignedCellsAfter self available ∧
        output.y.cell ∈
          ((processW w row).operations self).assignedCellsAfter self available)
    (i row : ℕ) (available : List Cell)
    (haccX : Cell.of self row cfg.addIncompleteConfig.xQR ∈ available)
    (haccY : Cell.of self row cfg.addIncompleteConfig.yQR ∈ available) :
    let operations := (windowChainStep cfg processW i row).operations self
    operations.CopyCellsAssignedFrom self available ∧
      Cell.of self (row + 1) cfg.addIncompleteConfig.xQR ∈
        operations.assignedCellsAfter self available ∧
      Cell.of self (row + 1) cfg.addIncompleteConfig.yQR ∈
        operations.assignedCellsAfter self available := by
  simp only [windowChainStep, circuit_norm]
  let processOperations := (processW (i + 2) row).operations self
  let processOutput := (processW (i + 2) row).output self
  let addInput : Var AddIncomplete.Inputs Fp :=
    ⟨processOutput,
      ⟨AssignedCell.of self row cfg.addIncompleteConfig.xQR,
        AssignedCell.of self row cfg.addIncompleteConfig.yQR⟩⟩
  let addOperations :=
    (AddIncomplete.add.call cfg.addIncompleteConfig row addInput).operations self
  have hprocessLaw := hprocess (i + 2) row available
  have hout := hprocessOutput (i + 2) row available
  have haddLaw : addOperations.CopyCellsAssignedFrom self
      (processOperations.assignedCellsAfter self available) := by
    apply AddIncomplete.add.call_copyCellsAssignedFrom
      cfg.addIncompleteConfig hconfigured row _ self
    intro cell hcell
    rw [AddIncomplete.Configured.inputCells_eq] at hcell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
    rcases hcell with rfl | rfl | rfl | rfl
    · exact hout.1
    · exact hout.2
    · exact RegionOperations.mem_assignedCellsAfter_of_mem _ _ _ _ haccX
    · exact RegionOperations.mem_assignedCellsAfter_of_mem _ _ _ _ haccY
  have haddOutput := AddIncomplete.add_output_cells_assigned
    cfg.addIncompleteConfig row addInput
      self (processOperations.assignedCellsAfter self available)
  refine ⟨?_, ?_, ?_⟩
  · rw [RegionOperations.copyCellsAssignedFrom_append_iff]
    exact ⟨hprocessLaw, haddLaw⟩
  · rw [RegionOperations.assignedCellsAfter_append]
    exact haddOutput.1
  · rw [RegionOperations.assignedCellsAfter_append]
    exact haddOutput.2

private theorem windowChainLoop_copyCellsAssignedFrom
    (cfg : Config) (hconfigured : AddIncomplete.add.Configured cfg.addIncompleteConfig)
    (self : RegionIndex)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (hprocess : ∀ w row available,
      ((processW w row).operations self).CopyCellsAssignedFrom self available)
    (hprocessOutput : ∀ w row available,
      let output := (processW w row).output self
      output.x.cell ∈
          ((processW w row).operations self).assignedCellsAfter self available ∧
        output.y.cell ∈
          ((processW w row).operations self).assignedCellsAfter self available)
    (offset k : ℕ) (available : List Cell)
    (haccX : Cell.of self (offset + 2) cfg.addIncompleteConfig.xQR ∈ available)
    (haccY : Cell.of self (offset + 2) cfg.addIncompleteConfig.yQR ∈ available) :
    RegionOperations.CopyCellsAssignedFrom self available
        ((RegionCircuit.loopAux (fun i => offset + 2 + i * 1)
          (windowChainStep cfg processW) k).operations self) ∧
      Cell.of self (offset + 2 + k) cfg.addIncompleteConfig.xQR ∈
        RegionOperations.assignedCellsAfter self available
          ((RegionCircuit.loopAux (fun i => offset + 2 + i * 1)
            (windowChainStep cfg processW) k).operations self) ∧
      Cell.of self (offset + 2 + k) cfg.addIncompleteConfig.yQR ∈
        RegionOperations.assignedCellsAfter self available
          ((RegionCircuit.loopAux (fun i => offset + 2 + i * 1)
            (windowChainStep cfg processW) k).operations self) := by
  induction k with
  | zero =>
      simp only [RegionCircuit.loopAux, circuit_norm, Nat.add_zero]
      exact ⟨RegionOperations.CopyCellsAssignedFrom.nil available,
        haccX, haccY⟩
  | succ k inductionHypothesis =>
      have hstep := windowChainStep_copyCellsAssignedFrom cfg hconfigured self
        processW hprocess hprocessOutput k (offset + 2 + k * 1)
        (RegionOperations.assignedCellsAfter self available
          ((RegionCircuit.loopAux (fun i => offset + 2 + i * 1)
            (windowChainStep cfg processW) k).operations self))
        (by simpa only [Nat.mul_one] using inductionHypothesis.2.1)
        (by simpa only [Nat.mul_one] using inductionHypothesis.2.2)
      rw [RegionCircuit.loopAux_operations_succ]
      refine ⟨?_, ?_, ?_⟩
      · rw [RegionOperations.copyCellsAssignedFrom_append_iff]
        exact ⟨inductionHypothesis.1, hstep.1⟩
      · rw [RegionOperations.assignedCellsAfter_append]
        simpa only [Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using hstep.2.1
      · rw [RegionOperations.assignedCellsAfter_append]
        simpa only [Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using hstep.2.2

/-- Copy endpoints in the shared window chain are assigned by the chain itself or
provided as input to its per-window witness program. -/
theorem windowChain_copyCellsAssignedFrom
    (cfg : Config) (hconfigured : AddIncomplete.add.Configured cfg.addIncompleteConfig)
    (self : RegionIndex)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (hprocess : ∀ w row available,
      ((processW w row).operations self).CopyCellsAssignedFrom self available)
    (hprocessOutput : ∀ w row available,
      let output := (processW w row).output self
      output.x.cell ∈
          ((processW w row).operations self).assignedCellsAfter self available ∧
        output.y.cell ∈
          ((processW w row).operations self).assignedCellsAfter self available)
    (offset numWindows : ℕ) (hnumWindows : 3 ≤ numWindows)
    (available : List Cell) :
    let chain := windowChain cfg processW offset numWindows
    (chain.operations self).CopyCellsAssignedFrom self available ∧
      (chain.output self).1.x.cell ∈
        (chain.operations self).assignedCellsAfter self available ∧
      (chain.output self).1.y.cell ∈
        (chain.operations self).assignedCellsAfter self available ∧
      (chain.output self).2.x.cell ∈
        (chain.operations self).assignedCellsAfter self available ∧
      (chain.output self).2.y.cell ∈
        (chain.operations self).assignedCellsAfter self available := by
  let op0 := (processW 0 offset).operations self
  let op1 := (processW 1 (offset + 1)).operations self
  let input : Var AddIncomplete.Inputs Fp :=
    ⟨(processW 1 (offset + 1)).output self,
      (processW 0 offset).output self⟩
  let addOps :=
    (AddIncomplete.add.call cfg.addIncompleteConfig (offset + 1) input).operations self
  let loopOps :=
    (RegionCircuit.forRange' (offset + 2) 1 (numWindows - 3)
      (windowChainStep cfg processW)).operations self
  let lastOps :=
    (processW (numWindows - 1) (offset + (numWindows - 1))).operations self
  have h0 := hprocess 0 offset available
  have hout0 := hprocessOutput 0 offset available
  have h1 := hprocess 1 (offset + 1) (op0.assignedCellsAfter self available)
  have hout1 := hprocessOutput 1 (offset + 1)
    (op0.assignedCellsAfter self available)
  have h01 : (op0 ++ op1).CopyCellsAssignedFrom self available := by
    rw [RegionOperations.copyCellsAssignedFrom_append_iff]
    exact ⟨h0, h1⟩
  have hadd : addOps.CopyCellsAssignedFrom self
      ((op0 ++ op1).assignedCellsAfter self available) := by
    apply AddIncomplete.add.call_copyCellsAssignedFrom
      cfg.addIncompleteConfig hconfigured (offset + 1) input self
    intro cell hcell
    rw [AddIncomplete.Configured.inputCells_eq] at hcell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
    rcases hcell with rfl | rfl | rfl | rfl
    · rw [RegionOperations.assignedCellsAfter_append]
      exact hout1.1
    · rw [RegionOperations.assignedCellsAfter_append]
      exact hout1.2
    · rw [RegionOperations.assignedCellsAfter_append]
      exact RegionOperations.mem_assignedCellsAfter_of_mem _ _ _ _ hout0.1
    · rw [RegionOperations.assignedCellsAfter_append]
      exact RegionOperations.mem_assignedCellsAfter_of_mem _ _ _ _ hout0.2
  have h01add : ((op0 ++ op1) ++ addOps).CopyCellsAssignedFrom self available := by
    rw [RegionOperations.copyCellsAssignedFrom_append_iff]
    exact ⟨h01, hadd⟩
  have haddOutput := AddIncomplete.add_output_cells_assigned
    cfg.addIncompleteConfig (offset + 1) input self
      ((op0 ++ op1).assignedCellsAfter self available)
  have hloop := windowChainLoop_copyCellsAssignedFrom cfg hconfigured self
    processW hprocess hprocessOutput offset (numWindows - 3)
    (((op0 ++ op1) ++ addOps).assignedCellsAfter self available)
    (by
      rw [RegionOperations.assignedCellsAfter_append]
      simpa only [Nat.add_assoc] using haddOutput.1)
    (by
      rw [RegionOperations.assignedCellsAfter_append]
      simpa only [Nat.add_assoc] using haddOutput.2)
  have hprefix : (((op0 ++ op1) ++ addOps) ++ loopOps)
      |>.CopyCellsAssignedFrom self available := by
    rw [RegionOperations.copyCellsAssignedFrom_append_iff]
    exact ⟨h01add, hloop.1⟩
  have hlast := hprocess (numWindows - 1) (offset + (numWindows - 1))
    ((((op0 ++ op1) ++ addOps) ++ loopOps).assignedCellsAfter self available)
  have hlastOutput := hprocessOutput
    (numWindows - 1) (offset + (numWindows - 1))
    ((((op0 ++ op1) ++ addOps) ++ loopOps).assignedCellsAfter self available)
  have hall : ((((op0 ++ op1) ++ addOps) ++ loopOps) ++ lastOps)
      |>.CopyCellsAssignedFrom self available := by
    rw [RegionOperations.copyCellsAssignedFrom_append_iff]
    exact ⟨hprefix, hlast⟩
  have hlastRow : offset + 2 + (numWindows - 3) =
      offset + (numWindows - 1) := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [windowChain, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure, operations_cellAt, List.append_nil,
      List.append_assoc] using hall
  · simp only [windowChain, circuit_norm, RegionOperations.assignedCellsAfter_append]
    apply RegionOperations.mem_assignedCellsAfter_of_mem
    rw [← hlastRow]
    simpa only [op0, op1, addOps, loopOps, RegionCircuit.forRange',
      RegionOperations.assignedCellsAfter_append, Nat.mul_one] using
      hloop.2.1
  · simp only [windowChain, circuit_norm, RegionOperations.assignedCellsAfter_append]
    apply RegionOperations.mem_assignedCellsAfter_of_mem
    rw [← hlastRow]
    simpa only [op0, op1, addOps, loopOps, RegionCircuit.forRange',
      RegionOperations.assignedCellsAfter_append, Nat.mul_one] using
      hloop.2.2
  · simpa only [windowChain, circuit_norm,
      RegionOperations.assignedCellsAfter_append] using hlastOutput.1
  · simpa only [windowChain, circuit_norm,
      RegionOperations.assignedCellsAfter_append] using hlastOutput.2

@[synthesis_summary_norm]
theorem windowChainStep_synthesisSummary_eq
    (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (i row : ℕ) (self : RegionIndex)
    (hprocess : FloorPlanner.regionSynthesisSummary
      ((processW (i + 2) row).operations self) =
        processWindowSynthesisSummary cfg row) :
    FloorPlanner.regionSynthesisSummary
        ((windowChainStep cfg processW i row).operations self) =
      windowStepSynthesisSummary cfg row := by
  simp only [windowChainStep, circuit_norm,
    FloorPlanner.regionSynthesisSummary_append, hprocess,
    synthesis_summary_norm]

@[synthesis_summary_norm]
theorem windowChainStep_synthesisSummary_constantSiteCount
    (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (i row : ℕ) (self : RegionIndex)
    (hprocess : (FloorPlanner.regionSynthesisSummary
      ((processW (i + 2) row).operations self)).constantSiteCount = 0) :
    (FloorPlanner.regionSynthesisSummary
      ((windowChainStep cfg processW i row).operations self)).constantSiteCount = 0 := by
  simp only [windowChainStep, circuit_norm,
    FloorPlanner.regionSynthesisSummary_append,
    FloorPlanner.RegionSynthesisSummary.combine_constantSiteCount,
    hprocess, Nat.zero_add]
  rw [← AddIncomplete.add.elaborated.synthesisSummary_eq,
    AddIncomplete.add_synthesisSummary_eq]
  exact AddIncomplete.synthesisSummary_constantSiteCount _ _

/-- Reduced footprint of the shared window chain. The caller supplies a window
witness whose footprint is `processWindowSynthesisSummary`. -/
def windowChainSynthesisSummary (cfg : Config)
    (offset numWindows : ℕ) : FloorPlanner.RegionSynthesisSummary :=
  (processWindowSynthesisSummary cfg offset).combine
    ((processWindowSynthesisSummary cfg (offset + 1)).combine
      ((AddIncomplete.synthesisSummary cfg.addIncompleteConfig (offset + 1)).combine
        ((FloorPlanner.RegionSynthesisSummary.repeatColumnsWithSelector
            cfg.addIncompleteConfig.qAddIncomplete.index
            (windowStepColumns cfg) (offset + 2) 1 2 0
              (numWindows - 3)).combine
          (processWindowSynthesisSummary cfg (offset + (numWindows - 1))))))

@[synthesis_summary_norm]
theorem windowChainSynthesisSummary_lookupActivationCount
    (cfg : Config) (offset numWindows : ℕ) :
    (windowChainSynthesisSummary cfg offset numWindows).lookupActivationCount = 0 := by
  simp only [windowChainSynthesisSummary, processWindowSynthesisSummary,
    AddIncomplete.synthesisSummary, synthesis_summary_norm, Nat.mul_zero,
    Nat.zero_add]

@[synthesis_summary_norm]
theorem windowChainSynthesisSummary_instanceRowExtent_eq
    (cfg : Config) (offset numWindows : ℕ) :
    (windowChainSynthesisSummary cfg offset numWindows).instanceRowExtent = 0 := by
  simp only [windowChainSynthesisSummary, processWindowSynthesisSummary,
    AddIncomplete.synthesisSummary, synthesis_summary_norm]
  simp

@[synthesis_summary_norm]
theorem windowChain_synthesisSummary_eq
    (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (offset numWindows : ℕ) (self : RegionIndex)
    (hprocess : ∀ w row,
      FloorPlanner.regionSynthesisSummary ((processW w row).operations self) =
        processWindowSynthesisSummary cfg row) :
    FloorPlanner.regionSynthesisSummary
        ((windowChain cfg processW offset numWindows).operations self) =
      windowChainSynthesisSummary cfg offset numWindows := by
  have hrepeat :
      (List.ofFn fun i : Fin (numWindows - 3) =>
        (FloorPlanner.RegionSynthesisSummary.ofColumns
          (windowStepColumns cfg) (offset + 2 + i.val + 2) 0).withSelectorActivations
            [(cfg.addIncompleteConfig.qAddIncomplete.index,
              offset + 2 + i.val)]).foldr
          FloorPlanner.RegionSynthesisSummary.combine {} =
        FloorPlanner.RegionSynthesisSummary.repeatColumnsWithSelector
          cfg.addIncompleteConfig.qAddIncomplete.index (windowStepColumns cfg)
          (offset + 2) 1 2 0 (numWindows - 3) := by
    simpa only [Nat.one_mul, Nat.add_assoc] using
      (FloorPlanner.RegionSynthesisSummary.foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector
        cfg.addIncompleteConfig.qAddIncomplete.index (windowStepColumns cfg)
        (offset + 2) 1 2 0 (numWindows - 3))
  have haddEmpty (row : ℕ) :
      ({} : FloorPlanner.RegionSynthesisSummary).combine
          (({} : FloorPlanner.RegionSynthesisSummary).combine
            (AddIncomplete.synthesisSummary cfg.addIncompleteConfig row)) =
        AddIncomplete.synthesisSummary cfg.addIncompleteConfig row := by
    have hcolumns :
        (AddIncomplete.synthesisSummary cfg.addIncompleteConfig row).columns.Nodup := by
      exact FloorPlanner.RegionSynthesisSummary.withSelectorActivations_ofColumns_columns_nodup
        _ _ _ _
    rw [FloorPlanner.RegionSynthesisSummary.empty_combine _ hcolumns,
      FloorPlanner.RegionSynthesisSummary.empty_combine _ hcolumns]
  unfold windowChainSynthesisSummary
  simp only [windowChain,
    RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    FloorPlanner.regionSynthesisSummary_append, operations_cellAt,
    RegionCircuit.forRange'_regionSynthesisSummary,
    FormalRegionCircuit.call_synthesisSummary,
    AddIncomplete.add_synthesisSummary_eq,
    FloorPlanner.regionSynthesisSummary_nil, haddEmpty,
    processWindow_combine_addIncomplete_synthesisSummary,
    hprocess, windowStepSynthesisSummary, Nat.mul_one,
    FloorPlanner.RegionSynthesisSummary.combine_empty,
    hrepeat]

@[synthesis_summary_norm]
theorem windowChainSynthesisSummary_constantSiteCount
    (cfg : Config) (offset numWindows : ℕ) :
    (windowChainSynthesisSummary cfg offset
      numWindows).constantSiteCount = 0 := by
  simp only [windowChainSynthesisSummary, synthesis_summary_norm,
    processWindowSynthesisSummary, AddIncomplete.synthesisSummary]
  simp

/-- The shared window chain never writes fixed columns. -/
@[synthesis_summary_norm]
theorem windowChainSynthesisSummary_hasNoFixedColumns
    (cfg : Config) (offset numWindows : ℕ) :
    (windowChainSynthesisSummary cfg offset numWindows).HasNoFixedColumns := by
  simp only [windowChainSynthesisSummary, processWindowSynthesisSummary,
    AddIncomplete.synthesisSummary,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_combine,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_withSelectorActivations,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_repeatColumnsWithSelector,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_repeatColumns]
  simp [windowStepColumns]

/-- A window chain whose per-window witness has the standard advice-only footprint
performs no fixed assignments. -/
theorem windowChain_hasNoFixedAssignments
    (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (offset numWindows : ℕ) (self : RegionIndex)
    (hprocess : ∀ w row,
      FloorPlanner.regionSynthesisSummary ((processW w row).operations self) =
        processWindowSynthesisSummary cfg row) :
    ((windowChain cfg processW offset numWindows).operations self)
      |>.HasNoFixedAssignments := by
  apply FloorPlanner.RegionSynthesisSummary.HasNoFixedColumns.hasNoFixedAssignments
  rw [windowChain_synthesisSummary_eq cfg processW offset numWindows self hprocess]
  exact windowChainSynthesisSummary_hasNoFixedColumns cfg offset numWindows

/-- The shared window chain requests no deferred constant allocations when its
per-window witness program does not. -/
theorem windowChain_synthesisSummary_constantSiteCount_eq_zero
    (config : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (offset numWindows : ℕ) (region : RegionIndex)
    (hprocessW : ∀ w row,
      (FloorPlanner.regionSynthesisSummary
        ((processW w row).operations region)).constantSiteCount = 0) :
    (FloorPlanner.regionSynthesisSummary
      ((windowChain config processW
        offset numWindows).operations region)).constantSiteCount = 0 := by
  simp only [windowChain, RegionCircuit.operations_bind,
    RegionCircuit.operations_pure, FloorPlanner.regionSynthesisSummary_append,
    synthesis_summary_norm]
  simp only [hprocessW, operations_cellAt, synthesis_summary_norm,
    List.map_ofFn, Function.comp_def]
  simp

/-- The standard fixed-base window witness program requests no deferred constants. -/
@[synthesis_summary_norm]
theorem windowChain_processWindow_synthesisSummary_constantSiteCount
    (B : FixedBaseData) (table : ℕ → ℕ → Point Fp) (config : Config)
    (alpha : AssignedCell Fp) (offset numWindows : ℕ)
    (region : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((windowChain config (processWindow B table config alpha)
        offset numWindows).operations region)).constantSiteCount = 0 := by
  apply windowChain_synthesisSummary_constantSiteCount_eq_zero
  intro w row
  simp only [processWindow, circuit_norm]

/-- Lookup-local activation correctness composes through the shared window-chain
driver whenever it holds for the supplied per-window program. -/
theorem windowChain_lookupActivationsWellFormed
    (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (offset numWindows : ℕ) (region : RegionIndex)
    (hprocessW : ∀ w row,
      ((processW w row).operations region).LookupActivationsWellFormed) :
    ((windowChain cfg processW offset numWindows).operations region)
      |>.LookupActivationsWellFormed := by
  unfold windowChain
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    RegionOperations.LookupActivationsWellFormed, List.forall_append,
    List.forall_nil, and_true, operations_cellAt]
  keygen_registration

/-- The standard fixed-base per-window program and its shared driver satisfy the
lookup-local activation law. -/
@[keygen_norm]
theorem windowChain_processWindow_lookupActivationsWellFormed
    (B : FixedBaseData) (table : ℕ → ℕ → Point Fp) (cfg : Config)
    (alpha : AssignedCell Fp) (offset numWindows : ℕ)
    (region : RegionIndex) :
    ((windowChain cfg (processWindow B table cfg alpha)
      offset numWindows).operations region).LookupActivationsWellFormed := by
  apply windowChain_lookupActivationsWellFormed
  intro w row
  unfold processWindow
  keygen_registration

@[keygen_helper]
theorem windowChain_processWindow_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (B : FixedBaseData) (table : ℕ → ℕ → Point Fp) (cfg : Config)
    (alpha : AssignedCell Fp) (offset numWindows : ℕ) (self : RegionIndex)
    (configured : AddIncomplete.add.Configured cfg.addIncompleteConfig)
    (hgates : ∀ gate, gate ∈ configured.gates → gate ∈ gates)
    (hlookups : ∀ argument, argument ∈ configured.lookups → argument ∈ lookups)
    (hfixedColumns : ∀ column,
      column ∈ configured.fixedColumns → column ∈ fixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ configured.permutationColumns → column ∈ permutationColumns)
    (hprocessColumns : ∀ column,
      column ∈ Add.permutationColumns cfg.addConfig → column ∈ permutationColumns) :
    ((windowChain cfg (processWindow B table cfg alpha) offset numWindows).operations self).Forall
      (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns) := by
  unfold windowChain windowChainStep processWindow
  simp only [keygen_spine, operations_assignAdvice, operations_cellAt,
    List.forall_cons, List.forall_nil, RegionOperation.KeygenRegistered]
  constructor
  · exact FormalRegionCircuit.call_keygenRegistered
      AddIncomplete.add cfg.addIncompleteConfig configured
      (offset + 1) _ self hgates hlookups hfixedColumns hpermutationColumns
      (by
        rw [AddIncomplete.Configured.inputCells_eq]
        simp only [circuit_norm]
        refine ⟨hprocessColumns _ (by simp [Add.permutationColumns]),
          hprocessColumns _ (by simp [Add.permutationColumns]),
          hprocessColumns _ (by simp [Add.permutationColumns]),
          hprocessColumns _ (by simp [Add.permutationColumns])⟩)
  · intro i
    exact FormalRegionCircuit.call_keygenRegistered
      AddIncomplete.add cfg.addIncompleteConfig configured
      (offset + 2 + i * 1) _ self hgates hlookups hfixedColumns hpermutationColumns
      (by
        rw [AddIncomplete.Configured.inputCells_eq]
        simp only [circuit_norm]
        refine ⟨hprocessColumns _ (by simp [Add.permutationColumns]),
          hprocessColumns _ (by simp [Add.permutationColumns]), ?_⟩
        constructor <;> apply hpermutationColumns <;>
          rw [AddIncomplete.Configured.permutationColumns_eq] <;>
          simp [AddIncomplete.permutationColumns])

/-! ## Shared proof helpers for the wrapper bundles

Context-free value lemmas the sibling proof arcs (`base_field_elem`, `full_width`, `short`) all
consume, kept file-level so in-proof uses run in an empty context (`omega` whnf-scans every
hypothesis). -/

/-- Structure eta for `Point` as an equation. -/
theorem point_eta (P : Point Fp) : ({ x := P.x, y := P.y } : Point Fp) = P := rfl

/-- `OnCurve` of the coords-mk of a point is `OnCurve` of the point (structure eta). -/
theorem point_eta_onCurve {P : Point Fp} (h : P.OnCurve) :
    ({ x := P.x, y := P.y } : Point Fp).OnCurve := h

/-- `partialSum` at 1, unfolded (context-free arithmetic). -/
theorem partialSum_one (ks : ℕ → ℕ) :
    Ecc.MulFixed.partialSum ks 1 = ks 0 + 2 + (ks 1 + 2) * 8 ^ 1 := by
  simp [Ecc.MulFixed.partialSum]

/-- `partialSum` at a successor (context-free unfold). -/
theorem partialSum_succ (ks : ℕ → ℕ) (n : ℕ) :
    Ecc.MulFixed.partialSum ks (n + 1)
      = Ecc.MulFixed.partialSum ks n + (ks (n + 1) + 2) * 8 ^ (n + 1) := rfl

/-- Pure-ℕ bounds for the ladder's first addition (windows 0 + 1). -/
theorem base_bounds {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    0 < (a + 2) * 8 ^ 0 ∧ (a + 2) * 8 ^ 0 < (b + 2) * 8 ^ 1 ∧
    (a + 2) * 8 ^ 0 + (b + 2) * 8 ^ 1
      < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
  have hcard : 100 < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]
  norm_num
  omega

/-- Pure-ℕ bounds for a ladder step. -/
theorem step_bounds {k S j : ℕ} (hk : k < 8) (hS_lt : S < 2 * 8 ^ (j + 1))
    (_hS_pos : 0 < S) (hj : j ≤ 82) :
    0 < (k + 2) * 8 ^ (j + 1) ∧ S < (k + 2) * 8 ^ (j + 1) ∧
    (k + 2) * 8 ^ (j + 1) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
    S < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
    S + (k + 2) * 8 ^ (j + 1) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
  have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
  have htu : (k + 2) * 8 ^ (j + 1) ≤ 9 * 8 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have htl : 2 * 8 ^ (j + 1) ≤ (k + 2) * 8 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have hp83 : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 83 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 11 * 8 ^ 83 < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]
  refine ⟨by positivity, by omega, by omega, by omega, by omega⟩

/-- `partialSum` only reads windows `0..w`. -/
theorem partialSum_congr {ks ks' : ℕ → ℕ} (w : ℕ) (h : ∀ t ≤ w, ks t = ks' t) :
    Ecc.MulFixed.partialSum ks w = Ecc.MulFixed.partialSum ks' w := by
  induction w with
  | zero => simp [Ecc.MulFixed.partialSum, h 0 (by omega)]
  | succ n ih =>
    simp only [Ecc.MulFixed.partialSum]
    rw [ih (fun t ht => h t (by omega)), h (n + 1) le_rfl]

/-- Lower windows' table point as a plain scalar multiple (the `+2`-padded window
scalar; both the 85- and 22-window families share this form below the MSB). -/
theorem windowPoint_lower (point : Point Fp) {w k : ℕ} (hw : w < 84) (hk : k < 8) :
    Ecc.MulFixed.windowPoint point w k = (((k + 2) * 8 ^ w : ℕ) • point) := by
  unfold Ecc.MulFixed.windowPoint
  rw [Ecc.MulFixed.windowScalar_val hw hk]

/-- The shared incomplete-addition ladder, abstract over the base point, window count
and cell reads: window `w < N−1` holds `[(ks w + 2)·8^w]·P` (`hWP`), the entering
accumulator is window 0 (`hAcc0`), and each guarded addition fact (`hStep`, the
post-`subcircuit_rw` shape of an `add_incomplete` chunk) — then the accumulator after
windows `0..j` is `[partialSum ks j]·P`. One induction for every wrapper's soundness
AND completeness ladder (85-window and 22-window families alike); the circuit-fact glue
differs per caller, the value algebra does not. -/
theorem chain_ladder (point : Point Fp) (hP : point.OnCurve)
    (N : ℕ) (hN2 : 2 ≤ N) (hN85 : N ≤ 85)
    (ks : ℕ → ℕ) (hks_lt : ∀ t, ks t < 8)
    (wx wy ax ay : ℕ → Fp)
    (hWP : ∀ w, w < N - 1 →
      wx w = ((((ks w + 2) * 8 ^ w : ℕ)) • point).x ∧
      wy w = ((((ks w + 2) * 8 ^ w : ℕ)) • point).y)
    (hAcc0 : ax 0 = wx 0 ∧ ay 0 = wy 0)
    (hStep : ∀ j, 1 ≤ j → j ≤ N - 2 →
      (({ x := wx j, y := wy j } : Point Fp).OnCurve ∧
        ({ x := ax (j - 1), y := ay (j - 1) } : Point Fp).OnCurve ∧
        wx j ≠ ax (j - 1)) →
      ({ x := ax j, y := ay j } : Point Fp)
        = { x := wx j, y := wy j } + { x := ax (j - 1), y := ay (j - 1) }) :
    ∀ j, j ≤ N - 2 →
      ax j = (Ecc.MulFixed.partialSum ks j • point).x ∧
      ay j = (Ecc.MulFixed.partialSum ks j • point).y := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨h0x, h0y⟩ := hWP 0 (by omega)
    rw [show ((ks 0 + 2) * 8 ^ 0 : ℕ) = Ecc.MulFixed.partialSum ks 0 from by
      simp [Ecc.MulFixed.partialSum]] at h0x h0y
    exact ⟨hAcc0.1.trans h0x, hAcc0.2.trans h0y⟩
  | succ n ih =>
    intro hle
    have hih := ih (by omega)
    obtain ⟨hpx, hpy⟩ := hWP (n + 1) (by omega)
    -- opaque scalars (performance: keep the products off the goal)
    obtain ⟨t, ht_def⟩ : ∃ t : ℕ, t = (ks (n + 1) + 2) * 8 ^ (n + 1) := ⟨_, rfl⟩
    obtain ⟨S, hS_def⟩ : ∃ S : ℕ, S = Ecc.MulFixed.partialSum ks n := ⟨_, rfl⟩
    rw [← ht_def] at hpx hpy
    rw [← hS_def] at hih
    have hS_lt : S < 2 * 8 ^ (n + 1) := by
      rw [hS_def]
      exact Ecc.MulFixed.partialSum_lt _ n (fun _ _ => hks_lt _)
    have hS_pos : 0 < S := by
      rw [hS_def]; exact Ecc.MulFixed.partialSum_pos _ n
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
      step_bounds (hks_lt (n + 1)) hS_lt hS_pos (by omega)
    rw [← ht_def] at hb1 hb2 hb3 hb5
    have hOut := hStep (n + 1) (by omega) (by omega) ⟨by
        rw [hpx, hpy]
        exact point_eta_onCurve (Point.nsmul_onCurve hP hb1 hb3),
      by
        rw [show n + 1 - 1 = n from by omega, hih.1, hih.2]
        exact point_eta_onCurve (Point.nsmul_onCurve hP hS_pos hb4),
      by
        rw [show n + 1 - 1 = n from by omega, hpx, hih.1]
        exact Point.nsmul_x_ne hP hS_pos hb2 (by omega)⟩
    rw [show n + 1 - 1 = n from by omega, hpx, hpy, hih.1, hih.2] at hOut
    rw [point_eta ((t : ℕ) • point), point_eta ((S : ℕ) • point),
      Point.nsmul_add_nsmul hP] at hOut
    have hps : t + S = Ecc.MulFixed.partialSum ks (n + 1) := by
      rw [ht_def, hS_def, partialSum_succ]
      ring
    rw [hps] at hOut
    exact ⟨congrArg Point.x hOut, congrArg Point.y hOut⟩

/-- Reduce the witness tables' `getElem!` at the honest window value: index
`windowVal = α.val / 8^w % 8 < 8`, and `8^w = 2^{3w}`. -/
theorem ofFn8_get_windowVal (f : Fin 8 → Fp) (env : Placed ProverEnvironment Fp)
    (alpha : AssignedCell Fp) (w : ℕ) (a : Fp) (ha : readCell env alpha = a) :
    (Vector.ofFn f)[windowVal env alpha w]!
      = f ⟨a.val / 2 ^ (3 * w) % 8, Nat.mod_lt _ (by norm_num)⟩ := by
  have hidx : windowVal env alpha w = a.val / 2 ^ (3 * w) % 8 := by
    unfold windowVal
    rw [ha, pow_mul]
    norm_num
  have hlt : windowVal env alpha w < 8 := by
    rw [hidx]; exact Nat.mod_lt _ (by norm_num)
  rw [getElem!_pos (Vector.ofFn f) (windowVal env alpha w) (by simpa using hlt)]
  rw [Vector.getElem_ofFn]
  congr 1
  exact Fin.ext hidx

/-- The incomplete-addition child's output cells (`rfl`; the hand `add_output_eq`
pattern). -/
theorem addinc_output_cells (cfgI : AddIncomplete.Config) (row : ℕ)
    (input : Var AddIncomplete.Inputs Fp) (self : RegionIndex) :
    AddIncomplete.add.output cfgI row input self
      = { x := AssignedCell.of self (row + 1) cfgI.xQR,
          y := AssignedCell.of self (row + 1) cfgI.yQR } := rfl

end Zcash.Circuits.Ecc.MulFixed
