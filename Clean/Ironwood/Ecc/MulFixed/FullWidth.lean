import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElemTheorems

/-!
Fixed-base scalar multiplication by a full-width scalar: the windows are witnessed
directly (not derived from a running sum, and allowed to be non-canonical), constrained
3-bit by a per-window gate, and fed into the shared incomplete-addition window chain
plus a closing complete addition. The scalar is prover-side only, so the bundle's
witness is the 85 three-bit windows and the extracted scalar they encode; `Spec` is the
extractor-form `output = s • B`.

Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`.
-/

-- The variable-name style linter whnf-walks the chunk-typed statements of the proof
-- helpers below and times out; disabled file-wide (as in `BaseFieldElem.lean`).
set_option linter.constructorNameAsVariable false

namespace Zcash.Circuits.Ecc.MulFixed.FullWidth

open Halo2
open Ecc.MulFixed
  (coordsCheck fixedConstantsLoop processWindow FixedBaseData)
open DecomposeRunningSum (rangeCheckExpr)
open Ecc.MulFixed (FixedBase)

structure Config where
  -- Selector for the "Full-width fixed-base scalar mul" gate.
  qMulFixedFull : Selector
  -- The shared fixed-base multiplication config.
  superConfig : MulFixed.Config

/-- The "Full-width fixed-base scalar mul" gate: the shared `coords_check` over the raw
`window` query, plus the 3-bit window range check — all on `q_mul_fixed_full`. -/
def fullWidthGate (cfg : Config) : Gate Fp :=
  -- the raw `window` query first, then `coords_check`'s atoms (y_p, x_p, the fixed `z`, u)
  -- and the eight Lagrange-coeff fixed queries from `interpolated_x`.
  Gate.withSelector "Full-width fixed-base scalar mul" cfg.qMulFixedFull
    [ queryAdvice cfg.superConfig.window 0,
      queryAdvice cfg.superConfig.addConfig.yP 0, queryAdvice cfg.superConfig.addConfig.xP 0,
      queryFixed cfg.superConfig.fixedZ, queryAdvice cfg.superConfig.u 0,
      queryFixed (cfg.superConfig.lagrangeCoeffs 0), queryFixed (cfg.superConfig.lagrangeCoeffs 1),
      queryFixed (cfg.superConfig.lagrangeCoeffs 2), queryFixed (cfg.superConfig.lagrangeCoeffs 3),
      queryFixed (cfg.superConfig.lagrangeCoeffs 4), queryFixed (cfg.superConfig.lagrangeCoeffs 5),
      queryFixed (cfg.superConfig.lagrangeCoeffs 6), queryFixed (cfg.superConfig.lagrangeCoeffs 7) ] <|
    let window : Expression Fp Query := queryAdvice cfg.superConfig.window 0
    coordsCheck cfg.superConfig window
      ++ [("window range check", rangeCheckExpr 8 window)]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem fullWidthGate_selector (cfg : Config) :
    (fullWidthGate cfg).selector = cfg.qMulFixedFull := rfl

/-- Allocate a fresh selector, register the gate. -/
def configure (superConfig : MulFixed.Config) : Configure Fp Config := do
  let qMulFixedFull ← selector
  let cfg : Config := { qMulFixedFull, superConfig }
  createGate (fullWidthGate cfg)
  return cfg

instance (superConfig : MulFixed.Config) :
    ElaboratedConfigure (configure superConfig) := by
  unfold configure
  infer_instance

@[keygen_norm]
theorem configure_delta_lookups (superConfig : MulFixed.Config)
    (counts : ConfigureCounts) :
    ((configure superConfig).delta counts).lookups = [] := by
  unfold configure
  rfl

@[keygen_norm]
def innerKeygenRequirements : KeygenRequirements Fp Config Unit where
  configLawful cfg :=
    AddIncomplete.add.Configured cfg.superConfig.addIncompleteConfig ×
      cfg.superConfig.FixedColumnsLawful
  gates cfg configured :=
    [fullWidthGate cfg] ++
      runningSumKeygenRequirements.gates cfg.superConfig configured.1
  lookups cfg configured :=
    runningSumKeygenRequirements.lookups cfg.superConfig configured.1
  fixedColumns cfg _ := MulFixed.fixedColumns cfg.superConfig
  permutationColumns cfg configured :=
    runningSumKeygenRequirements.permutationColumns cfg.superConfig configured.1

/-- `decompose_scalar_fixed`: enable `q_mul_fixed_full` on all `numWindows` rows, then
witness the scalar's 3-bit windows `k[w]` into the `window` column — from the window
hints. Returns nothing; the window cells are read positionally (the coords rows consume
them via queries, `process_window` via the hint values). -/
def witnessScalarLoop (cfg : Config) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  RegionCircuit.forRange' offset 1 85 (fun _ row =>
    (fullWidthGate cfg).enable row)
  RegionCircuit.forRange' offset 1 85 (fun w row => do
    let _k ← assignAdvice cfg.superConfig.window row (Witgen.MOver.toIRScalar windows[w]!)
    return ())

/-- Reduced footprint of the selector and advice passes that witness all 85 windows. -/
def witnessScalarLoopSynthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  (FloorPlanner.RegionSynthesisSummary.repeatColumnsWithSelector
      cfg.qMulFixedFull.index
      [.selector cfg.qMulFixedFull.index] offset 1 1 0 85).combine
    (FloorPlanner.RegionSynthesisSummary.repeatColumns
      [.column .advice cfg.superConfig.window.index] offset 1 1 0 85)

@[synthesis_summary_norm]
theorem witnessScalarLoopSynthesisSummary_lookupActivationCount
    (cfg : Config) (offset : ℕ) :
    (witnessScalarLoopSynthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [witnessScalarLoopSynthesisSummary, synthesis_summary_norm,
    Nat.mul_zero, Nat.zero_add]

@[synthesis_summary_norm]
theorem witnessScalarLoopSynthesisSummary_instanceRowExtent_eq
    (cfg : Config) (offset : ℕ) :
    (witnessScalarLoopSynthesisSummary cfg offset).instanceRowExtent = 0 := by
  simp only [witnessScalarLoopSynthesisSummary, synthesis_summary_norm]
  norm_num

@[synthesis_summary_norm]
theorem witnessScalarLoop_synthesisSummary_eq
    (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((witnessScalarLoop cfg windows offset).operations self) =
      witnessScalarLoopSynthesisSummary cfg offset := by
  have hselectors :=
    FloorPlanner.RegionSynthesisSummary.foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector
      cfg.qMulFixedFull.index [.selector cfg.qMulFixedFull.index] offset 1 1 0 85
  have hwindows :=
    FloorPlanner.RegionSynthesisSummary.foldr_ofColumns_eq_repeatColumns
      [.column .advice cfg.superConfig.window.index] offset 1 1 0 85
  simp only [witnessScalarLoop, witnessScalarLoopSynthesisSummary,
    RegionCircuit.operations_bind, FloorPlanner.regionSynthesisSummary_append,
    RegionCircuit.forRange'_regionSynthesisSummary, circuit_norm,
    synthesis_summary_norm, Nat.mul_one]
  rw [show
    (List.ofFn fun i : Fin 85 =>
      FloorPlanner.RegionSynthesisSummary.ofColumns
        [.selector cfg.1.index] (offset + i.val + 1) 0
        [(cfg.qMulFixedFull.index, offset + i.val)]).foldr
          FloorPlanner.RegionSynthesisSummary.combine {} =
        FloorPlanner.RegionSynthesisSummary.repeatColumnsWithSelector
          cfg.qMulFixedFull.index [.selector cfg.qMulFixedFull.index]
          offset 1 1 0 85 by
      simpa [Nat.add_assoc] using hselectors]
  rw [show
    (List.ofFn fun i : Fin 85 =>
      FloorPlanner.RegionSynthesisSummary.ofColumns
        [.column .advice cfg.superConfig.window.index]
          (offset + i.val + 1) 0).foldr
          FloorPlanner.RegionSynthesisSummary.combine {} =
        FloorPlanner.RegionSynthesisSummary.repeatColumns
          [.column .advice cfg.superConfig.window.index] offset 1 1 0 85 by
      simpa [Nat.add_assoc] using hwindows]

@[synthesis_summary_norm]
theorem witnessScalarLoopSynthesisSummary_constantSiteCount
    (cfg : Config) (offset : ℕ) :
    (witnessScalarLoopSynthesisSummary cfg offset).constantSiteCount = 0 := by
  simp only [witnessScalarLoopSynthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem witnessScalarLoopSynthesisSummary_hasNoFixedColumns
    (cfg : Config) (offset : ℕ) :
    (witnessScalarLoopSynthesisSummary cfg offset).HasNoFixedColumns := by
  simp only [witnessScalarLoopSynthesisSummary,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_combine,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_repeatColumnsWithSelector,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_repeatColumns]
  simp

@[keygen_helper]
theorem witnessScalarLoop_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (self : RegionIndex)
    (hfullWidth : fullWidthGate cfg ∈ gates) :
    ((witnessScalarLoop cfg windows offset).operations self).Forall
      (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns) := by
  unfold witnessScalarLoop
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    RegionCircuit.forRange'_forall, operations_enable, operations_assignAdvice,
    List.forall_append, List.forall_cons, List.forall_nil,
    RegionOperation.KeygenRegistered, hfullWidth, and_true]
  exact ⟨fun _ => trivial, fun _ => trivial⟩

@[keygen_norm, keygen_helper]
theorem witnessScalarLoop_copyCellsAssignedFrom
    (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (self : RegionIndex) (available : List Cell) :
    ((witnessScalarLoop cfg windows offset).operations self)
      |>.CopyCellsAssignedFrom self available := by
  unfold witnessScalarLoop
  simp only [RegionCircuit.operations_bind]
  rw [RegionOperations.copyCellsAssignedFrom_append_iff]
  constructor <;>
    apply RegionCircuit.forRange'_copyCellsAssignedFrom_of_forall_copiedCells_eq_nil <;>
    intro i <;>
    simp only [circuit_norm, RegionOperation.copiedCells, List.Forall]

/-- Witnessing the scalar windows requests no deferred constant allocations. -/
@[synthesis_summary_norm]
theorem witnessScalarLoop_synthesisSummary_constantSiteCount
    (config : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (region : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((witnessScalarLoop config windows offset).operations
        region)).constantSiteCount = 0 := by
  apply FloorPlanner.regionSynthesisSummary_constantSiteCount_eq_zero_of_forall
  unfold witnessScalarLoop
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    List.forall_append, RegionCircuit.forRange'_forall, circuit_norm]

/-- The full-width `process_window` witness values, driven by the WINDOW HINTS (not a
scalar cell): `x_p`/`y_p`/`u` of window `w` at hint value `k_w`. -/
def hintWindowVal (env : Placed ProverEnvironment Fp) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w : ℕ) : ℕ :=
  (Witgen.MOver.eval (value := field) env windows[w]!).val % 8

def xPWitH (B : FixedBaseData) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (Ecc.MulFixed.windowPoint B.point w k.val).x)[
      hintWindowVal env windows w]!)]

def yPWitH (B : FixedBaseData) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (Ecc.MulFixed.windowPoint B.point w k.val).y)[
      hintWindowVal env windows w]!)]

def uWitH (B : FixedBaseData) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => B.u w k.val)[hintWindowVal env windows w]!)]

/-- `process_window` over the window hints. -/
def processWindowH (B : FixedBaseData) (cfg : Config) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w row : ℕ) : RegionCircuit Fp (Point (AssignedCell Fp)) := do
  let x ← assignAdvice cfg.superConfig.addConfig.xP row (xPWitH B windows w)
  let y ← assignAdvice cfg.superConfig.addConfig.yP row (yPWitH B windows w)
  let _u ← assignAdvice cfg.superConfig.u row (uWitH B windows w)
  return { x, y }

@[synthesis_summary_norm]
theorem processWindowH_synthesisSummary_eq
    (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w row : ℕ) (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((processWindowH B cfg windows w row).operations self) =
      processWindowSynthesisSummary cfg.superConfig row := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [processWindowH, processWindowSynthesisSummary, circuit_norm]
  · simp only [processWindowH, processWindowSynthesisSummary, circuit_norm]
    omega
  · simp only [processWindowH, processWindowSynthesisSummary, circuit_norm]
  · simp only [processWindowH, processWindowSynthesisSummary, circuit_norm]
  · simp only [processWindowH, processWindowSynthesisSummary, circuit_norm,
      synthesis_summary_norm]
  · simp only [processWindowH, processWindowSynthesisSummary, circuit_norm,
      synthesis_summary_norm]

@[keygen_norm, keygen_output_norm]
theorem processWindowH_output_x_column (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w row : ℕ) (self : RegionIndex) :
    ((processWindowH B cfg windows w row).output self).x.cell.column =
      cfg.superConfig.addConfig.xP := by
  simp only [processWindowH, circuit_norm]

@[keygen_norm, keygen_output_norm]
theorem processWindowH_output_y_column (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w row : ℕ) (self : RegionIndex) :
    ((processWindowH B cfg windows w row).output self).y.cell.column =
      cfg.superConfig.addConfig.yP := by
  simp only [processWindowH, circuit_norm]

@[keygen_norm, keygen_helper]
theorem processWindowH_copyCellsAssignedFrom
    (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w row : ℕ) (self : RegionIndex) (available : List Cell) :
    ((processWindowH B cfg windows w row).operations self)
      |>.CopyCellsAssignedFrom self available := by
  simp only [processWindowH, circuit_norm, keygen_norm, keygen_spine]

theorem processWindowH_output_cells_assigned
    (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w row : ℕ) (self : RegionIndex) (available : List Cell) :
    let output := (processWindowH B cfg windows w row).output self
    output.x.cell ∈
        ((processWindowH B cfg windows w row).operations self
          |>.assignedCellsAfter self available) ∧
      output.y.cell ∈
        ((processWindowH B cfg windows w row).operations self
          |>.assignedCellsAfter self available) := by
  simp only [processWindowH, circuit_norm, AssignedCell.of_cell,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  constructor <;> right <;>
    simp only [RegionOperations.assignedCells, List.flatMap_cons,
      RegionOperation.assignedCells, List.singleton_append,
      List.flatMap_nil, List.mem_cons, true_or, or_true]

/-- A hinted window witness only assigns advice. -/
@[synthesis_summary_norm]
theorem processWindowH_synthesisSummary_constantSiteCount
    (B : FixedBaseData) (config : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (w row : ℕ) (region : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((processWindowH B config windows w row).operations
        region)).constantSiteCount = 0 := by
  simp only [processWindowH, circuit_norm]

/-- The hinted full-width window chain requests no deferred constants. -/
@[synthesis_summary_norm]
theorem windowChain_processWindowH_synthesisSummary_constantSiteCount
    (B : FixedBaseData) (config : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset numWindows : ℕ) (region : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((windowChain config.superConfig (processWindowH B config windows)
        offset numWindows).operations region)).constantSiteCount = 0 := by
  apply windowChain_synthesisSummary_constantSiteCount_eq_zero
  intro w row
  exact processWindowH_synthesisSummary_constantSiteCount
    B config windows w row region

structure InnerOut (F : Type) where
  -- The exit accumulator after windows 0..83.
  acc : Point F
  -- The MSB window (84) point.
  mulB : Point F
deriving ProvableStruct

/-- Region 1, "Full-width fixed-base mul (incomplete addition)": witness the scalar
windows, then the shared inner body — fixed constants (toggle = `q_mul_fixed_full`),
window-0 accumulator, the incomplete-addition loop over windows 1..83, the most
significant window 84. -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) :
    RegionCircuit Fp (InnerOut (AssignedCell Fp)) := do
  -- witness the scalar
  witnessScalarLoop cfg windows offset
  -- `assign_fixed_constants` with `q_mul_fixed_full` as the coords toggle
  fixedConstantsLoop (fullWidthGate cfg) B cfg.superConfig offset 85
  -- the shared window chain: init (window 0), incomplete additions (1..83), MSB (84)
  let r ← MulFixed.windowChain cfg.superConfig (processWindowH B cfg windows) offset 85
  return { acc := r.1, mulB := r.2 }

theorem innerRegion_operations_eq
    (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (self : RegionIndex) :
    (innerRegion B cfg offset windows).operations self =
      (witnessScalarLoop cfg windows offset).operations self ++
        (fixedConstantsLoop (fullWidthGate cfg) B cfg.superConfig offset 85).operations self ++
          (windowChain cfg.superConfig (processWindowH B cfg windows) offset 85).operations self := by
  simp only [innerRegion, RegionCircuit.operations_bind,
    RegionCircuit.operations_pure, List.append_nil, List.append_assoc]

/-- Reduced footprint of the full-width inner region. -/
def innerRegionSynthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  (witnessScalarLoopSynthesisSummary cfg offset).combine
    ((fixedConstantsLoopSynthesisSummary (fullWidthGate cfg) cfg.superConfig
      offset 85).combine
      (windowChainSynthesisSummary cfg.superConfig offset 85))

@[synthesis_summary_norm]
theorem innerRegion_synthesisSummary_eq
    (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (self : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((innerRegion B cfg offset windows).operations self) =
      innerRegionSynthesisSummary cfg offset := by
  simp only [innerRegion, innerRegionSynthesisSummary,
    RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    FloorPlanner.regionSynthesisSummary_append, synthesis_summary_norm]
  rw [windowChain_synthesisSummary_eq]
  intro w row
  exact processWindowH_synthesisSummary_eq B cfg windows w row self

@[keygen_helper]
theorem windowChain_processWindowH_keygenRegistered
    {gates : List (Gate Fp)} {lookups : List (LookupArgument Fp)}
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset numWindows : ℕ) (self : RegionIndex)
    (configured : AddIncomplete.add.Configured cfg.superConfig.addIncompleteConfig)
    (hgates : ∀ gate, gate ∈ configured.gates → gate ∈ gates)
    (hpermutationColumns : ∀ column,
      column ∈ configured.permutationColumns → column ∈ permutationColumns)
    (hprocessColumns : ∀ column,
      column ∈ Add.permutationColumns cfg.superConfig.addConfig →
        column ∈ permutationColumns) :
    ((MulFixed.windowChain cfg.superConfig (processWindowH B cfg windows)
      offset numWindows).operations self).Forall
        (RegionOperation.KeygenRegistered gates lookups fixedColumns
          permutationColumns) := by
  keygen_registration [MulFixed.windowChain]

@[keygen_helper]
theorem innerRegion_keygenRegistered
    (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (self : RegionIndex)
    (configured : innerKeygenRequirements.configLawful cfg) :
    ((innerRegion B cfg offset windows).operations self).Forall
      (RegionOperation.KeygenRegistered
        (innerKeygenRequirements.gates cfg configured)
        (innerKeygenRequirements.lookups cfg configured)
        (innerKeygenRequirements.fixedColumns cfg configured)
        (innerKeygenRequirements.permutationColumns cfg configured)) := by
  simp only [innerRegion, RegionCircuit.operations_bind,
    RegionCircuit.operations_pure, List.forall_append, List.forall_nil, and_true]
  constructor
  · unfold witnessScalarLoop
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
      RegionCircuit.forRange'_forall, operations_enable, operations_assignAdvice,
      List.forall_append, List.forall_cons, List.forall_nil,
      RegionOperation.KeygenRegistered, and_true]
    exact ⟨fun _ => by keygen_registration, fun _ => trivial⟩
  constructor
  · simp only [MulFixed.fixedConstantsLoop, RegionCircuit.forRange'_forall]
    intro i
    unfold MulFixed.fixedConstantsWindow
    keygen_registration
  · apply windowChain_processWindowH_keygenRegistered
      (configured := configured.1) <;>
      keygen_registration

theorem innerRegion_copyCellsAssignedFrom_and_outputAssigned
    (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (self : RegionIndex)
    (configured : AddIncomplete.add.Configured
      cfg.superConfig.addIncompleteConfig)
    (available : List Cell) :
    let inner := innerRegion B cfg offset windows
    (inner.operations self).CopyCellsAssignedFrom self available ∧
      (inner.output self).acc.x.cell ∈
        (inner.operations self).assignedCellsAfter self available ∧
      (inner.output self).acc.y.cell ∈
        (inner.operations self).assignedCellsAfter self available ∧
      (inner.output self).mulB.x.cell ∈
        (inner.operations self).assignedCellsAfter self available ∧
      (inner.output self).mulB.y.cell ∈
        (inner.operations self).assignedCellsAfter self available := by
  let witnessOps := (witnessScalarLoop cfg windows offset).operations self
  let fixedOps :=
    (fixedConstantsLoop (fullWidthGate cfg) B cfg.superConfig offset 85).operations self
  have hwitness := witnessScalarLoop_copyCellsAssignedFrom
    cfg windows offset self available
  have hfixed := MulFixed.fixedConstantsLoop_copyCellsAssignedFrom
    (fullWidthGate cfg) B cfg.superConfig offset 85 self
      (witnessOps.assignedCellsAfter self available)
  have hchain := MulFixed.windowChain_copyCellsAssignedFrom
    cfg.superConfig configured self (processWindowH B cfg windows)
    (fun w row current => processWindowH_copyCellsAssignedFrom
      B cfg windows w row self current)
    (fun w row current => processWindowH_output_cells_assigned
      B cfg windows w row self current)
    offset 85 (by norm_num)
    ((witnessOps ++ fixedOps).assignedCellsAfter self available)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [innerRegion, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure, List.append_nil]
    rw [RegionOperations.copyCellsAssignedFrom_append_iff]
    refine ⟨hwitness, ?_⟩
    rw [RegionOperations.copyCellsAssignedFrom_append_iff]
    refine ⟨hfixed, ?_⟩
    simpa only [RegionOperations.assignedCellsAfter_append,
      witnessOps, fixedOps] using hchain.1
  · simpa only [innerRegion, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure, List.append_nil,
      RegionOperations.assignedCellsAfter_append, witnessOps, fixedOps]
      using hchain.2.1
  · simpa only [innerRegion, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure, List.append_nil,
      RegionOperations.assignedCellsAfter_append, witnessOps, fixedOps]
      using hchain.2.2.1
  · simpa only [innerRegion, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure, List.append_nil,
      RegionOperations.assignedCellsAfter_append, witnessOps, fixedOps]
      using hchain.2.2.2.1
  · simpa only [innerRegion, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure, List.append_nil,
      RegionOperations.assignedCellsAfter_append, witnessOps, fixedOps]
      using hchain.2.2.2.2

/-- The two regions. Returns the result point `[scalar]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) :
    Circuit Fp (Var Point Fp) := do
  let inn ←
    assignRegion "Full-width fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 windows)
  assignRegion "Full-width fixed-base mul (last window, complete addition)"
    (Add.add.call cfg.superConfig.addConfig 0 ⟨inn.mulB, inn.acc⟩)

theorem synthesize_copyCellsAssignedFrom
    (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (i : RegionIndex)
    (configuredIncomplete : AddIncomplete.add.Configured
      cfg.superConfig.addIncompleteConfig)
    (configuredAdd : Add.add.Configured cfg.superConfig.addConfig) :
    ((synthesize B cfg windows).operations i).CopyCellsAssigned i [] := by
  let innerBody := (innerRegion B cfg 0 windows).operations i
  let innerOutput := (innerRegion B cfg 0 windows).output i
  let afterInner := innerBody.assignedCellsAfter i []
  have hinner := innerRegion_copyCellsAssignedFrom_and_outputAssigned
    B cfg 0 windows i configuredIncomplete []
  have hadd : ((Add.add.call cfg.superConfig.addConfig 0
      ⟨innerOutput.mulB, innerOutput.acc⟩).operations (i + 1))
      |>.CopyCellsAssignedFrom (i + 1) afterInner := by
    apply Add.add.call_copyCellsAssignedFrom cfg.superConfig.addConfig
      configuredAdd 0 ⟨innerOutput.mulB, innerOutput.acc⟩ (i + 1)
    intro cell hcell
    rw [Add.add_inputCells] at hcell
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
    rcases hcell with rfl | rfl | rfl | rfl
    · exact hinner.2.2.2.1
    · exact hinner.2.2.2.2
    · exact hinner.2.1
    · exact hinner.2.2.1
  simp only [synthesize, Circuit.operations_bind, operations_assignRegion,
    output_assignRegion, nextRegionIndex_assignRegion, List.singleton_append]
  apply Operations.CopyCellsAssignedFrom.region
  · exact hinner.1
  apply Operations.CopyCellsAssignedFrom.region
  · exact hadd
  · exact .nil (i + 2) _

/-! ## The inner-region contract

Extractor-form contracts: the 85 window cells are the designated env readings
(`Witness := fields 85`); the digits are existentially bound in `Spec` (soundness pins
each window cell to a 3-bit value via the gate's range check), and `ProverSpec` exposes
the honest exit values at the witnessed digits. -/

@[keygen_norm]
private theorem innerRegion_output_acc (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (self : RegionIndex) :
    ((innerRegion B cfg offset windows).output self).acc
      = { x := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.xQR,
          y := AssignedCell.of self (offset + 84)
            cfg.superConfig.addIncompleteConfig.yQR } := by
  simp only [innerRegion, MulFixed.windowChain, circuit_norm]

@[keygen_norm]
private theorem innerRegion_output_mulB (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (self : RegionIndex) :
    ((innerRegion B cfg offset windows).output self).mulB
      = { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
          y := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.yP } := by
  simp only [innerRegion, MulFixed.windowChain, processWindowH, circuit_norm]

/-- The whole inner-region output as a cell literal (structure eta over the
projections). -/
private theorem innerRegion_output (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (self : RegionIndex) :
    (innerRegion B cfg offset windows).output self
      = { acc := { x := AssignedCell.of self (offset + 84)
                     cfg.superConfig.addIncompleteConfig.xQR,
                   y := AssignedCell.of self (offset + 84)
                     cfg.superConfig.addIncompleteConfig.yQR },
          mulB := { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
                    y := AssignedCell.of self (offset + 84)
                      cfg.superConfig.addConfig.yP } } := by
  rw [← innerRegion_output_acc, ← innerRegion_output_mulB]

derive_contract_bridges addinc := Ecc.AddIncomplete.add
derive_contract_bridges addc := Ecc.Add.add

/-- Required shared-config equalities: `add_incomplete.x_p/y_p` are `add.x_p/y_p`. -/
def InnerEnvAssumptions (cfg : Config) (_ : Placed Environment Fp) : Prop :=
  cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP ∧
  cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP

/-- The window cells (positional; the extraction data). -/
def windowCells (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    Var (fields 85) Fp :=
  Vector.ofFn (fun w : Fin 85 =>
    AssignedCell.of self (offset + w.val) cfg.superConfig.window)

/-- The inner region's output cells, reduced (the explicit `elaborated` output). -/
def innerOutCells (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    Var InnerOut Fp where
  acc := { x := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.xQR,
           y := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.yQR }
  mulB := { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
            y := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.yP }

/-- Verifier contract: each window cell is a 3-bit digit, and the exit cells hold the
windowed ladder values at those digits. -/
def InnerSpec (B : FixedBase) (_ : Value unit Fp) (out : Value InnerOut Fp)
    (ws : Vector Fp 85) : Prop :=
  ∃ ks : ℕ → ℕ, (∀ w, w < 85 → ks w < 8) ∧
    (∀ w : Fin 85, ws[w.val] = ((ks w.val : ℕ) : Fp)) ∧
    out.acc = { x := ((Ecc.MulFixed.partialSum ks 83) • B.point).x,
                y := ((Ecc.MulFixed.partialSum ks 83) • B.point).y } ∧
    out.mulB = Ecc.MulFixed.windowPoint B.point 84 (ks 84)

/-- Honest-prover precondition: trivial — the window programs the bundle instantiates are
3-bit by construction (`scalarWindows`), so the digit bound is proved, not assumed
(`fw_inner_completeness` takes it as a side hypothesis on the programs). -/
def InnerProverAssumptions (_ : ProverValue unit Fp) (_ : Vector Fp 85)
    (_ : ProverHint Fp) : Prop :=
  True

/-- Honest-prover postcondition: the witnessed windows are genuine 3-bit digits, and the
exit cells hold the ladder values at those digits. -/
def InnerProverSpec (B : FixedBase) (_ : ProverValue unit Fp)
    (out : ProverValue InnerOut Fp) (ws : Vector Fp 85) (_ : ProverHint Fp) : Prop :=
  (∀ t : ℕ, t < 85 → (ws[t]!).val < 8) ∧
  out.acc.x = (Ecc.MulFixed.partialSum (fun t => (ws[t]!).val) 83 • B.point).x ∧
  out.acc.y = (Ecc.MulFixed.partialSum (fun t => (ws[t]!).val) 83 • B.point).y ∧
  out.mulB.x = (Ecc.MulFixed.windowPoint B.point 84 ((ws[84]!).val)).x ∧
  out.mulB.y = (Ecc.MulFixed.windowPoint B.point 84 ((ws[84]!).val)).y

theorem innerRegion_fixedAssignmentsAgree
    (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (self : RegionIndex) (fixedColumnsLawful : cfg.superConfig.FixedColumnsLawful) :
    ((innerRegion B cfg offset windows).operations self)
      |>.FixedAssignmentsAgree := by
  rw [innerRegion_operations_eq]
  generalize fullWidthGate cfg = toggle
  have hfixed :=
    fixedConstantsLoop_fixedAssignmentsAgree
      toggle B cfg.superConfig fixedColumnsLawful offset 85 self
  have hchain := windowChain_hasNoFixedAssignments cfg.superConfig
    (processWindowH B cfg windows) offset 85 self fun w row =>
      processWindowH_synthesisSummary_eq B cfg windows w row self
  apply hfixed.between
  · unfold witnessScalarLoop RegionOperations.HasNoFixedAssignments
    simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
      RegionCircuit.forRange'_forall, List.forall_append]
    constructor <;> intro i <;>
      simp only [operations_enable, operations_assignAdvice,
        List.forall_cons, List.forall_nil,
        RegionOperation.HasNoFixedAssignment, and_self]
  · exact hchain

seal innerRegion in
/-- The elaborated-metadata instance for the inner region's synthesize lambda, with the
output cells in explicit reduced form (`innerOutCells`) — computing the default output
projection runs the whole region monad (a `List.append` whnf storm). -/
instance innerElab (B : FixedBaseData)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) :
    ElaboratedRegionCircuit Fp Config Config unit InnerOut
      pure
      (fun config offset (_ : Var unit Fp) => innerRegion B config offset windows) where
  keygenRequirements :=
    innerKeygenRequirements
  registered configInput counts configured offset input self :=
    innerRegion_keygenRegistered B configInput offset windows self configured
  copyCellsAssigned configInput _ configured offset _ self :=
    (innerRegion_copyCellsAssignedFrom_and_outputAssigned
      B configInput offset windows self configured.1 []).1
  lookupActivationsWellFormed config offset _ region := by
    simp only [innerRegion, RegionCircuit.operations_bind,
      RegionCircuit.operations_pure,
      RegionOperations.LookupActivationsWellFormed,
      List.forall_append, List.forall_nil, and_true]
    constructor
    · unfold witnessScalarLoop
      keygen_registration
    constructor
    · simp only [fixedConstantsLoop, RegionCircuit.forRange'_forall]
      intro i
      unfold fixedConstantsWindow
      keygen_registration
    · apply windowChain_lookupActivationsWellFormed
      intro w row
      unfold processWindowH
      keygen_registration
  fixedAssignmentsAgree := by
    intro configInput _ configured offset _ self
    exact innerRegion_fixedAssignmentsAgree B configInput offset windows self configured.2
  output config offset _ self := innerOutCells config offset self
  synthesisSummary config offset _ _ :=
    innerRegionSynthesisSummary config offset
  output_eq := by
    intro _ _ _ self
    rw [innerOutCells, innerRegion_output]
  synthesisSummary_eq := by
    intro _ _ _ self
    exact (innerRegion_synthesisSummary_eq B _ _ windows self).symm
seal innerRegion in
@[synthesis_summary_norm]
theorem innerRegion_synthesisSummary_constantSiteCount
    (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (self : RegionIndex) :
    (FloorPlanner.regionSynthesisSummary
      ((innerRegion B cfg offset windows).operations self)).constantSiteCount = 0 := by
  simp only [innerRegion, RegionCircuit.operations_bind,
    RegionCircuit.operations_pure, FloorPlanner.regionSynthesisSummary_append,
    synthesis_summary_norm]

/-- Reduce the witness tables' `getElem!` at the hint digit (`hintWindowVal < 8`). -/
private theorem ofFn8_get_hint (f : Fin 8 → Fp) (env : Placed ProverEnvironment Fp)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (w : ℕ) :
    (Vector.ofFn f)[hintWindowVal env windows w]!
      = f ⟨hintWindowVal env windows w, Nat.mod_lt _ (by norm_num)⟩ := by
  have hlt : hintWindowVal env windows w < 8 := Nat.mod_lt _ (by norm_num)
  rw [getElem!_pos (Vector.ofFn f) (hintWindowVal env windows w) (by simpa using hlt)]
  rw [Vector.getElem_ofFn]

set_option linter.all false in
/-- The honest per-window point values: the chain's witness programs put the
window-table coordinates and `u` values at each window row, at the HINT digits. -/
private theorem fw_windows_honest (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self)) :
    ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Ecc.MulFixed.windowPoint B.point w.val
            (hintWindowVal env windows w.val)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Ecc.MulFixed.windowPoint B.point w.val
            (hintWindowVal env windows w.val)).y ∧
      env.env.advice cfg.superConfig.u
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = B.u w.val (hintWindowVal env windows w.val) := by
  simp only [MulFixed.windowChain, processWindowH, circuit_norm, mul_one,
    xPWitH, yPWitH, uWitH] at hWchain
  obtain ⟨hx0, hy0, hu0, hx1, hy1, hu1, _hAW1, hLoopW, hx84, hy84, hu84⟩ := hWchain
  intro w
  rcases w with ⟨wv, hwv⟩
  simp only []
  rcases Nat.eq_zero_or_pos wv with rfl | hpos
  · rw [show offset + 0 = offset from by omega]
    rw [hx0, hy0, hu0, ofFn8_get_hint _ env windows 0, ofFn8_get_hint _ env windows 0,
      ofFn8_get_hint _ env windows 0]
    exact ⟨rfl, rfl, rfl⟩
  rcases Nat.lt_or_ge wv 2 with h1 | h2
  · rw [show wv = 1 from by omega]
    rw [hx1, hy1, hu1, ofFn8_get_hint _ env windows 1, ofFn8_get_hint _ env windows 1,
      ofFn8_get_hint _ env windows 1]
    exact ⟨rfl, rfl, rfl⟩
  rcases Nat.lt_or_ge wv 84 with h84 | h84
  · obtain ⟨hxw, hyw, huw, -⟩ := hLoopW ⟨wv - 2, by omega⟩
    rw [show offset + 2 + (wv - 2) = offset + wv from by omega,
      show wv - 2 + 2 = wv from by omega] at hxw hyw huw
    rw [hxw, hyw, huw, ofFn8_get_hint _ env windows wv, ofFn8_get_hint _ env windows wv,
      ofFn8_get_hint _ env windows wv]
    exact ⟨rfl, rfl, rfl⟩
  · rw [show wv = 84 from by omega]
    rw [hx84, hy84, hu84, ofFn8_get_hint _ env windows 84,
      ofFn8_get_hint _ env windows 84, ofFn8_get_hint _ env windows 84]
    exact ⟨rfl, rfl, rfl⟩

set_option linter.all false in
/-- Completeness of the window chain (standalone): the incomplete additions' constraints
from their completeness leaves on the honest ladder, plus the honest exit values. -/
private theorem fw_completeness_chain (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self))
    (hXPeq : cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP)
    (hYPeq : cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self) ∧
    (env.env.advice cfg.superConfig.addIncompleteConfig.xQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).x ∧
     env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).y ∧
     env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).x ∧
     env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).y) := by
  have hPW := fw_windows_honest B cfg offset self env windows hWchain
  have hks_lt : ∀ t, hintWindowVal env windows t < 8 :=
    fun t => Nat.mod_lt _ (by norm_num)
  -- the addinc chunk witnesses
  simp only [MulFixed.windowChain, processWindowH, circuit_norm, mul_one] at hWchain
  obtain ⟨-, -, -, -, -, -, hAW1, hLoopW, -, -, -⟩ := hWchain
  -- per-chunk derived statements (Spec under Assumptions)
  have hD1 := Halo2.SubcircuitRw.region_completeness_derived_placed
    AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 1) self env
    ⟨⟨AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.xP,
      AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.yP⟩,
     ⟨AssignedCell.of self offset cfg.superConfig.addConfig.xP,
      AssignedCell.of self offset cfg.superConfig.addConfig.yP⟩⟩ hAW1
  simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
    addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at hD1
  have hLoopD := fun (i : Fin 82) => by
    have h := Halo2.SubcircuitRw.region_completeness_derived_placed
      AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 2 + i.val) self env
      ⟨⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.xP,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.yP⟩,
       ⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.xQR,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.yQR⟩⟩
      ((hLoopW i).2.2.2)
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at h
    exact h
  -- the honest ladder (shared)
  have hLadder := MulFixed.chain_ladder B.point B.onCurve 85 (by norm_num)
    (by norm_num) (fun t => hintWindowVal env windows t) hks_lt
    (fun w => env.env.advice cfg.superConfig.addConfig.xP
      ((env.place self + (offset + w) : ℕ) : ℤ))
    (fun w => env.env.advice cfg.superConfig.addConfig.yP
      ((env.place self + (offset + w) : ℕ) : ℤ))
    (fun j => if j = 0 then
        env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + offset : ℕ) : ℤ)
      else
        env.env.advice cfg.superConfig.addIncompleteConfig.xQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ))
    (fun j => if j = 0 then
        env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + offset : ℕ) : ℤ)
      else
        env.env.advice cfg.superConfig.addIncompleteConfig.yQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ))
    (fun w hw => by
      obtain ⟨hx, hy, -⟩ := hPW ⟨w, by omega⟩
      rw [MulFixed.windowPoint_lower B.point (by omega) (hks_lt _)] at hx hy
      exact ⟨hx, hy⟩)
    ⟨if_pos rfl, if_pos rfl⟩
    (by
      intro j hj1 hj83 hAssumptions
      obtain ⟨hOnP, hOnQ, hne⟩ := hAssumptions
      dsimp only at hOnP hOnQ hne ⊢
      rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)]
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj : j = 1 := by omega
        subst hj
        obtain ⟨⟨-, hOut⟩, -⟩ := hD1 ⟨hOnP, hOnQ, hne⟩
        exact hOut
      · have h := hLoopD ⟨j - 2, by omega⟩
        rw [show offset + 2 + (j - 2) = offset + j from by omega] at h
        rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega] at hOnQ
        rw [if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega] at hne
        rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega]
        obtain ⟨⟨-, hOut⟩, -⟩ := h ⟨hOnP, hOnQ, hne⟩
        exact hOut)
  have hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 83 →
      env.env.advice cfg.superConfig.addIncompleteConfig.xQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) j
            • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) j
            • B.point).y := by
    intro j hj1 hj83
    have h := hLadder j hj83
    dsimp only at h
    rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)] at h
    exact h
  have hHonest : env.env.advice cfg.superConfig.addIncompleteConfig.xQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).y ∧
      env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).y := by
    have h83 := hInv 83 (by norm_num) le_rfl
    rw [show offset + 83 + 1 = offset + 84 from by omega] at h83
    obtain ⟨hx84', hy84', -⟩ := hPW ⟨84, by norm_num⟩
    rw [show ((⟨84, by norm_num⟩ : Fin 85) : ℕ) = 84 from rfl] at hx84' hy84'
    exact ⟨h83.1, h83.2, hx84', hy84'⟩
  refine And.intro ?_ hHonest
  simp only [MulFixed.windowChain, processWindowH, circuit_norm, mul_one]
  have hC1 := Halo2.SubcircuitRw.region_completeness_leaf_placed
    AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 1) self env
    ⟨⟨AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.xP,
      AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.yP⟩,
     ⟨AssignedCell.of self offset cfg.superConfig.addConfig.xP,
      AssignedCell.of self offset cfg.superConfig.addConfig.yP⟩⟩ hAW1
  simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
    addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at hC1
  constructor
  · -- first addition: window-1 point + window-0 point, honest values
    obtain ⟨hp1x, hp1y, -⟩ := hPW ⟨1, by norm_num⟩
    obtain ⟨hp0x, hp0y, -⟩ := hPW ⟨0, by norm_num⟩
    rw [show ((⟨1, by norm_num⟩ : Fin 85) : ℕ) = 1 from rfl] at hp1x hp1y
    rw [show ((⟨0, by norm_num⟩ : Fin 85) : ℕ) = 0 from rfl,
      show offset + 0 = offset from by omega] at hp0x hp0y
    obtain ⟨t1, ht1_def⟩ : ∃ t : ℕ, t = (Ecc.MulFixed.windowScalar 1
      (hintWindowVal env windows 1)).val := ⟨_, rfl⟩
    obtain ⟨s0, hs0_def⟩ : ∃ t : ℕ, t = (Ecc.MulFixed.windowScalar 0
      (hintWindowVal env windows 0)).val := ⟨_, rfl⟩
    have ht1 : t1 = (hintWindowVal env windows 1 + 2) * 8 ^ 1 := by
      rw [ht1_def]
      exact Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 1)
    have hs0 : s0 = (hintWindowVal env windows 0 + 2) * 8 ^ 0 := by
      rw [hs0_def]
      exact Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 0)
    have hwp1 : Ecc.MulFixed.windowPoint B.point 1
        (hintWindowVal env windows 1) = t1 • B.point := by rw [ht1_def]; rfl
    have hwp0 : Ecc.MulFixed.windowPoint B.point 0
        (hintWindowVal env windows 0) = s0 • B.point := by rw [hs0_def]; rfl
    rw [hwp1] at hp1x hp1y
    rw [hwp0] at hp0x hp0y
    obtain ⟨hbb1, hbb2, hbb3⟩ := MulFixed.base_bounds (hks_lt 0) (hks_lt 1)
    rw [← hs0] at hbb1 hbb2 hbb3
    rw [← ht1] at hbb2 hbb3
    exact hC1 ⟨by
        rw [hp1x, hp1y]
        exact MulFixed.point_eta_onCurve
          (by rw [← hwp1]; exact B.windowPoint_onCurve (hks_lt 1)),
      by
        rw [hp0x, hp0y]
        exact MulFixed.point_eta_onCurve
          (by rw [← hwp0]; exact B.windowPoint_onCurve (hks_lt 0)),
      by
        rw [hp1x, hp0x]
        exact B.nsmul_x_ne hbb1 hbb2 hbb3⟩
  · -- loop chunk i: window-(i+2) point + honest accumulator [partialSum (i+1)]·B
    intro i
    have hC := Halo2.SubcircuitRw.region_completeness_leaf_placed
      AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 2 + i.val) self env
      ⟨⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.xP,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.yP⟩,
       ⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.xQR,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.yQR⟩⟩
      ((hLoopW i).2.2.2)
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at hC
    obtain ⟨hpx, hpy, -⟩ := hPW ⟨i.val + 2, by omega⟩
    rw [show ((⟨i.val + 2, by omega⟩ : Fin 85) : ℕ) = i.val + 2 from rfl,
      show offset + (i.val + 2) = offset + 2 + i.val from by omega] at hpx hpy
    have hih := hInv (i.val + 1) (by omega) (by omega)
    rw [show offset + (i.val + 1) + 1 = offset + 2 + i.val from by omega] at hih
    obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
        t = (Ecc.MulFixed.windowScalar (i.val + 2)
          (hintWindowVal env windows (i.val + 2))).val := ⟨_, rfl⟩
    obtain ⟨S, hS_def⟩ : ∃ S : ℕ,
        S = Ecc.MulFixed.partialSum
          (fun t => hintWindowVal env windows t) (i.val + 1) := ⟨_, rfl⟩
    have hval : t = (hintWindowVal env windows (i.val + 2) + 2) * 8 ^ (i.val + 2) := by
      rw [ht_def]
      exact Ecc.MulFixed.windowScalar_val (by omega) (hks_lt _)
    have hwp : Ecc.MulFixed.windowPoint B.point (i.val + 2)
        (hintWindowVal env windows (i.val + 2)) = t • B.point := by
      rw [ht_def]; rfl
    rw [hwp] at hpx hpy
    rw [← hS_def] at hih
    have hS_lt : S < 2 * 8 ^ (i.val + 2) := by
      rw [hS_def]
      exact Ecc.MulFixed.partialSum_lt _ _ (fun _ _ => hks_lt _)
    have hS_pos : 0 < S := by
      rw [hS_def]; exact Ecc.MulFixed.partialSum_pos _ _
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
      MulFixed.step_bounds (hks_lt (i.val + 2)) hS_lt hS_pos (by omega)
    rw [← hval] at hb1 hb2 hb3 hb5
    exact hC ⟨by
        rw [hpx, hpy]
        exact MulFixed.point_eta_onCurve (B.nsmul_onCurve hb1 hb3),
      by
        rw [hih.1, hih.2]
        exact MulFixed.point_eta_onCurve (B.nsmul_onCurve hS_pos hb4),
      by
        rw [hpx, hih.1]
        exact B.nsmul_x_ne hS_pos hb2 (by omega)⟩

set_option linter.all false in
/-- Completeness of the gate/fixed rows (standalone): the fixed-cell witness equations
pin the Lagrange columns, and the gate holds at the honest window digits — for BOTH
enable sites (the witness loop and the fixed-constants loop share the same per-row gate
equations; the latter's are proven and the former's extracted). Needs the window cells
pinned to the hint digits (`hWin` — the honest-prover `< 8` guarantee, threaded from
`ProverAssumptions`). -/
private theorem fw_completeness_fixed (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (hWfix : RegionOperations.ExtendsWitnesses env.place self env.env
      ((fixedConstantsLoop (fullWidthGate cfg) B.toData cfg.superConfig offset
        85).operations self))
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self))
    (hWin : ∀ w : Fin 85, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((hintWindowVal env windows w.val : ℕ) : Fp)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((witnessScalarLoop cfg windows offset).operations self) ∧
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((fixedConstantsLoop (fullWidthGate cfg) B.toData cfg.superConfig offset
        85).operations self) := by
  have hPW := fw_windows_honest B cfg offset self env windows hWchain
  simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow, circuit_norm,
    mul_one] at hWfix
  constructor
  · -- the witness loop's 85 gate enables
    simp only [witnessScalarLoop, fullWidthGate, MulFixed.coordsCheck,
      MulFixed.eval_interpolatedX,
      DecomposeRunningSum.eval_rangeCheckExpr,
      circuit_norm, mul_one, one_mul]
    intro i
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hWfix i
    simp only [show B.toData.params = B.params from rfl] at hL0 hL1 hL2 hL3 hL4 hL5
    simp only [show B.toData.params = B.params from rfl] at hL6 hL7 hZf
    obtain ⟨hpx, hpy, hpu⟩ := hPW i
    have hdig : hintWindowVal env windows i.val < 8 := Nat.mod_lt _ (by norm_num)
    have hxi : (Ecc.MulFixed.windowPoint B.point i.val
          (hintWindowVal env windows i.val)).x
        = Ecc.MulFixed.interpolate (B.params i.val)
            ((hintWindowVal env windows i.val : ℕ) : Fp) :=
      (B.interpolate_eq i.val i.isLt _ hdig).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- check x
      rw [hWin i, hpx, hxi, sub_eq_zero]
      symm
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0.symm | exact hL1.symm | exact hL2.symm | exact hL3.symm
        | exact hL4.symm | exact hL5.symm | exact hL6.symm | exact hL7.symm
    · -- check y (u² = y_p + z)
      rw [hpu, hpy, hZf]
      have huu := B.u_mul_u i.val i.isLt _ hdig
      linear_combination huu
    · -- on-curve
      rw [hpx, hpy]
      have hoc := B.windowPoint_onCurve (w := i.val) hdig
      unfold Point.OnCurve at hoc
      linear_combination hoc
    · -- window range check
      rw [hWin i]
      exact (Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 8 _).mpr
        ((DecomposeRunningSum.inRange_iff_exists_lt 8 (by norm_num) _).mpr
          ⟨hintWindowVal env windows i.val, hdig, rfl⟩)
  · -- the fixed-constants loop: the same gate equations + the fixed-cell clauses
    simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow,
      fullWidthGate, MulFixed.coordsCheck, MulFixed.eval_interpolatedX,
      DecomposeRunningSum.eval_rangeCheckExpr,
      circuit_norm, mul_one, one_mul]
    intro i
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hWfix i
    simp only [show B.toData.params = B.params from rfl] at hL0 hL1 hL2 hL3 hL4 hL5
    simp only [show B.toData.params = B.params from rfl] at hL6 hL7 hZf
    obtain ⟨hpx, hpy, hpu⟩ := hPW i
    have hdig : hintWindowVal env windows i.val < 8 := Nat.mod_lt _ (by norm_num)
    have hxi : (Ecc.MulFixed.windowPoint B.point i.val
          (hintWindowVal env windows i.val)).x
        = Ecc.MulFixed.interpolate (B.params i.val)
            ((hintWindowVal env windows i.val : ℕ) : Fp) :=
      (B.interpolate_eq i.val i.isLt _ hdig).symm
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩
    · -- check x
      rw [hWin i, hpx, hxi, sub_eq_zero]
      symm
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0.symm | exact hL1.symm | exact hL2.symm | exact hL3.symm
        | exact hL4.symm | exact hL5.symm | exact hL6.symm | exact hL7.symm
    · -- check y (u² = y_p + z)
      rw [hpu, hpy, hZf]
      have huu := B.u_mul_u i.val i.isLt _ hdig
      linear_combination huu
    · -- on-curve
      rw [hpx, hpy]
      have hoc := B.windowPoint_onCurve (w := i.val) hdig
      unfold Point.OnCurve at hoc
      linear_combination hoc
    · -- window range check
      rw [hWin i]
      exact (Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 8 _).mpr
        ((DecomposeRunningSum.inRange_iff_exists_lt 8 (by norm_num) _).mpr
          ⟨hintWindowVal env windows i.val, hdig, rfl⟩)

/-- The elaborated output projection, reduced (`rfl` via `innerElab`). -/
private theorem innerElab_output (B : FixedBaseData) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (config : Config) (offset : ℕ) (input : Var unit Fp) (self : RegionIndex) :
    ElaboratedRegionCircuit.output pure
        (fun config offset (_ : Var unit Fp) => innerRegion B config offset windows)
        config offset input self
      = innerOutCells config offset self := rfl

set_option linter.all false in
/-- Soundness of the inner region. -/
private theorem fw_inner_soundness (B : FixedBase) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (cfg : Config) (offset : ℕ) :
    FormalRegionCircuit.Soundness (Input := unit) (Output := InnerOut)
      pure
      (fun config offset (_ : Var unit Fp) =>
        innerRegion B.toData config offset windows)
      cfg offset
      (fun _ self env => eval env (windowCells cfg offset self))
      (InnerEnvAssumptions cfg) (fun _ => True) (InnerSpec B) := by
  circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions]
  obtain ⟨env, rfl, rfl⟩ :
      ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
    ⟨⟨place, env⟩, rfl, rfl⟩
  obtain ⟨-, hFixed, hChain⟩ := hc
  -- circuit_proof_start unfolded `innerRegion` in `h_output`; it is defeq to the reduced cells.
  change ProvableStruct.Halo2.eval env.place env.env (innerOutCells cfg offset self)
    = { acc := output_acc, mulB := output_mulB } at h_output
  simp only [innerOutCells] at h_output
  provable_type_simp
  obtain ⟨⟨hOax, hOay⟩, hOmx, hOmy⟩ := h_output
  obtain ⟨hXPeq, hYPeq⟩ := _hE
  -- ── the per-row gate + Lagrange-fixed rows ──
  simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow,
    fullWidthGate, MulFixed.coordsCheck, MulFixed.eval_interpolatedX,
    DecomposeRunningSum.eval_rangeCheckExpr,
    circuit_norm, mul_one, one_mul] at hFixed
  -- ── the 3-bit digits, from the per-row window range checks ──
  have hdig : ∀ w : Fin 85, ∃ k : ℕ, k < 8 ∧
      env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ) = ((k : ℕ) : Fp) := by
    intro w
    obtain ⟨⟨-, -, -, hRange⟩, -⟩ := hFixed w
    exact (DecomposeRunningSum.inRange_iff_exists_lt 8 (by norm_num) _).mp
      ((Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 8 _).mp hRange)
  choose kf hkf_lt hkf_eq using hdig
  obtain ⟨ks, hks_def⟩ : ∃ ks : ℕ → ℕ,
      ks = fun t => if h : t < 85 then kf ⟨t, h⟩ else 0 := ⟨_, rfl⟩
  have hks_lt : ∀ t, ks t < 8 := by
    intro t
    rw [hks_def]
    dsimp only
    split
    · exact hkf_lt _
    · norm_num
  have hkeq : ∀ w : Fin 85, env.env.advice cfg.superConfig.window
      ((env.place self + (offset + w.val) : ℕ) : ℤ) = ((ks w.val : ℕ) : Fp) := by
    intro w
    rw [hks_def]
    dsimp only
    rw [dif_pos w.isLt]
    exact hkf_eq w
  -- ── the per-row window points (the coords rows) ──
  have hWP : ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Ecc.MulFixed.windowPoint B.point w.val (ks w.val)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Ecc.MulFixed.windowPoint B.point w.val (ks w.val)).y := by
    intro w
    have hRow := hFixed w
    obtain ⟨⟨hIx, hUy, hCrv, -⟩, hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hRow
    simp only [show B.toData.params = B.params from rfl]
      at hL0 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hZf
    rw [hkeq w] at hIx
    have hxP : env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = Ecc.MulFixed.interpolate (B.params w.val)
            ((ks w.val : ℕ) : Fp) := by
      rw [← sub_eq_zero.mp hIx]
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0 | exact hL1 | exact hL2 | exact hL3
        | exact hL4 | exact hL5 | exact hL6 | exact hL7
    have hspec : Ecc.MulFixed.Coords.Spec (B.params w.val)
        { window := ((ks w.val : ℕ) : Fp),
          xP := env.env.advice cfg.superConfig.addConfig.xP
            ((env.place self + (offset + w.val) : ℕ) : ℤ),
          yP := env.env.advice cfg.superConfig.addConfig.yP
            ((env.place self + (offset + w.val) : ℕ) : ℤ),
          u := env.env.advice cfg.superConfig.u
            ((env.place self + (offset + w.val) : ℕ) : ℤ) } := by
      refine ⟨hxP, ?_, ?_⟩
      · rw [← hZf]; linear_combination hUy
      · linear_combination hCrv
    have hcw := B.coords_eq_windowPoint (w := w.val) (k := ks w.val)
      (by omega) (hks_lt _) rfl hspec
    dsimp only at hcw
    exact hcw
  refine ⟨ks, fun w _ => hks_lt w, ?_, ?_, ?_⟩
  · -- the window cells hold the digits
    intro w
    simp only [windowCells, circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
      AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
      Environment.get_advice]
    exact hkeq w
  · -- acc = [partialSum ks 83]·B  (the window-chain ladder)
    simp only [MulFixed.windowChain, processWindowH, circuit_norm,
      RegionCircuit.operations_bind, RegionOperations.constraints_append] at hChain
    obtain ⟨hA1, hALoop⟩ := hChain
    subcircuit_rw at hA1
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      MulFixed.addinc_output_cells, circuit_norm] at hA1
    have hLoopS := fun (i : Fin 82) => by
      have h := hALoop i
      subcircuit_rw at h
      simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
        MulFixed.addinc_output_cells, circuit_norm, mul_one] at h
      exact h
    clear hALoop
    -- ── the shared ladder, at this region's reads ──
    have hLadder := MulFixed.chain_ladder B.point B.onCurve 85 (by norm_num)
      (by norm_num) ks hks_lt
      (fun w => env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + w) : ℕ) : ℤ))
      (fun w => env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + w) : ℕ) : ℤ))
      (fun j => if j = 0 then
          env.env.advice cfg.superConfig.addConfig.xP
            ((env.place self + offset : ℕ) : ℤ)
        else
          env.env.advice cfg.superConfig.addIncompleteConfig.xQR
            ((env.place self + (offset + j + 1) : ℕ) : ℤ))
      (fun j => if j = 0 then
          env.env.advice cfg.superConfig.addConfig.yP
            ((env.place self + offset : ℕ) : ℤ)
        else
          env.env.advice cfg.superConfig.addIncompleteConfig.yQR
            ((env.place self + (offset + j + 1) : ℕ) : ℤ))
      (fun w hw => by
        obtain ⟨hx, hy⟩ := hWP ⟨w, by omega⟩
        rw [MulFixed.windowPoint_lower B.point (by omega) (hks_lt _)] at hx hy
        exact ⟨hx, hy⟩)
      ⟨if_pos rfl, if_pos rfl⟩
      (by
        intro j hj1 hj83 hAssumptions
        obtain ⟨hOnP, hOnQ, hne⟩ := hAssumptions
        dsimp only at hOnP hOnQ hne ⊢
        rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)]
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · -- j = 1: the explicit first chunk (window 1 + window 0)
          have hj : j = 1 := by omega
          subst hj
          obtain ⟨-, hOut⟩ := hA1 ⟨hOnP, hOnQ, hne⟩
          exact hOut
        · -- j ≥ 2: loop chunk j − 2
          have h := hLoopS ⟨j - 2, by omega⟩
          rw [show offset + 2 + (j - 2) = offset + j from by omega] at h
          rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega] at hOnQ
          rw [if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega] at hne
          rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega]
          obtain ⟨-, hOut⟩ := h ⟨hOnP, hOnQ, hne⟩
          exact hOut)
    have hI83 := hLadder 83 (by norm_num)
    dsimp only at hI83
    rw [if_neg (by norm_num : ¬(83 : ℕ) = 0), if_neg (by norm_num : ¬(83 : ℕ) = 0),
      show offset + 83 + 1 = offset + 84 from by omega] at hI83
    rw [← hOax, ← hOay]
    rcases hP : Ecc.MulFixed.partialSum ks 83 • B.point with ⟨px, py⟩
    rw [hP] at hI83
    rw [hI83.1, hI83.2]
  · -- mulB = windowPoint 84 k₈₄  (the MSB coords row)
    obtain ⟨hwx, hwy⟩ := hWP ⟨84, by norm_num⟩
    rw [← hOmx, ← hOmy]
    rcases hW : Ecc.MulFixed.windowPoint B.point 84 (ks 84) with ⟨wx, wy⟩
    rw [show ((⟨84, by norm_num⟩ : Fin 85) : ℕ) = 84 from rfl, hW] at hwx hwy
    rw [hwx, hwy]

set_option linter.all false in
/-- Completeness of the inner region. -/
private theorem fw_inner_completeness (B : FixedBase) (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (cfg : Config) (offset : ℕ)
    (hbound : ∀ (env : Placed ProverEnvironment Fp) (w : Fin 85),
      (Witgen.MOver.eval (value := field) env windows[w.val]!).val < 8) :
    FormalRegionCircuit.Completeness (Input := unit) (Output := InnerOut)
      pure
      (fun config offset (_ : Var unit Fp) =>
        innerRegion B.toData config offset windows)
      cfg offset
      (fun _ self env => eval env (windowCells cfg offset self))
      (InnerEnvAssumptions cfg) (fun _ => True) InnerProverAssumptions
      (InnerProverSpec B) := by
  circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions,
    InnerProverSpec]
  obtain ⟨env, rfl, rfl⟩ :
      ∃ pe : Placed ProverEnvironment Fp, pe.place = place ∧ pe.env = env :=
    ⟨⟨place, env⟩, rfl, rfl⟩
  obtain ⟨hWwsl, hWfix, hWchain⟩ := hwit
  obtain ⟨hXPeq, hYPeq⟩ := _hE
  -- the window cells hold the hint digits (the witness loop's assign clauses).
  -- NB `have hW := hWwsl` (a chunk-typed copy) whnf-storms; peel in place.
  -- Land the assigned advice on the hint program's `MOver.eval` atom, and STOP there:
  -- run circuit_norm with `eval_toIRScalar` erased (leaves the `toIRScalar _ .eval`
  -- form, since `MOver.eval` never appears to be unfolded), then apply `eval_toIRScalar`
  -- alone. The honest-value facts below (`hbound`/`hintWindowVal`) are atom-spelled and
  -- meet it directly. (The general high-level path is the follow-up discriminating simproc.)
  simp only [witnessScalarLoop, circuit_norm, mul_one] at hWwsl
  have hWwslM := hWwsl
  -- TEMPORARY (pending the follow-up discriminating simproc): with `eval` reducing
  -- again, `hWwslM` lands at the reduced program-run spelling, so bridge the honest
  -- facts (atom-spelled `hbound`/`hintWindowVal`) to that same run form via
  -- `circuit_norm`. The high-level path keeps `MOver.eval env <hint>` an atom.
  have hPA' : ∀ w : Fin 85, (env.env.advice cfg.superConfig.window
      ((env.place self + (offset + w.val) : ℕ) : ℤ)).val < 8 := by
    intro w
    rw [hWwslM w]
    have hb := hbound env w
    simp only [circuit_norm] at hb
    exact hb
  have hWin : ∀ w : Fin 85, env.env.advice cfg.superConfig.window
      ((env.place self + (offset + w.val) : ℕ) : ℤ)
    = ((hintWindowVal env windows w.val : ℕ) : Fp) := by
    intro w
    simp only [hintWindowVal, circuit_norm]
    rw [hWwslM w, Nat.mod_eq_of_lt (by rw [← hWwslM w]; exact hPA' w)]
    exact (ZMod.natCast_zmod_val _).symm
  -- the trailing `pure` region auto-discharged, so the constraint block is the three loops only.
  refine And.intro (And.intro ?_ (And.intro ?_ ?_)) ?_
  · with_reducible
      exact (fw_completeness_fixed B cfg offset self env windows hWfix hWchain hWin).1
  · with_reducible
      exact (fw_completeness_fixed B cfg offset self env windows hWfix hWchain hWin).2
  · with_reducible
      exact (fw_completeness_chain B cfg offset self env windows hWchain
        hXPeq hYPeq).1
  · -- the honest-prover contract (`InnerProverSpec`)
    change ProvableStruct.Halo2.eval env.place env.env.toEnvironment (innerOutCells cfg offset self)
      = _ at h_output
    simp only [innerOutCells] at h_output
    provable_type_simp
    obtain ⟨⟨hOax, hOay⟩, hOmx, hOmy⟩ := h_output
    have hws : ∀ t : ℕ, t < 85 →
        ZMod.val (@getElem! (Vector Fp 85) ℕ Fp _ _ _
          (eval (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp)
            (windowCells cfg offset self)) t)
        = hintWindowVal env windows t := by
      intro t ht
      rw [getElem!_pos _ t (by simpa using ht)]
      simp only [windowCells, circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
        AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
        Environment.get_advice]
      rw [hWin ⟨t, ht⟩]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
      exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
        (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    have hax := (fw_completeness_chain B cfg offset self env windows hWchain
      hXPeq hYPeq).2
    refine ⟨fun t ht => by rw [hws t ht]; exact Nat.mod_lt _ (by norm_num), ?_, ?_, ?_, ?_⟩
    · rw [← hOax, hax.1,
        MulFixed.partialSum_congr 83 (fun t ht => hws t (by omega))]
    · rw [← hOay, hax.2.1,
        MulFixed.partialSum_congr 83 (fun t ht => hws t (by omega))]
    · rw [← hOmx, hax.2.2.1, hws 84 (by norm_num)]
    · rw [← hOmy, hax.2.2.2, hws 84 (by norm_num)]

/-! ## The gadget bundle (`FixedPoint::mul`)

Extractor form: `Witness` carries the window cells and the scalar they encode; `Spec` is
literally `output = s • B`. The scalar hint enters as a nat-valued witness-IR program, and
the 85 three-bit window programs are derived from it. -/

/-- The 85 three-bit window programs derived from the scalar's Nat-hint program:
window `w` reads `(scalar >>> 3w) &&& 7` as a field-valued witness program. The concrete
85-entry vector stays irreducible so callers can share it without materializing every
bind-program. -/
irreducible_def scalarWindows (scalar : Var UnconstrainedNat Fp) :
    Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85 :=
  Vector.ofFn fun w =>
    (do let n ← scalar
        pure (.ofNat (.land (.shiftR n (.const (3 * w.val))) (.const 7))) :
      Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))

/-- The derived window programs are 3-bit by construction. -/
theorem scalarWindows_eval_lt (scalar : Var UnconstrainedNat Fp)
    (env : Placed ProverEnvironment Fp) (w : Fin 85) :
    (Witgen.MOver.eval (value := field) env (scalarWindows scalar)[w.val]!).val < 8 := by
  rw [getElem!_pos _ w.val w.isLt]
  simp only [scalarWindows, Vector.getElem_ofFn]
  simp only [Witgen.MOver.eval, circuit_norm, Witgen.eval_field, Witgen.FExprOver.eval,
    Witgen.NExprOver.eval, FiniteField.fromNat_F]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  · exact Nat.lt_succ_of_le Nat.and_le_right
  · exact lt_of_lt_of_le (Nat.lt_succ_of_le Nat.and_le_right)
      (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

open CompElliptic.Fields.Pasta (Fq PALLAS_BASE_CARD) in
/-- The scalar read off the 85 window cells (the constructive extractor). -/
def windowsScalar (ws : Vector Fp 85) : Fq :=
  ((∑ w ∈ Finset.range 85, (ws[w]!).val * 8 ^ w : ℕ) : Fq)

/-- The top-level extraction data: the window cells and the scalar they encode
(a named def keeps the pair opaque during proof setup). -/
def fwExtract (cfg : Config) (i₀ : RegionIndex) (env : Placed Environment Fp) :
    Vector Fp 85 × Fq :=
  let ws := eval env (windowCells cfg 0 i₀)
  (ws, windowsScalar ws)

/-- Environment preconditions: the shared incomplete- and complete-addition point columns agree. -/
def EnvAssumptions (cfg : Config) (_ : Placed Environment Fp) : Prop :=
  cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP ∧
  cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP

/-- The region count of `synthesize`: inner mul + complete addition. -/
private theorem synthesize_regionCount (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85) (i : RegionIndex) :
    Operations.regionCount ((synthesize B cfg windows).operations i) = 2 := by
  simp only [synthesize, circuit_norm, operations_assignRegion, Operations.regionCount]

/-- Reduced footprint of the two top-level regions. -/
def circuitSynthesisSummary (cfg : Config) :
    FloorPlanner.SynthesisSummary :=
  (FloorPlanner.SynthesisSummary.ofRegion
    (innerRegionSynthesisSummary cfg 0)).combine
    (FloorPlanner.SynthesisSummary.ofRegion
      (Add.synthesisSummary cfg.superConfig.addConfig 0))

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_lookupActivationCount (cfg : Config) :
    (circuitSynthesisSummary cfg).lookupActivationCount = 0 := by
  simp only [circuitSynthesisSummary, innerRegionSynthesisSummary,
    synthesis_summary_norm]

@[synthesis_summary_norm]
theorem synthesize_synthesisSummary_eq
    (B : FixedBaseData) (cfg : Config)
    (windows : Vector (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (self : RegionIndex) :
    FloorPlanner.synthesisSummary ((synthesize B cfg windows).operations self) =
      circuitSynthesisSummary cfg := by
  simp only [synthesize, circuitSynthesisSummary, Circuit.operations_bind,
    FloorPlanner.synthesisSummary_append, operations_assignRegion,
    synthesis_summary_norm]

seal innerRegion in
set_option linter.constructorNameAsVariable false in
/-- `[s]B` for the full-width scalar encoded by the witnessed windows. The input is the scalar's
nat-valued reading program; the window programs derive from it and are 3-bit by construction. -/
def circuit (B : FixedBase) :
    FormalCircuit Fp MulFixed.Config Config UnconstrainedNat Point where
  name := "fixed-base mul (full width)"

  configure := configure

  synthesize cfg scalar := synthesize B.toData cfg (scalarWindows scalar)

  elaborated :=
    { keygenRequirements :=
        { configLawful cfg :=
            AddIncomplete.add.Configured cfg.addIncompleteConfig ×
              Add.add.Configured cfg.addConfig × cfg.FixedColumnsLawful
          gates cfg configured :=
            runningSumKeygenRequirements.gates cfg configured.1 ++ configured.2.1.gates
          lookups cfg configured :=
            runningSumKeygenRequirements.lookups cfg configured.1 ++ configured.2.1.lookups
          fixedColumns cfg _ := MulFixed.fixedColumns cfg
          permutationColumns cfg configured :=
            runningSumKeygenRequirements.permutationColumns cfg configured.1 ++
              configured.2.1.permutationColumns }
      registered configInput counts configured scalar self := by
        rcases configured with
          ⟨configuredAddIncomplete, configuredAdd, fixedColumnsLawful⟩
        simp only [keygen_norm, keygen_spine, configure, synthesize]
        have hinner := innerRegion_keygenRegistered B.toData
          { qMulFixedFull := { index := counts.numSelectors, simple := true },
            superConfig := configInput }
          0 (scalarWindows scalar) self ⟨configuredAddIncomplete, fixedColumnsLawful⟩
        constructor
        · exact RegionOperations.keygenRegistered_mono hinner
            (by keygen_registration) (by keygen_registration)
            (by keygen_registration) (by keygen_registration)
        · keygen_registration
      lookupSelectorsAnchoredBy_of_registered := by
        intro configInput counts hconfig _ _ anchor _ hregistered
        rcases hconfig with ⟨configuredIncomplete, configuredAdd, _⟩
        have hlookups :
            (runningSumKeygenRequirements.lookups configInput
                configuredIncomplete ++ configuredAdd.lookups) ++
              ((configure configInput).delta counts).lookups = [] := by
          simp only [keygen_norm,
            AddIncomplete.Configured.lookups_eq_nil configuredIncomplete,
            Add.Configured.lookups_eq_nil configuredAdd]
        rw [hlookups] at hregistered
        exact Operations.LookupSelectorsAnchoredBy.of_registered_noLookups
          hregistered anchor
      lookupActivationsWellFormed config scalar region := by
        simp only [synthesize, Circuit.operations_bind,
          operations_assignRegion, Operations.LookupActivationsWellFormed]
        constructor
        · exact (innerElab B.toData (scalarWindows scalar))
            |>.lookupActivationsWellFormed config 0 () region
        · exact Add.add.call_lookupActivationsWellFormed
            config.superConfig.addConfig 0 _ (region + 1)
      output cfg _ i :=
        { x := .of (i + 1) 1 cfg.superConfig.addConfig.xQR
          y := .of (i + 1) 1 cfg.superConfig.addConfig.yQR }
      synthesisSummary cfg _ _ := circuitSynthesisSummary cfg
      regionCount _ := 2
      output_eq := by
        intro _ _ _
        simp only [synthesize, circuit_norm, keygen_output_norm]
      synthesisSummary_eq := by
        intro _ _ self
        exact (synthesize_synthesisSummary_eq B.toData _ _ self).symm
      regionCount_eq := fun cfg scalar i =>
        (synthesize_regionCount B.toData cfg (scalarWindows scalar) i).symm
      fixedWritesLawful := by
        intro configInput counts hconfig scalar self
        rcases hconfig with
          ⟨configuredIncomplete, configuredAdd, fixedColumnsLawful⟩
        let cfg := (configure configInput).output counts
        let windows := scalarWindows scalar
        have hinner := innerRegion_fixedAssignmentsAgree B.toData cfg 0 windows self
          fixedColumnsLawful
        have hadd := Add.add.call_fixedAssignmentsAgree
          cfg.superConfig.addConfig configuredAdd 0
          ⟨((innerRegion B.toData cfg 0 windows).output self).mulB,
            ((innerRegion B.toData cfg 0 windows).output self).acc⟩
          (self + 1)
        constructor
        · simpa only [synthesize, Circuit.operations_bind, operations_assignRegion,
            List.forall_append, List.forall_cons, List.forall_nil, and_true,
            windows] using And.intro hinner hadd
        · simp [synthesize, Circuit.operations_bind, operations_assignRegion,
            Operations.loadedTableColumns]
        · simp [synthesize, Circuit.operations_bind, operations_assignRegion,
            Operations.loadedTableColumns]
        · simp [synthesize, Circuit.operations_bind, operations_assignRegion,
            Operations.loadedTableColumns]
      copyCellsAssigned := by
        intro configInput counts hconfig scalar i
        rcases hconfig with ⟨configuredIncomplete, configuredAdd, _⟩
        exact synthesize_copyCellsAssignedFrom B.toData
          ((configure configInput).output counts) (scalarWindows scalar) i
          configuredIncomplete configuredAdd }

  EnvAssumptions := EnvAssumptions

  Assumptions _ := True

  Witness := fun F => Vector F 85 × Fq
  extract cfg _ i₀ env := fwExtract cfg i₀ env

  Spec _ output s := output = s.2 • B

  ProverAssumptions _ _ _ := True

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start2
    -- region 1: the inner windowed mul, consumed through the family soundness on the
    -- folded chunk (cps2 delivers it beta-reduced — no change pre-beta needed)
    have hIS : InnerSpec B (eval (⟨place, env⟩ : Placed Environment Fp) (default : Var unit Fp))
        (eval (⟨place, env⟩ : Placed Environment Fp) (innerOutCells cfg 0 i₀))
        (eval (⟨place, env⟩ : Placed Environment Fp) (windowCells cfg 0 i₀)) :=
      fw_inner_soundness B (scalarWindows input_var) cfg 0 i₀
        ⟨place, env⟩ default env_assumptions trivial region_0
    simp only [InnerSpec, innerOutCells, windowCells, circuit_norm] at hIS
    obtain ⟨ks, hks_lt', hws, hAcc, hMulB⟩ := hIS
    -- concretize the minted inner-output atoms via the closed form
    rw [innerRegion_output] at inn_eq
    cases inn_eq
    -- ── region 2: the complete addition `mul_b + acc` (the terminal chunk's contract) ──
    simp only [addc_spec_eq, addc_assumptions_eq, addc_envAssumptions_eq,
      Nat.zero_add, circuit_norm] at region_1
    have hAdd := region_1
    -- ── the honest scalars, opaque ──
    obtain ⟨t84, ht84_def⟩ : ∃ t : ℕ,
        t = (Ecc.MulFixed.windowScalar 84 (ks 84)).val := ⟨_, rfl⟩
    have hwp84 : Ecc.MulFixed.windowPoint B.point 84 (ks 84) = t84 • B.point := by
      rw [ht84_def]; rfl
    obtain ⟨S83, hS83_def⟩ : ∃ S : ℕ, S = Ecc.MulFixed.partialSum ks 83 := ⟨_, rfl⟩
    have hS83_lt : S83 < 2 * 8 ^ 84 := by
      rw [hS83_def]
      exact Ecc.MulFixed.partialSum_lt _ 83 (fun j hj => hks_lt' j (by omega))
    have hS83_pos : 0 < S83 := by
      rw [hS83_def]
      exact Ecc.MulFixed.partialSum_pos _ _
    have hS83_card : S83 < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD :=
      Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card hS83_lt (by norm_num)
    have hOnP : (t84 • B.point).OnCurve := by
      rw [← hwp84]
      exact B.windowPoint_onCurve (hks_lt' 84 (by norm_num))
    have hOnQ : (S83 • B.point).OnCurve := B.nsmul_onCurve hS83_pos hS83_card
    obtain ⟨-, hOutEq⟩ := hAdd ⟨by rw [hMulB, hwp84]; exact Or.inl hOnP,
      by rw [hAcc, ← hS83_def]; exact Or.inl hOnQ⟩
    rw [hMulB, hAcc, hwp84, ← hS83_def] at hOutEq
    rw [Point.nsmul_add_nsmul B.onCurve] at hOutEq
    -- ── the extracted scalar is the digit sum ──
    have hchain : (t84 + S83) • B.point
        = (((∑ w ∈ Finset.range 85, ks w * 8 ^ w : ℕ) :
            Fq)).val • B.point := by
      rw [ht84_def, hS83_def, ← Ecc.MulFixed.FixedBase.add_natCast_val_nsmul,
        Ecc.MulFixed.BaseFieldElem.RunningSumMul.windowScalar_partialSum]
    have hsum : windowsScalar
        (eval (⟨place, env⟩ : Placed Environment Fp) (windowCells cfg 0 i₀))
        = ((∑ w ∈ Finset.range 85, ks w * 8 ^ w : ℕ) :
            Fq) := by
      unfold windowsScalar
      refine congrArg Nat.cast (Finset.sum_congr rfl ?_)
      intro w hw
      have hwlt : w < 85 := Finset.mem_range.mp hw
      rw [getElem!_pos _ w (by simpa using hwlt)]
      simp only [windowCells, circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
        AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
        Environment.get_advice, Nat.zero_add]
      rw [hws ⟨w, hwlt⟩, ZMod.val_natCast,
        Nat.mod_eq_of_lt (lt_of_lt_of_le (hks_lt' w hwlt)
          (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))]
    show ({ x := output_x, y := output_y } : Point Fp)
      = (fwExtract cfg i₀ ⟨place, env⟩).2 • B
    simp only [fwExtract]
    rw [hsum]
    calc
      { x := output_x, y := output_y } =
          eval (⟨place, env⟩ : Placed Environment Fp)
            (Add.add.output cfg.superConfig.addConfig 0
              { p := { x := .of i₀ 84 cfg.superConfig.addConfig.xP,
                       y := .of i₀ 84 cfg.superConfig.addConfig.yP }
                q := { x := .of i₀ 84 cfg.superConfig.addIncompleteConfig.xQR,
                       y := .of i₀ 84 cfg.superConfig.addIncompleteConfig.yQR } }
              (i₀ + 1)) := by
                simp only [keygen_output_norm, circuit_norm, Point.mk.injEq]
                exact ⟨output_eq.1.symm, output_eq.2.symm⟩
      _ = (t84 + S83) • B.point := hOutEq
      _ = ((∑ w ∈ Finset.range 85, ks w * 8 ^ w : ℕ) : Fq).val • B.point := hchain
      _ = ((∑ w ∈ Finset.range 85, ks w * 8 ^ w : ℕ) : Fq) • B :=
        (MulFixed.point_eta _).symm

  completeness := by
    circuit_proof_start2
    -- region 1 honest: the inner windowed mul, via the family completeness
    have hIC := fw_inner_completeness B (scalarWindows input_var) cfg 0
      (scalarWindows_eval_lt input_var) i₀ ⟨place, env⟩ default region_0
      env_assumptions trivial trivial
    have hPS := hIC.2
    rw [ElaboratedRegionCircuit.output_eq, innerRegion_output] at hPS
    simp only [InnerProverSpec, circuit_norm] at hPS
    -- the digit bounds arrive as the honest contract's first conjunct, already in the
    -- `getElem!` spelling the honest facts use
    obtain ⟨hkv, hax, hay, hmx, hmy⟩ := hPS
    -- concretize the minted inner-output atoms via the closed form
    rw [innerRegion_output] at inn_eq
    cases inn_eq
    simp only [addc_assumptions_eq, addc_envAssumptions_eq,
      addc_proverAssumptions_eq, Nat.zero_add, circuit_norm]
    refine ⟨hIC.1, ?_, ?_⟩
    · -- mulB honest: window-84 point on curve
      have hOn : (Ecc.MulFixed.windowPoint B.point 84
          (@getElem! (Vector Fp 85) ℕ Fp _ _ _
            (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) (windowCells cfg 0 i₀)) 84).val).OnCurve :=
        B.windowPoint_onCurve (hkv 84 (by norm_num))
      rcases hWp : Ecc.MulFixed.windowPoint B.point 84
          (@getElem! (Vector Fp 85) ℕ Fp _ _ _
            (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) (windowCells cfg 0 i₀)) 84).val with ⟨wx, wy⟩
      rw [hWp] at hOn hmx hmy
      rw [hmx, hmy]
      exact Or.inl hOn
    · -- acc honest: partialSum point on curve
      have hOn : ((Ecc.MulFixed.partialSum
          (fun t => (@getElem! (Vector Fp 85) ℕ Fp _ _ _
            (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) (windowCells cfg 0 i₀)) t).val) 83)
            • B.point).OnCurve :=
        B.nsmul_onCurve (Ecc.MulFixed.partialSum_pos _ _)
          (Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card
            (Ecc.MulFixed.partialSum_lt _ 83 (fun j hj => hkv j (by omega)))
            (by norm_num))
      rcases hSp : Ecc.MulFixed.partialSum
          (fun t => (@getElem! (Vector Fp 85) ℕ Fp _ _ _
            (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) (windowCells cfg 0 i₀)) t).val) 83
          • B.point with ⟨sx, sy⟩
      rw [hSp] at hOn hax hay
      rw [hax, hay]
      exact Or.inl hOn

@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq
    (B : FixedBase) (cfg : Config) (input : Var UnconstrainedNat Fp)
    (self : RegionIndex) :
    (circuit B).elaborated.synthesisSummary cfg input self =
      circuitSynthesisSummary cfg := rfl

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_constantSiteCount (config : Config) :
    (circuitSynthesisSummary config).constantSiteCount = 0 := by
  simp only [circuitSynthesisSummary, synthesis_summary_norm,
    innerRegionSynthesisSummary, Add.synthesisSummary]

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_instanceRowExtent_eq (config : Config) :
    (circuitSynthesisSummary config).instanceRowExtent = 0 := by
  simp only [circuitSynthesisSummary, innerRegionSynthesisSummary,
    Add.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_tableRowExtent_eq (config : Config) :
    (circuitSynthesisSummary config).tableRowExtent = 0 := by
  simp only [circuitSynthesisSummary, synthesis_summary_norm]

/-- Full-width fixed-base multiplication requests no deferred constant allocations. -/
@[synthesis_summary_norm]
theorem circuit_synthesisSummary_constantSiteCount
    (B : FixedBase) (config : Config) (input : Var UnconstrainedNat Fp)
    (region : RegionIndex) :
    ((circuit B).elaborated.synthesisSummary
      config input region).constantSiteCount = 0 := by
  rw [circuit_synthesisSummary_eq]
  exact circuitSynthesisSummary_constantSiteCount config

@[keygen_output_norm]
theorem circuit_output_cells
    (B : FixedBase) (config : Config) (input : Var UnconstrainedNat Fp)
    (self : RegionIndex) :
    (circuit B).output config input self =
      { x := .of (self + 1) 1 config.superConfig.addConfig.xQR,
        y := .of (self + 1) 1 config.superConfig.addConfig.yQR } := by
  rfl

@[circuit_norm]
theorem circuit_regionCount (B : FixedBase) (input : Var UnconstrainedNat Fp) :
    (circuit B).regionCount input = 2 := by
  rfl

@[keygen_norm]
theorem circuit_inputCells_eq
    (B : FixedBase) {config : Config}
    (configured : (circuit B).Configured config)
    (input : Var UnconstrainedNat Fp) :
    configured.inputCells input = [] := by
  rfl

@[keygen_norm]
theorem Configured.lookups_eq_nil
    (B : FixedBase) {config : Config}
    (configured : (circuit B).Configured config) :
    configured.lookups = [] := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [FormalCircuit.Configured.lookups,
    FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
    circuit, keygen_norm,
    AddIncomplete.Configured.lookups_eq_nil hconfig.1,
    Add.Configured.lookups_eq_nil hconfig.2.1]

theorem circuit_call_output_cells_assigned
    (B : FixedBase) (config : Config) (input : Var UnconstrainedNat Fp)
    (self : RegionIndex) :
    let output := (circuit B).output config input self
    output.x.cell ∈ Operations.assignedCellsFrom
        (((circuit B).call config input).operations self) self ∧
      output.y.cell ∈ Operations.assignedCellsFrom
        (((circuit B).call config input).operations self) self := by
  rw [circuit_output_cells]
  rw [FormalCircuit.call_operations]
  let innerOutput := (innerRegion B.toData config 0 (scalarWindows input)).output self
  have hadd := Add.add_output_cells_assigned config.superConfig.addConfig 0
    ⟨innerOutput.mulB, innerOutput.acc⟩ (self + 1) []
  dsimp only at hadd
  simp only [RegionOperations.mem_assignedCellsAfter_iff, List.nil_append,
    Add.add_output_cells, AssignedCell.of_cell] at hadd
  simp only [circuit, synthesize, Circuit.operations_bind,
    operations_assignRegion, output_assignRegion, nextRegionIndex_assignRegion,
    List.singleton_append, List.append_nil, Operations.assignedCellsFrom,
    List.mem_append]
  exact ⟨Or.inr hadd.1, Or.inr hadd.2⟩

/-- The complete-addition columns remain equality-enabled through the full-width bundle. -/
theorem Configured.addPermutationColumns_subset (B : FixedBase) {cfg : Config}
    (configured : (circuit B).Configured cfg) :
    ∀ column ∈ Add.permutationColumns cfg.superConfig.addConfig,
      column ∈ configured.permutationColumns := by
  intro column hcolumn
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [FormalCircuit.Configured.permutationColumns,
    FormalCircuit.keygenRequirements, ElaboratedCircuit.keygenRequirements,
    circuit, List.mem_append]
  apply Or.inl
  apply Or.inr
  rw [Add.Configured.permutationColumns_eq hconfig.2.1]
  exact hcolumn

derive_contract_bridges circuit (B : FixedBase) := circuit B

end Zcash.Circuits.Ecc.MulFixed.FullWidth
