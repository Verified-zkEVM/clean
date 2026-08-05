import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Basic

namespace Zcash.Circuits.Ecc

open Halo2

/-!
Reference:
`halo2_gadgets/src/ecc/chip/witness_point.rs`
- `witness point`
- `witness non-identity point`
-/

namespace WitnessPoint

structure Config where
  qPoint : Selector
  qPointNonId : Selector
  x : Column .advice
  y : Column .advice

/-- `y² = x³ + b`, the short-Weierstrass curve equation over the point's columns. -/
@[selector_free, query_correct]
def curveEqn (x y : Column .advice) : Expression Fp Query :=
  let x : Expression Fp Query := queryAdvice x 0
  let y : Expression Fp Query := queryAdvice y 0
  y * y - x * x * x - pallasB

/-- The "witness point" gate: pure function of its selector and columns, so the
constraints are known at every use site (both the configure registration and the
synthesize soundness proof reference this same def). -/
def pointGate (qPoint : Selector) (x y : Column .advice) : Gate Fp where
  name := "witness point"
  selector := qPoint
  queriedCells := [queryAdvice x 0, queryAdvice y 0]
  constraints :=
    let qPoint := querySelector qPoint
    [ ⟨ "x == 0 v on_curve", qPoint * queryAdvice x 0 * curveEqn x y ⟩,
      ⟨ "y == 0 v on_curve", qPoint * queryAdvice y 0 * curveEqn x y ⟩ ]
  wellFormed := by
    refine ⟨by query_correct, by query_correct, ?_, ?_⟩
    · simp [Expression.selectorsCovered, querySelector,
        queryAdvice, curveEqn]
    · intro _ constraint hconstraint
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hconstraint
      rcases hconstraint with rfl | rfl
      all_goals
        intro base scale hscale hzero
        have hcurveEval :
            (curveEqn x y).eval
                (Expression.replaceSelectorValue qPoint scale base) =
              (curveEqn x y).eval
                (Expression.enabledGateValuation qPoint base) := by
          apply Expression.eval_eq_of_selectorFree (curveEqn x y) (by selector_free)
          · intro _ _
            rfl
          · intro _ _
            rfl
          · intro _ _
            rfl
        simp only [querySelector, queryAdvice, Expression.eval,
          Expression.replaceSelectorValue, Expression.enabledGateValuation, if_pos] at hzero ⊢
        rw [← hcurveEval, one_mul]
        rcases mul_eq_zero.mp hzero with hscaled | hcurve
        · exact mul_eq_zero.mpr (.inl ((mul_eq_zero.mp hscaled).resolve_left hscale))
        · exact mul_eq_zero.mpr (.inr hcurve)

/-- The "witness non-identity point" gate. -/
def pointNonIdGate (qPointNonId : Selector) (x y : Column .advice) : Gate Fp :=
  Gate.withSelector "witness non-identity point" qPointNonId
    [queryAdvice x 0, queryAdvice y 0]
    [("on_curve", curveEqn x y)]

def configure (x y : Column .advice) : Configure Fp Config := do
  let qPoint ← selector
  let qPointNonId ← selector
  createGate (pointGate qPoint x y)
  createGate (pointNonIdGate qPointNonId x y)
  return { qPoint, qPointNonId, x, y }

instance (x y : Column .advice) :
    ElaboratedConfigure (configure x y) := by
  unfold configure
  infer_instance

def point : FormalRegionCircuit Fp (Column .advice × Column .advice) Config
    (Unconstrained Point) Point where
  configure | (x, y) => configure x y

  synthesize config offset (point : Var (Unconstrained Point) Fp) := do
    -- enable "witness point" gate
    (pointGate config.qPoint config.x config.y).enable offset
    -- assign the x and y values (per-cell scalar programs off the hint program)
    let xVar ← assignAdvice config.x offset (Witgen.MOver.toIRScalar (Point.x <$> point))
    let yVar ← assignAdvice config.y offset (Witgen.MOver.toIRScalar (Point.y <$> point))
    return ⟨ xVar, yVar ⟩

  elaborated :=
    { registered := by keygen_registration
      output config offset _ self :=
        { x := .of self offset config.x, y := .of self offset config.y }
      output_eq := by intro _ _ _ _; rfl }

  Spec _ output _ := output.Valid
  ProverAssumptions input _ _ := input.Valid
  ProverSpec input output _ _ := output = input

  soundness := by
    circuit_proof_start2 [pointGate, curveEqn]
    grind [Point.Valid, Point.OnCurve, Point.zero_def]

  completeness := by
    circuit_proof_start2 [pointGate, curveEqn]
    -- `region_0`/`region_1`: the witnessed cells carry the hint point's coordinates
    refine ⟨?_, region_0, region_1⟩
    simp only [region_0, region_1]
    rcases prover_assumptions with hc | h0
    · have hc' : _ ^ 2 = _ ^ 3 + pallasB := hc
      exact ⟨by linear_combination input_x * hc', by linear_combination input_y * hc'⟩
    · grind [Point.zero_def]

/-- The "witness non-identity point" bundle (Rust `Config::point_non_id`). Mirrors `point`:
enable the `pointNonId` gate at `offset` and
assign x/y; but the gate has no identity escape hatch, so the `Spec` is *strictly* on-curve
(`OnCurve`, not merely `Valid`), matching the Rust guarantee that the witnessed point is a
valid curve point. The Rust additionally errors when the value is known to be the identity;
that non-identity precondition is carried on the honest prover as `ProverAssumptions` (the
input is `Unconstrained`, so — like `point` — the honest-side facts about it live there). -/
def pointNonId : FormalRegionCircuit Fp (Column .advice × Column .advice) Config
    (Unconstrained Point) Point where
  configure | (x, y) => configure x y

  synthesize config offset (point : Var (Unconstrained Point) Fp) := do
    -- enable "witness non-identity point" gate
    (pointNonIdGate config.qPointNonId config.x config.y).enable offset
    -- assign the x and y values (per-cell scalar programs off the hint program)
    let xVar ← assignAdvice config.x offset (Witgen.MOver.toIRScalar (Point.x <$> point))
    let yVar ← assignAdvice config.y offset (Witgen.MOver.toIRScalar (Point.y <$> point))
    return ⟨ xVar, yVar ⟩

  elaborated :=
    { registered := by keygen_registration }

  Spec _ output _ := output.OnCurve
  -- honest-prover precondition: the witnessed point is genuinely on-curve. The Rust errors
  -- on the identity; an on-curve point is automatically non-identity (`ne_zero_of_onCurve`),
  -- so a single `OnCurve` hint captures both the non-id error path and the curve constraint.
  ProverAssumptions input _ _ := input.OnCurve
  ProverSpec input output _ _ := output = input

  soundness := by
    circuit_proof_start2 [pointNonIdGate, curveEqn]
    grind [Point.OnCurve]

  completeness := by
    circuit_proof_start2 [pointNonIdGate, curveEqn]
    refine ⟨?_, region_0, region_1⟩
    simp only [region_0, region_1]
    have hc : input_y ^ 2 = input_x ^ 3 + pallasB := prover_assumptions
    linear_combination hc

/-- The layouter-level point witnesses: the region bundles in their own regions, named
once here as in the Rust chip (`ecc/chip/witness_point.rs`). -/
def pointFormal :=
  point.toFormal "witness point"

def pointNonIdFormal :=
  pointNonId.toFormal "witness non-identity point"
@[circuit_norm ↑, synthesis_summary_norm]
theorem pointFormal_synthesisSummary_columns
    (config : Config) (input : Var (Unconstrained Point) Fp)
    (region : RegionIndex) :
    (pointFormal.elaborated.synthesisSummary config input region).columns =
      [.selector config.qPoint.index, .column .advice config.x.index,
        .column .advice config.y.index] := by
  unfold pointFormal
  rw [FormalRegionCircuit.toFormal_synthesisSummary_columns]
  rw [ElaboratedRegionCircuit.synthesisSummary_columns_eq]
  simp only [point, circuit_norm]
  simp [pointGate]

@[circuit_norm ↑, synthesis_summary_norm]
theorem pointFormal_synthesisSummary_columnOccupancy
    (config : Config) (input : Var (Unconstrained Point) Fp)
    (region : RegionIndex) (column : FloorPlanner.RegionColumn) :
    (pointFormal.elaborated.synthesisSummary
      config input region).columnOccupancy column =
      if column ∈ [.selector config.qPoint.index,
          .column .advice config.x.index,
          .column .advice config.y.index]
      then 1 else 0 := by
  unfold pointFormal
  rw [FormalRegionCircuit.toFormal_synthesisSummary_columnOccupancy]
  rw [ElaboratedRegionCircuit.synthesisSummary_columns_eq,
    ElaboratedRegionCircuit.synthesisSummary_rowCount_eq]
  simp only [point, circuit_norm]
  simp [pointGate]

@[circuit_norm ↑, synthesis_summary_norm]
theorem pointFormal_synthesisSummary_constantSiteCount
    (config : Config) (input : Var (Unconstrained Point) Fp)
    (region : RegionIndex) :
    (pointFormal.elaborated.synthesisSummary
      config input region).constantSiteCount = 0 := by
  unfold pointFormal
  rw [FormalRegionCircuit.toFormal_synthesisSummary_constantSiteCount]
  rw [ElaboratedRegionCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [point, circuit_norm]

@[circuit_norm ↑, synthesis_summary_norm]
theorem pointNonIdFormal_synthesisSummary_columns
    (config : Config) (input : Var (Unconstrained Point) Fp)
    (region : RegionIndex) :
    (pointNonIdFormal.elaborated.synthesisSummary config input region).columns =
      [.selector config.qPointNonId.index, .column .advice config.x.index,
        .column .advice config.y.index] := by
  unfold pointNonIdFormal
  rw [FormalRegionCircuit.toFormal_synthesisSummary_columns]
  rw [ElaboratedRegionCircuit.synthesisSummary_columns_eq]
  simp only [pointNonId, circuit_norm]
  simp [pointNonIdGate, Gate.withSelector]

@[circuit_norm ↑, synthesis_summary_norm]
theorem pointNonIdFormal_synthesisSummary_columnOccupancy
    (config : Config) (input : Var (Unconstrained Point) Fp)
    (region : RegionIndex) (column : FloorPlanner.RegionColumn) :
    (pointNonIdFormal.elaborated.synthesisSummary
      config input region).columnOccupancy column =
      if column ∈ [.selector config.qPointNonId.index,
          .column .advice config.x.index,
          .column .advice config.y.index]
      then 1 else 0 := by
  unfold pointNonIdFormal
  rw [FormalRegionCircuit.toFormal_synthesisSummary_columnOccupancy]
  rw [ElaboratedRegionCircuit.synthesisSummary_columns_eq,
    ElaboratedRegionCircuit.synthesisSummary_rowCount_eq]
  simp only [pointNonId, circuit_norm]
  simp [pointNonIdGate, Gate.withSelector]

@[circuit_norm ↑, synthesis_summary_norm]
theorem pointNonIdFormal_synthesisSummary_constantSiteCount
    (config : Config) (input : Var (Unconstrained Point) Fp)
    (region : RegionIndex) :
    (pointNonIdFormal.elaborated.synthesisSummary
      config input region).constantSiteCount = 0 := by
  unfold pointNonIdFormal
  rw [FormalRegionCircuit.toFormal_synthesisSummary_constantSiteCount]
  rw [ElaboratedRegionCircuit.synthesisSummary_constantSiteCount_eq]
  simp only [pointNonId, circuit_norm]


/-- The non-identity witness circuit's two positional output cells. -/
@[keygen_output_norm]
theorem pointNonIdFormal_output_cells (config : Config)
    (input : Var (Unconstrained Point) Fp) (self : RegionIndex) :
    pointNonIdFormal.output config input self =
      { x := .of self 0 config.x, y := .of self 0 config.y } := by
  rfl

derive_contract_bridges pointFormal := pointFormal

derive_contract_bridges pointNonIdFormal := pointNonIdFormal

end WitnessPoint

end Zcash.Circuits.Ecc
