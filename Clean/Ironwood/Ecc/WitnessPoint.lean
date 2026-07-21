import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Basic

namespace Halo2.Ironwood.Ecc
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
  constraints :=
    let qPoint := querySelector qPoint
    [ ⟨ "x == 0 v on_curve", qPoint * queryAdvice x 0 * curveEqn x y ⟩,
      ⟨ "y == 0 v on_curve", qPoint * queryAdvice y 0 * curveEqn x y ⟩ ]

/-- The "witness non-identity point" gate. -/
def pointNonIdGate (qPointNonId : Selector) (x y : Column .advice) : Gate Fp where
  name := "witness non-identity point"
  selector := qPointNonId
  constraints := [⟨ "on_curve", querySelector qPointNonId * curveEqn x y ⟩]

def configure (x y : Column .advice) : Configure Fp Config := do
  let qPoint ← selector
  let qPointNonId ← selector
  createGate (pointGate qPoint x y)
  createGate (pointNonIdGate qPointNonId x y)
  return { qPoint, qPointNonId, x, y }

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

  elaborated config offset :=
    { output := fun _ self => { x := .of self offset config.x, y := .of self offset config.y }
      output_eq := by intro _ _; rfl }

  Spec _ output _ := output.Valid
  ProverAssumptions input _ _ := input.Valid
  ProverSpec input output _ _ := output = input

  soundness := by
    circuit_proof_start2 [pointGate, curveEqn]
    grind [Halo2.Ironwood.Point.Valid, Halo2.Ironwood.Point.OnCurve, Halo2.Ironwood.Point.zero_def]

  completeness := by
    circuit_proof_start2 [pointGate, curveEqn]
    -- `region_0`/`region_1`: the witnessed cells carry the hint point's coordinates
    refine ⟨?_, region_0, region_1⟩
    simp only [region_0, region_1]
    rcases prover_assumptions with hc | h0
    · have hc' : _ ^ 2 = _ ^ 3 + Halo2.Ironwood.pallasB := hc
      exact ⟨by linear_combination input_x * hc', by linear_combination input_y * hc'⟩
    · grind [Halo2.Ironwood.Point.zero_def]

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

  Spec _ output _ := output.OnCurve
  -- honest-prover precondition: the witnessed point is genuinely on-curve. The Rust errors
  -- on the identity; an on-curve point is automatically non-identity (`ne_zero_of_onCurve`),
  -- so a single `OnCurve` hint captures both the non-id error path and the curve constraint.
  ProverAssumptions input _ _ := input.OnCurve
  ProverSpec input output _ _ := output = input

  soundness := by
    circuit_proof_start2 [pointNonIdGate, curveEqn]
    grind [Halo2.Ironwood.Point.OnCurve]

  completeness := by
    circuit_proof_start2 [pointNonIdGate, curveEqn]
    refine ⟨?_, region_0, region_1⟩
    simp only [region_0, region_1]
    have hc : input_y ^ 2 = input_x ^ 3 + Halo2.Ironwood.pallasB := prover_assumptions
    linear_combination hc

/-- The layouter-level point witnesses: the region bundles in their own regions, named
once here as in the Rust chip (`ecc/chip/witness_point.rs`). -/
def pointFormal :=
  point.toFormal "witness point"

def pointNonIdFormal :=
  pointNonId.toFormal "witness non-identity point"

derive_contract_bridges pointFormal := pointFormal

derive_contract_bridges pointNonIdFormal := pointNonIdFormal

/-- The output cells of the lifted `pointNonId` (row 0 of its own region). -/
theorem pointNonIdFormal_output (cfg : Config)
    (input : Var (Unconstrained Point) Fp) (i : RegionIndex) :
    pointNonIdFormal.output cfg input i
      = { x := AssignedCell.of i 0 cfg.x, y := AssignedCell.of i 0 cfg.y } := rfl

end WitnessPoint

end Halo2.Ironwood.Ecc
