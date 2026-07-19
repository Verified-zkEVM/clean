import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Basic

namespace Halo2.Ironwood.Ecc
/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/witness_point.rs`
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

  synthesize config offset (point : Point (FExpr Fp)) := do
    -- enable "witness point" gate
    (pointGate config.qPoint config.x config.y).enable offset
    -- assign the x and y values
    let xVar ← assignAdvice config.x offset (.ofFExpr point.x)
    let yVar ← assignAdvice config.y offset (.ofFExpr point.y)
    return ⟨ xVar, yVar ⟩

  Spec _ output _ := output.Valid
  ProverAssumptions input _ _ := input.Valid
  ProverSpec input output _ _ := output = input

  soundness := by
    circuit_proof_start [pointGate, curveEqn]
    -- ══ user-facing half: pure field values + curve math ══
    grind [Halo2.Ironwood.Point.Valid, Halo2.Ironwood.Point.OnCurve, Halo2.Ironwood.Point.zero_def]

  completeness := by
    circuit_proof_start [pointGate, curveEqn]
    -- ══ user-facing half: pure field values + curve math ══
    grind [Halo2.Ironwood.Point.Valid, Halo2.Ironwood.Point.OnCurve, Halo2.Ironwood.Point.zero_def]

/-- The "witness non-identity point" bundle (Rust `Config::point_non_id`,
`witness_point.rs:167-186`). Mirrors `point`: enable the `pointNonId` gate at `offset` and
assign x/y; but the gate has no identity escape hatch, so the `Spec` is *strictly* on-curve
(`OnCurve`, not merely `Valid`), matching the Rust guarantee that the witnessed point is a
valid curve point. The Rust additionally errors when the value is known to be the identity;
that non-identity precondition is carried on the honest prover as `ProverAssumptions` (the
input is `Unconstrained`, so — like `point` — the honest-side facts about it live there). -/
def pointNonId : FormalRegionCircuit Fp (Column .advice × Column .advice) Config
    (Unconstrained Point) Point where
  configure | (x, y) => configure x y

  synthesize config offset (point : Point (FExpr Fp)) := do
    -- enable "witness non-identity point" gate
    (pointNonIdGate config.qPointNonId config.x config.y).enable offset
    -- assign the x and y values
    let xVar ← assignAdvice config.x offset (.ofFExpr point.x)
    let yVar ← assignAdvice config.y offset (.ofFExpr point.y)
    return ⟨ xVar, yVar ⟩

  Spec _ output _ := output.OnCurve
  -- the witnessed point, published as extraction data (positional cells) so parents can
  -- state honest-prover conditions on the value actually assigned
  Witness := Point
  extract := fun cfg offset _ self env =>
    eval env ({ x := AssignedCell.of self offset cfg.x,
                y := AssignedCell.of self offset cfg.y } : Var Point Fp)
  -- honest-prover precondition: the witnessed point is genuinely on-curve. The Rust errors
  -- on the identity; an on-curve point is automatically non-identity (`ne_zero_of_onCurve`),
  -- so a single `OnCurve` hint captures both the non-id error path and the curve constraint.
  -- Stated at the extracted cell values (not the program), so parents discharge it from
  -- their own extract-level assumptions.
  ProverAssumptions _ wit _ := wit.OnCurve
  ProverSpec input output _ _ := output = input

  soundness := by
    circuit_proof_start [pointNonIdGate, curveEqn]
    -- ══ user-facing half: pure field values + curve math ══
    grind [Halo2.Ironwood.Point.OnCurve]

  completeness := by
    circuit_proof_start [pointNonIdGate, curveEqn]
    -- ══ user-facing half: pure field values + curve math ══
    grind [Halo2.Ironwood.Point.OnCurve]

/-! ## Layouter-level bridges for `pointNonId.toFormal`, shared by the consumers
(`rfl`, the bundle stays folded) -/

section Bridges

variable (name : String)

theorem pointNonId_toFormal_spec_eq :
    (pointNonId.toFormal name).Spec
      = fun _ (output : Point Fp) (_ : Point Fp) => output.OnCurve := rfl

theorem pointNonId_toFormal_assumptions_eq :
    (pointNonId.toFormal name).Assumptions = fun _ => True := rfl

theorem pointNonId_toFormal_proverAssumptions_eq :
    (pointNonId.toFormal name).ProverAssumptions
      = fun _ (wit : Point Fp) _ => wit.OnCurve := rfl

theorem pointNonId_toFormal_proverSpec_eq :
    (pointNonId.toFormal name).ProverSpec
      = fun (input : Point Fp) (output : Point Fp) (_ : Point Fp) _ =>
          output = input := rfl

theorem pointNonId_toFormal_extract_eq (cfg : Config)
    (input : Var (Unconstrained Point) Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (pointNonId.toFormal name).extract cfg input i env
      = (eval env ({ x := AssignedCell.of i 0 cfg.x,
                     y := AssignedCell.of i 0 cfg.y } : Var Point Fp)
          : Value Point Fp) := rfl

/-- The output cells of the lifted `pointNonId` (row 0 of its own region). -/
theorem pointNonId_toFormal_output (cfg : Config)
    (input : Var (Unconstrained Point) Fp) (i : RegionIndex) :
    (pointNonId.toFormal name).output cfg input i
      = { x := AssignedCell.of i 0 cfg.x, y := AssignedCell.of i 0 cfg.y } := rfl

/-- The lifted `pointNonId`'s call chunk is one region. -/
theorem pointNonId_toFormal_call_regionCount (cfg : Config)
    (input : Var (Unconstrained Point) Fp) (j : RegionIndex) :
    Operations.regionCount
      (((pointNonId.toFormal name).call cfg input).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

end Bridges

end WitnessPoint

end Halo2.Ironwood.Ecc
