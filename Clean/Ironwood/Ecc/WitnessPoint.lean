import Clean.Halo2
import Clean.Orchard.Specs.Pallas
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

/-- The curve gate's two product constraints imply the point is a valid Pallas point
(on-curve, or the `(0,0)` identity). The algebraic core of witness_point soundness. -/
theorem point_valid {xv yv : Fp}
    (hx : xv * (yv * yv - xv * xv * xv - pallasB) = 0)
    (hy : yv * (yv * yv - xv * xv * xv - pallasB) = 0) :
    ({ x := xv, y := yv } : Point Fp).Valid := by
  by_cases hxz : xv = 0
  · by_cases hyz : yv = 0
    · exact Or.inr (by simp [Orchard.Point.zero_def, hxz, hyz])
    · refine Or.inl ?_
      have h := (mul_eq_zero.mp hy).resolve_left hyz
      show yv ^ 2 = xv ^ 3 + pallasB
      linear_combination h
  · refine Or.inl ?_
    have h := (mul_eq_zero.mp hx).resolve_left hxz
    show yv ^ 2 = xv ^ 3 + pallasB
    linear_combination h

/-- Converse of `point_valid`: a valid point satisfies the gate's product constraints.
The algebraic core of witness_point completeness. -/
theorem point_products_of_valid {xv yv : Fp}
    (h : ({ x := xv, y := yv } : Point Fp).Valid) :
    xv * (yv * yv - xv * xv * xv - pallasB) = 0 ∧ yv * (yv * yv - xv * xv * xv - pallasB) = 0 := by
  rcases h with hoc | hz
  · have heq : yv * yv - xv * xv * xv - pallasB = 0 := by
      have h2 : yv ^ 2 = xv ^ 3 + pallasB := hoc
      linear_combination h2
    rw [heq]; exact ⟨by ring, by ring⟩
  · rw [Orchard.Point.zero_def, Orchard.Point.mk.injEq] at hz
    obtain ⟨hx0, hy0⟩ := hz
    subst hx0; subst hy0; exact ⟨by ring, by ring⟩

/-- The non-identity gate's single curve constraint is exactly `OnCurve`: the point satisfies
the short-Weierstrass equation `y² = x³ + b`. Unlike `pointGate`, there is no `(0,0)` identity
escape hatch — the constraint is `curveEqn` alone, so it forces the point strictly on-curve.
Algebraic core of `witness_point_non_id` soundness. -/
theorem point_onCurve {xv yv : Fp}
    (h : yv * yv - xv * xv * xv - pallasB = 0) :
    ({ x := xv, y := yv } : Point Fp).OnCurve := by
  show yv ^ 2 = xv ^ 3 + pallasB
  linear_combination h

/-- Converse of `point_onCurve`: an on-curve point satisfies the non-identity gate's curve
constraint. Algebraic core of `witness_point_non_id` completeness. -/
theorem curve_eqn_of_onCurve {xv yv : Fp}
    (h : ({ x := xv, y := yv } : Point Fp).OnCurve) :
    yv * yv - xv * xv * xv - pallasB = 0 := by
  have h2 : yv ^ 2 = xv ^ 3 + pallasB := h
  linear_combination h2

def point :
    FormalRegionCircuit Fp (Column .advice × Column .advice) Config
      (Unconstrained Point) Point where
  configure := fun (x, y) => configure x y
  synthesize config offset (point : Point (FExpr Fp)) := do
    -- enable "witness point" gate
    (pointGate config.qPoint config.x config.y).enable offset
    -- assign the x and y values
    let xVar ← assignAdvice config.x offset (.ofFExpr point.x)
    let yVar ← assignAdvice config.y offset (.ofFExpr point.y)
    return ⟨ xVar, yVar ⟩

  Spec _ output _ := output.Valid
  ProverAssumptions input _ := input.Valid
  ProverSpec input output _ := output = input

  soundness := by
    -- ══ framework/tactic half: strip all `eval`/vars, land on pure field values ══
    -- The steps here are exactly what the smart eval-split tactic will do mechanically.
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    -- reduce circuit structure (gates, `.output`, monad), running the eval simprocs
    simp only [circuit_norm, pointGate, curveEqn] at hc h_output
    -- destructure `output` and split its (now-literal) eval equation into coordinates
    provable_type_simp
    -- eval → value: state the constraints over the abstract output coords
    simp only [h_output] at hc
    -- ══ user-facing half: pure field values + curve math ══
    obtain ⟨hx, hy⟩ := hc
    exact point_valid hx hy

  completeness := by
    -- ══ framework/tactic half: strip all `eval`/vars, land on pure field values ══
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hassum hpa
    -- reduce circuit structure (gates, `.output`, monad), running the eval simprocs
    simp only [circuit_norm, pointGate, curveEqn] at hwit hpa h_input h_output ⊢
    -- destructure input/output/input_var; split every struct equation into coordinates
    -- (verifier + witgen evals)
    provable_type_simp
    -- eval → value: cell = witness (`hwit`) = input coord (`h_input`); state the goal over
    -- the input coords, and the output = input relation via `h_output`
    simp only [hwit, h_input] at h_output ⊢
    -- ══ user-facing half: pure field values + curve math ══
    exact ⟨point_products_of_valid hpa, h_output.1.symm, h_output.2.symm⟩

/-- The "witness non-identity point" bundle (Rust `Config::point_non_id`,
`witness_point.rs:167-186`). Mirrors `point`: enable the `pointNonId` gate at `offset` and
assign x/y; but the gate has no identity escape hatch, so the `Spec` is *strictly* on-curve
(`OnCurve`, not merely `Valid`), matching the Rust guarantee that the witnessed point is a
valid curve point. The Rust additionally errors when the value is known to be the identity;
that non-identity precondition is carried on the honest prover as `ProverAssumptions` (the
input is `Unconstrained`, so — like `point` — the honest-side facts about it live there). -/
def pointNonId :
    FormalRegionCircuit Fp (Column .advice × Column .advice) Config
      (Unconstrained Point) Point where
  configure := fun (x, y) => configure x y
  synthesize config offset (point : Point (FExpr Fp)) := do
    -- enable "witness non-identity point" gate
    (pointNonIdGate config.qPointNonId config.x config.y).enable offset
    -- assign the x and y values
    let xVar ← assignAdvice config.x offset (.ofFExpr point.x)
    let yVar ← assignAdvice config.y offset (.ofFExpr point.y)
    return ⟨ xVar, yVar ⟩

  Spec _ output _ := output.OnCurve
  -- honest-prover precondition: the witnessed point is genuinely on-curve. The Rust errors
  -- on the identity; an on-curve point is automatically non-identity (`ne_zero_of_onCurve`),
  -- so a single `OnCurve` hint captures both the non-id error path and the curve constraint.
  ProverAssumptions input _ := input.OnCurve
  ProverSpec input output _ := output = input

  soundness := by
    -- ══ framework/tactic half: strip all `eval`/vars, land on pure field values ══
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    -- reduce circuit structure (gate, `.output`, monad), running the eval simprocs
    simp only [circuit_norm, pointNonIdGate, curveEqn] at hc h_output
    -- destructure `output`, split its (now-literal) eval equation into coordinates
    provable_type_simp
    -- eval → value: state the single constraint over the abstract output coords
    simp only [h_output] at hc
    -- ══ user-facing half: pure field values + curve math ══
    exact point_onCurve hc

  completeness := by
    -- ══ framework/tactic half: strip all `eval`/vars, land on pure field values ══
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hassum hpa
    -- reduce circuit structure, running the eval simprocs
    simp only [circuit_norm, pointNonIdGate, curveEqn] at hwit hpa h_input h_output ⊢
    -- destructure input/output/input_var; split every struct equation into coordinates
    provable_type_simp
    -- eval → value: cell = witness (`hwit`) = input coord (`h_input`)
    simp only [hwit, h_input] at h_output ⊢
    -- ══ user-facing half: pure field values + curve math ══
    exact ⟨curve_eqn_of_onCurve hpa, h_output.1.symm, h_output.2.symm⟩

end WitnessPoint

end Halo2.Ironwood.Ecc
