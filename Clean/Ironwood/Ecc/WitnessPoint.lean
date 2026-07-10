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

def point (config : Config) (offset : ℕ) : FormalRegionCircuit Fp (Unconstrained Point) Point where
  main (point : Point (FExpr Fp)) := do
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
    -- easily automatable tactic layer.
    -- TODO(tactic): the input/output eval-split lemmas (here `Point.eval_eq`) still have
    -- to be chosen by hand; `circuit_proof_start` should derive them from the I/O types.
    intro self env input _ hc
    simp only [circuit_norm, pointGate, curveEqn, Point.eval_eq] at hc ⊢
    -- normal user-facing proof
    obtain ⟨hx, hy⟩ := hc
    exact point_valid hx hy

  completeness := by
    -- easily automatable tactic layer.
    -- TODO(tactic): the eval-split lemmas (`Point.eval_eq_prover`, `Point.witgen_eval_eq`)
    -- still have to be chosen by hand; the tactic should derive them from the I/O types.
    rintro self ⟨place, penv⟩ input hwit hpa
    simp only [circuit_norm, pointGate, curveEqn,
      Point.eval_eq_prover, Point.witgen_eval_eq] at hwit hpa ⊢
    -- normal user-facing proof
    obtain ⟨hpx, hpy⟩ := point_products_of_valid hpa
    simp_all

end WitnessPoint

end Halo2.Ironwood.Ecc
