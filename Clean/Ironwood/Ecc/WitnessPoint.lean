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
    -- rewrite to the intro'd-values form (input/output become plain values)
    rw [FormalRegionCircuit.soundness_iff]
    -- name + destructure input/output; `input` is `Unit` here (Unconstrained input)
    rintro self env input_var input ⟨ox, oy⟩ h_input h_output _hA hc
    -- reduce the gate constraints, and split the output-value equation into coordinates
    simp only [circuit_norm, pointGate, curveEqn, explicit_provable_type, Orchard.Point.mk.injEq]
      at hc h_output
    -- rewrite eval → value: the constraints get stated over the abstract coords `ox`/`oy`
    -- (NOT `subst`, which would splat eval back into the goal — the wrong direction)
    rw [h_output.1, h_output.2] at hc
    obtain ⟨hx, hy⟩ := hc
    -- clear the framework plumbing: nothing below mentions cells, envs, or vars
    clear h_output h_input _hA input_var input env self config offset
    -- ══ user-facing half: pure field values + curve math ══
    -- hx : ox * (oy * oy - ox * ox * ox - pallasB) = 0
    -- hy : oy * (oy * oy - ox * ox * ox - pallasB) = 0
    -- ⊢ ({ x := ox, y := oy } : Point Fp).Valid
    exact point_valid hx hy

  completeness := by
    -- ══ framework/tactic half: strip all `eval`/vars, land on pure field values ══
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    rintro self ⟨place, penv⟩ input_var ⟨ix, iy⟩ ⟨ox, oy⟩ h_input h_output hwit hpa
    -- reduce constraints; split every struct equation (`hwit`/`h_input`/`h_output`/goal)
    -- into coordinates
    simp only [circuit_norm, pointGate, curveEqn, explicit_provable_type,
      Point.witgen_eval_eq, Orchard.Point.mk.injEq] at hwit hpa h_input h_output ⊢
    -- the honest prover assigns the input's coordinates, so `output = input`. Chain the
    -- three coordinate equations to eliminate the output vars in favor of `ix`/`iy`:
    --   cell = ox  (h_output),  cell = witness  (hwit),  witness = ix  (h_input)
    obtain ⟨hox, hoy⟩ := h_output
    obtain ⟨hwx, hwy⟩ := hwit
    obtain ⟨hix, hiy⟩ := h_input
    rw [hox, hoy]                                    -- constraint cells → ox, oy
    have hoxix : ox = ix := hox.symm.trans (hwx.trans hix)
    have hoyiy : oy = iy := hoy.symm.trans (hwy.trans hiy)
    subst hoxix hoyiy                                -- identify input/output coords; goal now pure
    clear hox hoy hwx hwy hix hiy input_var penv place self config offset
    -- ══ user-facing half: pure field values + curve math ══
    -- hpa : ({ x := ox, y := oy } : Point Fp).Valid
    -- ⊢ (ox * (…) = 0 ∧ oy * (…) = 0) ∧ ox = ox ∧ oy = oy
    exact ⟨point_products_of_valid hpa, rfl, rfl⟩

end WitnessPoint

end Halo2.Ironwood.Ecc
