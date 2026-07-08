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
  pointGate : Gate Fp
  pointNonIdGate : Gate Fp

def configure (x y : Column .advice) : Configure Fp Config := do
  let qPoint ← selector
  let qPointNonId ← selector

  let curveEqn : Expression Fp Query :=
    let x : Expression Fp _ := queryAdvice x 0
    let y : Expression Fp _ := queryAdvice y 0
    -- y^2 = x^3 + b
    y * y - x * x * x - pallasB

  let pointGate ← createGate "witness point" qPoint <|
    let qPoint := querySelector qPoint
    let x := queryAdvice x 0
    let y := queryAdvice y 0
    [
      ⟨ "x == 0 v on_curve", qPoint * x * curveEqn ⟩,
      ⟨ "y == 0 v on_curve", qPoint * y * curveEqn ⟩
    ]

  let pointNonIdGate ← createGate "witness non-identity point" qPointNonId <|
    let qPointNonId := querySelector qPointNonId
    [⟨"on_curve", qPointNonId * curveEqn⟩]

  return { qPoint, qPointNonId, x, y, pointGate, pointNonIdGate }

def point (config : Config) (offset : ℕ) : FormalRegionCircuit Fp (Unconstrained Point) Point where
  main (point : Point (FExpr Fp)) := do
    -- enable "witness point" gate
    config.pointGate.enable offset
    -- assign the x and y values
    let xVar ← assignAdvice config.x offset (.ofFExpr point.x)
    let yVar ← assignAdvice config.y offset (.ofFExpr point.y)
    return ⟨ xVar, yVar ⟩

  elaborated := {}

  Spec _ output _ := output.Valid
  ProverAssumptions input _ := input.Valid
  ProverSpec input output _ := output = input

  soundness := by sorry
  completeness := by sorry

end WitnessPoint

end Halo2.Ironwood.Ecc
