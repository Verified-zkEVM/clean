import Clean.Orchard.Ecc.ScalarMul.Defs

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed.rs`.
-/

namespace Orchard.Ecc.ScalarMul.MulFixed

structure CoordsParams (F : Type) where
  z : F
  lagrange0 : F
  lagrange1 : F
  lagrange2 : F
  lagrange3 : F
  lagrange4 : F
  lagrange5 : F
  lagrange6 : F
  lagrange7 : F

def CoordsParams.toExpr (params : CoordsParams Fp) :
    CoordsParams (Expression Fp) where
  z := params.z
  lagrange0 := params.lagrange0
  lagrange1 := params.lagrange1
  lagrange2 := params.lagrange2
  lagrange3 := params.lagrange3
  lagrange4 := params.lagrange4
  lagrange5 := params.lagrange5
  lagrange6 := params.lagrange6
  lagrange7 := params.lagrange7

structure CoordsRow (F : Type) where
  window : F
  xP : F
  yP : F
  u : F
deriving ProvableStruct

def interpolatedX {K : Type} [Add K] [Mul K] (params : CoordsParams K) (row : CoordsRow K) : K :=
  params.lagrange0 +
    row.window * params.lagrange1 +
    row.window * row.window * params.lagrange2 +
    row.window * row.window * row.window * params.lagrange3 +
    row.window * row.window * row.window * row.window * params.lagrange4 +
    row.window * row.window * row.window * row.window * row.window * params.lagrange5 +
    row.window * row.window * row.window * row.window * row.window * row.window * params.lagrange6 +
    row.window * row.window * row.window * row.window * row.window * row.window * row.window *
      params.lagrange7

def xCheck {K : Type} [Add K] [Sub K] [Mul K] (params : CoordsParams K) (row : CoordsRow K) :
    K :=
  interpolatedX params row - row.xP

def yCheck {K : Type} [Sub K] [Mul K] (params : CoordsParams K) (row : CoordsRow K) : K :=
  row.u * row.u - row.yP - params.z

def onCurve {K : Type} [Sub K] [Mul K] [OfNat K 5] (row : CoordsRow K) : K :=
  row.yP * row.yP - row.xP * row.xP * row.xP - 5

namespace Coords

def Spec (params : CoordsParams Fp) (row : CoordsRow Fp) :
    Prop :=
  row.xP = interpolatedX params row ∧
    row.u * row.u = row.yP + params.z ∧
    row.yP * row.yP = row.xP * row.xP * row.xP + 5

def main (params : CoordsParams Fp) (row : Var CoordsRow Fp) :
    Circuit Fp Unit := do
  assertZero (xCheck params.toExpr row)
  assertZero (yCheck params.toExpr row)
  assertZero (onCurve row)

def circuit (params : CoordsParams Fp) :
    FormalAssertion Fp CoordsRow where
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, xCheck, yCheck, onCurve, interpolatedX]
    rcases h_holds with ⟨hx, hy, hCurve⟩
    simp [CoordsParams.toExpr, circuit_norm] at hx hy
    exact ⟨(sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hx)).symm,
      by linear_combination hy,
      by linear_combination hCurve⟩
  completeness := by
    circuit_proof_start [main, Spec, xCheck, yCheck, onCurve, interpolatedX]
    rcases h_spec with ⟨hx, hy, hCurve⟩
    simp [CoordsParams.toExpr, circuit_norm]
    exact ⟨by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hx.symm,
      by linear_combination hy,
      by linear_combination hCurve⟩

end Coords

namespace RunningSumCoords

structure Row (F : Type) extends CoordsRow F where
  zCur : F
  zNext : F
deriving ProvableStruct

def word {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Row K) : K :=
  row.zCur - row.zNext * 8

def coordsRow {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Row K) : CoordsRow K :=
  { row.toCoordsRow with window := word row }

def Spec (params : CoordsParams Fp) (row : Row Fp) : Prop :=
  Coords.Spec params (coordsRow row)

def main (params : CoordsParams Fp) (row : Var Row Fp) :
    Circuit Fp Unit := do
  Coords.circuit params { row.toCoordsRow with window := word row }

def circuit (params : CoordsParams Fp) : FormalAssertion Fp Row where
  name := "GATE Running sum coordinates check"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, coordsRow, Coords.circuit, Coords.Spec, word]
    simpa [sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Spec, coordsRow, Coords.circuit, Coords.Spec, word]
    simpa [sub_eq_add_neg] using h_spec

end RunningSumCoords

end Orchard.Ecc.ScalarMul.MulFixed
