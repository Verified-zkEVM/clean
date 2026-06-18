import Clean.Circuit
import Clean.Orchard.Specs.CompElliptic.CurveForms.ShortWeierstrass
import Clean.Orchard.Specs.Pallas
import Clean.Utils.Tactics
import Mathlib.Tactic

/-
Some definitions useful for circuits involving points
-/
namespace Orchard
variable {F : Type} [Field F]

structure CurrentNext (F : Type) where
  curr : F
  next : F
deriving ProvableStruct

instance : ProvableType Point where
  size := 2
  toElements point := #v[point.x, point.y]
  fromElements elems := {
    x := elems[0]
    y := elems[1]
  }

@[circuit_norm]
theorem Point.eval_eq (env : Environment F) (point : Point (Expression F)) :
    eval env point = { x := env point.x, y := env point.y } := by
  with_unfolding_all rfl

end Orchard
