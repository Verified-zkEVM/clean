import Clean.Circuit
import Clean.Orchard.Specs.Elliptic.Curves.Pasta
import Clean.Orchard.Specs.Elliptic.CurveForms.ShortWeierstrass
import Clean.Utils.Tactics
import Mathlib.Tactic

/-!
# Orchard ECC definitions

Shared Pallas field and point definitions used by the Orchard ECC circuits.
-/

namespace Orchard
namespace Ecc

variable {F : Type} [Field F]

abbrev Fp := CompElliptic.Fields.Pasta.PallasBaseField
abbrev Fq := CompElliptic.Fields.Pasta.PallasScalarField

def pallasB : F := 5

structure Point (F : Type) where
  x : F
  y : F

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

namespace Point

@[circuit_norm]
theorem eval_eq (env : Environment F) (point : Point (Expression F)) :
    eval env point = ({ x := env point.x, y := env point.y } : Point F) := by
  with_unfolding_all rfl

def onCurve (point : Point F) : Prop :=
  point.y * point.y - point.x * point.x * point.x - pallasB = 0

def isIdentityEncoding (point : Point F) : Prop :=
  point.x = 0 ∧ point.y = 0

def isPointOrIdentity (point : Point F) : Prop :=
  isIdentityEncoding point ∨ onCurve point

def coords (point : Point F) : F × F :=
  (point.x, point.y)

def neg [Neg F] (point : Point F) : Point F where
  x := point.x
  y := -point.y

end Point

end Ecc
end Orchard
