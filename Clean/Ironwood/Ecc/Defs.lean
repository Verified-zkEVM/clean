import Clean.Circuit
import CompElliptic.CurveForms.ShortWeierstrass
import Clean.Ironwood.Specs.Pallas
import Clean.Utils.Tactics
import Mathlib.Tactic

/-
Some definitions useful for circuits involving points
-/
namespace Halo2.Ironwood
variable {F : Type} [FiniteField F]

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

end Halo2.Ironwood

namespace Halo2.Ironwood.Ecc

/-- Shared helpers for the scalar-multiplication gates. -/

def ternary {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K]
    (choice ifTrue ifFalse : K) : K :=
  choice * ifTrue + (1 - choice) * ifFalse

def tQ {K : Type} [OfNat K 45560315531506369815346746415080538113] : K :=
  OfNat.ofNat 45560315531506369815346746415080538113

lemma sw_add_coords (P Q : CompElliptic.CurveForms.ShortWeierstrass.SWPoint CompElliptic.Curves.Pasta.Pallas.curve) :
  CompElliptic.CurveForms.ShortWeierstrass.add pallasA (P.x, P.y) (Q.x, Q.y) = ((P + Q).x, (P + Q).y) := rfl

end Halo2.Ironwood.Ecc
