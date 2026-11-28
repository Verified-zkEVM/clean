module

public import Clean.Circuit
public import CompElliptic.CurveForms.ShortWeierstrass
public import Clean.Ironwood.Specs.Pallas
public import Clean.Utils.Tactics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-
Some definitions useful for circuits involving points
-/
namespace Zcash.Circuits

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

end Zcash.Circuits

namespace Zcash.Circuits.Ecc

/-- Shared helpers for the scalar-multiplication gates. -/
def ternary {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K]
    (choice ifTrue ifFalse : K) : K :=
  choice * ifTrue + (1 - choice) * ifFalse

def tQ {K : Type} [OfNat K 45560315531506369815346746415080538113] : K :=
  OfNat.ofNat 45560315531506369815346746415080538113

lemma sw_add_coords (P Q : CompElliptic.CurveForms.ShortWeierstrass.SWPoint CompElliptic.Curves.Pasta.Pallas.curve) :
  CompElliptic.CurveForms.ShortWeierstrass.add pallasA (P.x, P.y) (Q.x, Q.y) = ((P + Q).x, (P + Q).y) := rfl

end Zcash.Circuits.Ecc
