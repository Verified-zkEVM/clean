import Clean.Ironwood.Ecc.Defs
import CompElliptic.CurveForms.ShortWeierstrass

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul.rs`.
-/

namespace Halo2.Ironwood.Ecc.Mul

namespace Gate

structure Input (F : Type) where
  z1 : F
  z0 : F
  xP : F
  yP : F
  baseX : F
  baseY : F
deriving ProvableStruct

def lsb {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Input K) : K :=
  row.z0 - row.z1 * 2

def lsbX {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Input K) : K :=
  ternary (lsb row) row.xP (row.xP - row.baseX)

def lsbY {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Input K) : K :=
  ternary (lsb row) row.yP (row.yP + row.baseY)

def SelectedCorrectionPoint (row : Input Fp) : Prop :=
  (lsb row = 0 →
    (row.xP, row.yP) =
      CompElliptic.CurveForms.ShortWeierstrass.neg (row.baseX, row.baseY)) ∧
    (lsb row = 1 →
      (row.xP, row.yP) = (0, 0))

def Spec (row : Input Fp) : Prop :=
  IsBool (lsb row) ∧ SelectedCorrectionPoint row

end Gate

end Halo2.Ironwood.Ecc.Mul
