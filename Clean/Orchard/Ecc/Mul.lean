import Clean.Orchard.Ecc.Defs
import Clean.Orchard.Specs.CompElliptic.CurveForms.ShortWeierstrass

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul.rs`.
-/

namespace Orchard.Ecc.Mul

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

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertBool (lsb row)
  assertZero (lsbX row)
  assertZero (lsbY row)

def circuit : FormalAssertion Fp Input where
  name := "GATE LSB check"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, SelectedCorrectionPoint, lsb, lsbX, lsbY,
      CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_holds with ⟨hBool, hX, hY⟩
    rcases h_input with ⟨hz1, hz0, hxP, hyP, hbaseX, hbaseY⟩
    constructor
    · simpa [sub_eq_add_neg] using hBool
    constructor
    · intro hBit
      apply Prod.ext
      · have hX' := hX
        simp [circuit_norm, ternary, hz0, hz1, hxP, hbaseX] at hX'
        apply sub_eq_zero.mp
        linear_combination hX' - input_baseX * hBit
      · have hY' := hY
        simp [circuit_norm, ternary, hz0, hz1, hyP, hbaseY] at hY'
        linear_combination hY' + input_baseY * hBit
    · intro hBit
      apply Prod.ext
      · have hX' := hX
        simp [circuit_norm, ternary, hz0, hz1, hxP, hbaseX] at hX'
        linear_combination hX' - input_baseX * hBit
      · have hY' := hY
        simp [circuit_norm, ternary, hz0, hz1, hyP, hbaseY] at hY'
        linear_combination hY' + input_baseY * hBit
  completeness := by
    circuit_proof_start [main, Spec, SelectedCorrectionPoint, lsb, lsbX, lsbY,
      CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_spec with ⟨hBool, hSelect⟩
    rcases h_input with ⟨hz1, hz0, hxP, hyP, hbaseX, hbaseY⟩
    constructor
    · simpa [sub_eq_add_neg] using hBool
    constructor
    · rcases hBool with hBit | hBit
      · exact by
          have hPoint := hSelect.1 hBit
          have hx := congrArg Prod.fst hPoint
          simp at hx
          simp [circuit_norm, ternary, hz0, hz1, hxP, hbaseX, hx]
          left
          simpa [sub_eq_add_neg] using hBit
      · exact by
          have hPoint := hSelect.2 hBit
          have hx := congrArg Prod.fst hPoint
          simp at hx
          simp [circuit_norm, ternary, hz0, hz1, hxP, hbaseX, hx]
          left
          linear_combination -hBit
    · rcases hBool with hBit | hBit
      · exact by
          have hPoint := hSelect.1 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hz0, hz1, hyP, hbaseY, hy]
          left
          simpa [sub_eq_add_neg] using hBit
      · exact by
          have hPoint := hSelect.2 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hz0, hz1, hyP, hbaseY, hy]
          left
          linear_combination -hBit

end Gate

end Orchard.Ecc.Mul
