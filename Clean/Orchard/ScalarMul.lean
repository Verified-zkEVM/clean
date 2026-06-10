import Clean.Circuit
import Clean.Orchard.NoteCommit
import Clean.Orchard.Sinsemilla
import Clean.Orchard.Specs.Elliptic.CurveForms.ShortWeierstrass
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Tactic

/-!
# Orchard scalar multiplication gates

Clean approximations of direct scalar-multiplication custom gates from `halo2_gadgets`.

References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul.rs`
- `LSB check`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `q_mul_1 == 1 checks`
- shared `for_loop` constraints for `q_mul_2 == 1 checks` and `q_mul_3 == 1 checks`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/overflow.rs`
- `overflow checks`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/complete.rs`
- `Decompose scalar for complete bits of variable-base mul`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed.rs`
- `Running sum coordinates check`
- `coords_check`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`
- `Full-width fixed-base scalar mul`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`
- `Canonicity checks`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`
- `Short fixed-base mul gate`

These assertions model the enabled gate polynomials, not row rotations, selectors,
lookups, fixed-base tables, or copy constraints around the gates.
-/

namespace Orchard
namespace ScalarMul

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2]

def ternary (choice ifTrue ifFalse : R) : R :=
  choice * ifTrue + (1 - choice) * ifFalse

def tQ [OfNat R 45560315531506369815346746415080538113] : R :=
  OfNat.ofNat 45560315531506369815346746415080538113

def IsBool (x : R) : Prop :=
  x = 0 ∨ x = 1

private theorem isBool_of_boolPoly_eq_zero {x : F} (h : NoteCommit.boolPoly x = 0) :
    IsBool x := by
  unfold NoteCommit.boolPoly at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

private theorem boolPoly_eq_zero_of_isBool {x : F} (h : IsBool x) :
    NoteCommit.boolPoly x = 0 := by
  rcases h with h | h <;> rw [h] <;> simp [NoteCommit.boolPoly]

namespace VarBaseLSB

structure Row (F : Type) where
  z1 : F
  z0 : F
  xP : F
  yP : F
  baseX : F
  baseY : F
deriving ProvableStruct

def lsb {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  row.z0 - row.z1 * 2

def lsbX {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Row K) : K :=
  ternary (lsb row) row.xP (row.xP - row.baseX)

def lsbY {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Row K) : K :=
  ternary (lsb row) row.yP (row.yP + row.baseY)

def SelectedCorrectionPoint (row : Row Ecc.PallasBaseField) : Prop :=
  (lsb row = 0 →
    (row.xP, row.yP) =
      CompElliptic.CurveForms.ShortWeierstrass.neg (row.baseX, row.baseY)) ∧
    (lsb row = 1 →
      (row.xP, row.yP) = (0, 0))

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  IsBool (lsb row) ∧ SelectedCorrectionPoint row

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (NoteCommit.boolPoly (lsb row))
  assertZero (lsbX row)
  assertZero (lsbY row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, SelectedCorrectionPoint, NoteCommit.boolPoly,
      lsb, lsbX, lsbY, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_holds with ⟨hBool, hX, hY⟩
    rcases h_input with ⟨hz1, hz0, hxP, hyP, hbaseX, hbaseY⟩
    constructor
    · exact isBool_of_boolPoly_eq_zero (by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBool)
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
    circuit_proof_start [main, Spec, SelectedCorrectionPoint, NoteCommit.boolPoly,
      lsb, lsbX, lsbY, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_spec with ⟨hBool, hSelect⟩
    rcases h_input with ⟨hz1, hz0, hxP, hyP, hbaseX, hbaseY⟩
    constructor
    · exact by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hBool
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

end VarBaseLSB

namespace VarBaseCompleteBit

structure Row (F : Type) where
  zPrev : F
  zNext : F
  baseY : F
  yP : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  row.zNext - 2 * row.zPrev

def ySwitch {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Row K) : K :=
  ternary (bit row) (row.baseY - row.yP) (row.baseY + row.yP)

def SelectedCompleteBitPoint (row : Row Ecc.PallasBaseField) : Prop :=
  ∀ x : Ecc.PallasBaseField,
    (bit row = 0 →
      (x, row.yP) = CompElliptic.CurveForms.ShortWeierstrass.neg (x, row.baseY)) ∧
      (bit row = 1 →
        (x, row.yP) = (x, row.baseY))

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  IsBool (bit row) ∧ SelectedCompleteBitPoint row

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (ySwitch row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, SelectedCompleteBitPoint,
      NoteCommit.boolPoly, bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_holds with ⟨hBool, hSwitch⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · exact isBool_of_boolPoly_eq_zero (by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBool)
    · intro x
      constructor
      · intro hBit
        apply Prod.ext
        · rfl
        · have hSwitch' := hSwitch
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP] at hSwitch'
          linear_combination hSwitch' + (2 * input_yP) * hBit
      · intro hBit
        apply Prod.ext
        · rfl
        · have hSwitch' := hSwitch
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP] at hSwitch'
          have hBitNorm : input_zNext + -(2 * input_zPrev) = 1 := by
            linear_combination hBit
          have hCoeff : 1 + (2 * input_zPrev + -input_zNext) = 0 := by
            linear_combination -hBitNorm
          have hDiff : input_baseY + -input_yP = 0 := by
            linear_combination hSwitch' - (input_baseY + -input_yP) * hBitNorm -
              (input_baseY + input_yP) * hCoeff
          linear_combination -hDiff
  completeness := by
    circuit_proof_start [main, Spec, SelectedCompleteBitPoint,
      NoteCommit.boolPoly, bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_spec with ⟨hBool, hSelect⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · exact by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hBool
    · rcases hBool with hBit | hBit
      · exact by
          have hPoint := (hSelect 0).1 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP, hy]
          left
          simpa [sub_eq_add_neg] using hBit
      · exact by
          have hPoint := (hSelect 0).2 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP, hy]
          left
          linear_combination -hBit

end VarBaseCompleteBit

namespace VarBaseIncomplete

/- The Rust gate uses `y_a = Y_A / 2`. These constraints multiply those
   equations by `2`, avoiding a division operation while preserving the Pallas
   gate's zero set. -/
def yADouble {K : Type} [Add K] [Sub K] [Mul K] (row : Sinsemilla.DoubleAndAddRow K) : K :=
  Sinsemilla.DoubleAndAdd.yA row

namespace Init

structure Row (F : Type) where
  yAWitnessed : F
  next : Sinsemilla.DoubleAndAddRow F
deriving ProvableStruct

def poly {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  2 * row.yAWitnessed - yADouble row.next

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  2 * row.yAWitnessed = yADouble row.next

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (poly row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, poly, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h_holds)
  completeness := by
    circuit_proof_start [main, Spec, poly, yADouble, Sinsemilla.DoubleAndAdd.yA,
      Sinsemilla.DoubleAndAdd.xR]
    exact by simpa [sub_eq_add_neg] using sub_eq_zero.mpr h_spec

end Init

namespace Loop

structure Row (F : Type) where
  zCur : F
  zPrev : F
  cur : Sinsemilla.DoubleAndAddRow F
  xANext : F
  yPCur : F
  yANextDouble : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  row.zCur - row.zPrev * 2

def gradient1 {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Row K) : K :=
  2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) - yADouble row.cur +
    2 * ((bit row * 2 - 1) * row.yPCur)

def secantLine {K : Type} [Sub K] [Mul K] (row : Row K) : K :=
  row.cur.lambda2 * row.cur.lambda2 - row.xANext -
    Sinsemilla.DoubleAndAdd.xR row.cur - row.cur.xA

def gradient2 {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  2 * row.cur.lambda2 * (row.cur.xA - row.xANext) - yADouble row.cur - row.yANextDouble

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  IsBool (bit row) ∧
    2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) +
        2 * ((bit row * 2 - 1) * row.yPCur) = yADouble row.cur ∧
    row.cur.lambda2 * row.cur.lambda2 =
        row.xANext + Sinsemilla.DoubleAndAdd.xR row.cur + row.cur.xA ∧
    2 * row.cur.lambda2 * (row.cur.xA - row.xANext) =
        yADouble row.cur + row.yANextDouble

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (gradient1 row)
  assertZero (secantLine row)
  assertZero (gradient2 row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, NoteCommit.boolPoly, bit, gradient1,
      secantLine, gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
    rcases h_holds with ⟨hBool, hGradient1, hSecant, hGradient2⟩
    exact ⟨isBool_of_boolPoly_eq_zero (by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBool),
      by linear_combination hGradient1,
      by linear_combination hSecant,
      by linear_combination hGradient2⟩
  completeness := by
    circuit_proof_start [main, Spec, NoteCommit.boolPoly, bit, gradient1,
      secantLine, gradient2, yADouble, Sinsemilla.DoubleAndAdd.yA, Sinsemilla.DoubleAndAdd.xR]
    rcases h_spec with ⟨hBool, hGradient1, hSecant, hGradient2⟩
    exact ⟨by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hBool,
      by linear_combination hGradient1,
      by linear_combination hSecant,
      by linear_combination hGradient2⟩

end Loop

namespace MainLoop

structure Row (F : Type) extends Loop.Row F where
  xPNext : F
  yPNext : F
deriving ProvableStruct

def xPCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.cur.xP - row.xPNext

def yPCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.yPCur - row.yPNext

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  row.cur.xP = row.xPNext ∧ row.yPCur = row.yPNext ∧ Loop.Spec row.toRow

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (xPCheck row)
  assertZero (yPCheck row)
  Loop.circuit row.toRow

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, xPCheck, yPCheck, Loop.circuit, Loop.Spec]
    rcases h_holds with ⟨hxP, hyP, hLoop⟩
    exact ⟨sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hxP),
      sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hyP),
      hLoop⟩
  completeness := by
    circuit_proof_start [main, Spec, xPCheck, yPCheck, Loop.circuit, Loop.Spec]
    rcases h_spec with ⟨hxP, hyP, hLoop⟩
    exact ⟨by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hxP,
      by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hyP,
      hLoop⟩

end MainLoop

end VarBaseIncomplete

namespace VarBaseOverflow

structure Row (F : Type) where
  z0 : F
  z130 : F
  eta : F
  k254 : F
  alpha : F
  sMinusLo130 : F
  s : F
deriving ProvableStruct

def sCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 130)] (row : Row K) : K :=
  row.s - (row.alpha + row.k254 * OfNat.ofNat (2 ^ 130))

def recovery {K : Type} [Sub K] [OfNat K 2]
    [OfNat K 45560315531506369815346746415080538113] (row : Row K) : K :=
  row.z0 - row.alpha - tQ

def loZero {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 124)] (row : Row K) : K :=
  row.k254 * (row.z130 - OfNat.ofNat (2 ^ 124))

def sMinusLo130Check {K : Type} [Mul K] (row : Row K) : K :=
  row.k254 * row.sMinusLo130

def canonicity {K : Type} [One K] [Sub K] [Mul K] (row : Row K) : K :=
  (1 - row.k254) * (1 - row.z130 * row.eta) * row.sMinusLo130

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  row.s = row.alpha + row.k254 * OfNat.ofNat (2 ^ 130) ∧
    row.z0 = row.alpha + tQ ∧
    (row.k254 = 0 ∨ row.z130 = OfNat.ofNat (2 ^ 124)) ∧
    (row.k254 = 0 ∨ row.sMinusLo130 = 0) ∧
    (row.k254 = 1 ∨ row.z130 * row.eta = 1 ∨ row.sMinusLo130 = 0)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (sCheck row)
  assertZero (recovery row)
  assertZero (loZero row)
  assertZero (sMinusLo130Check row)
  assertZero (canonicity row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, sCheck, recovery, loZero,
      sMinusLo130Check, canonicity, tQ]
    rcases h_holds with ⟨hS, hRecovery, hLoZero, hSMinusLo130, hCanonicity⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hS)
    · apply sub_eq_zero.mp
      linear_combination hRecovery
    · rcases mul_eq_zero.mp hLoZero with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h))
    · rcases mul_eq_zero.mp hSMinusLo130 with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases mul_eq_zero.mp hCanonicity with hK | hRest
      · rcases mul_eq_zero.mp hK with hK | hEta
        · exact Or.inl (by linear_combination -hK)
        · exact Or.inr (Or.inl (by linear_combination -hEta))
      · exact Or.inr (Or.inr hRest)
  completeness := by
    circuit_proof_start [main, Spec, sCheck, recovery, loZero,
      sMinusLo130Check, canonicity, tQ]
    rcases h_spec with ⟨hS, hRecovery, hLoZero, hSMinusLo130, hCanonicity⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hS
    · exact by linear_combination hRecovery
    · exact by
        rcases hLoZero with h | h
        · rw [h]
          simp
        · rw [h]
          simp
    · exact by
        rcases hSMinusLo130 with h | h
        · rw [h]
          simp
        · rw [h]
          simp
    · exact by
        rcases hCanonicity with hK | hRest
        · rw [hK]
          simp
        · rcases hRest with hEta | hSMinusLo130
          · rw [hEta]
            simp
          · rw [hSMinusLo130]
            simp

end VarBaseOverflow

namespace FixedBase

variable [OfNat R 3] [OfNat R 4] [OfNat R 5] [OfNat R 6] [OfNat R 7] [OfNat R 8]

structure CoordsRow (F : Type) where
  window : F
  xP : F
  yP : F
  z : F
  u : F
  lagrange0 : F
  lagrange1 : F
  lagrange2 : F
  lagrange3 : F
  lagrange4 : F
  lagrange5 : F
  lagrange6 : F
  lagrange7 : F
deriving ProvableStruct

def interpolatedX {K : Type} [Add K] [Mul K] (row : CoordsRow K) : K :=
  row.lagrange0 +
    row.window * row.lagrange1 +
    row.window * row.window * row.lagrange2 +
    row.window * row.window * row.window * row.lagrange3 +
    row.window * row.window * row.window * row.window * row.lagrange4 +
    row.window * row.window * row.window * row.window * row.window * row.lagrange5 +
    row.window * row.window * row.window * row.window * row.window * row.window * row.lagrange6 +
    row.window * row.window * row.window * row.window * row.window * row.window * row.window *
      row.lagrange7

def xCheck {K : Type} [Add K] [Sub K] [Mul K] (row : CoordsRow K) : K :=
  interpolatedX row - row.xP

def yCheck {K : Type} [Sub K] [Mul K] (row : CoordsRow K) : K :=
  row.u * row.u - row.yP - row.z

def onCurve {K : Type} [Sub K] [Mul K] [OfNat K 5] (row : CoordsRow K) : K :=
  row.yP * row.yP - row.xP * row.xP * row.xP - 5

def coordsSpec (row : CoordsRow Ecc.PallasBaseField) : Prop :=
  row.xP = interpolatedX row ∧
    row.u * row.u = row.yP + row.z ∧
    row.yP * row.yP = row.xP * row.xP * row.xP + 5

def coordsMain (row : Var CoordsRow Ecc.PallasBaseField) :
    Circuit Ecc.PallasBaseField Unit := do
  assertZero (xCheck row)
  assertZero (yCheck row)
  assertZero (onCurve row)

namespace Coords

def circuit : FormalAssertion Ecc.PallasBaseField CoordsRow where
  main := coordsMain
  Spec := coordsSpec
  soundness := by
    circuit_proof_start [coordsMain, coordsSpec, xCheck, yCheck, onCurve, interpolatedX]
    rcases h_holds with ⟨hx, hy, hCurve⟩
    exact ⟨(sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hx)).symm,
      by linear_combination hy,
      by linear_combination hCurve⟩
  completeness := by
    circuit_proof_start [coordsMain, coordsSpec, xCheck, yCheck, onCurve, interpolatedX]
    rcases h_spec with ⟨hx, hy, hCurve⟩
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

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  coordsSpec (coordsRow row)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Coords.circuit { row.toCoordsRow with window := word row }

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, coordsRow, Coords.circuit, coordsSpec, word]
    simpa [sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Spec, coordsRow, Coords.circuit, coordsSpec, word]
    simpa [sub_eq_add_neg] using h_spec

end RunningSumCoords

namespace FullWidth

def rangeCheck {K : Type} [One K] [Sub K] [Mul K]
    [OfNat K 2] [OfNat K 3] [OfNat K 4] [OfNat K 5] [OfNat K 6] [OfNat K 7]
    (row : CoordsRow K) : K :=
  row.window * (1 - row.window) * (2 - row.window) * (3 - row.window) *
    (4 - row.window) * (5 - row.window) * (6 - row.window) * (7 - row.window)

def IsWindow (window : Ecc.PallasBaseField) : Prop :=
  window = 0 ∨ window = 1 ∨ window = 2 ∨ window = 3 ∨
    window = 4 ∨ window = 5 ∨ window = 6 ∨ window = 7

def Spec (row : CoordsRow Ecc.PallasBaseField) : Prop :=
  coordsSpec row ∧ IsWindow row.window

def main (row : Var CoordsRow Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  Coords.circuit row
  assertZero (rangeCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField CoordsRow where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsWindow, Coords.circuit, coordsMain, coordsSpec,
      rangeCheck, xCheck, yCheck, onCurve, interpolatedX]
    constructor
    · simpa [sub_eq_add_neg] using h_holds.1
    · have hRange := h_holds.2
      rcases mul_eq_zero.mp hRange with hPrefix | h7
      · rcases mul_eq_zero.mp hPrefix with hPrefix | h6
        · rcases mul_eq_zero.mp hPrefix with hPrefix | h5
          · rcases mul_eq_zero.mp hPrefix with hPrefix | h4
            · rcases mul_eq_zero.mp hPrefix with hPrefix | h3
              · rcases mul_eq_zero.mp hPrefix with hPrefix | h2
                · rcases mul_eq_zero.mp hPrefix with h0 | h1
                  · exact Or.inl h0
                  · exact Or.inr (Or.inl (by linear_combination -h1))
                · exact Or.inr (Or.inr (Or.inl (by linear_combination -h2)))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination -h3))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination -h4)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination -h5))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
            linear_combination -h6)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
          linear_combination -h7)))))))
  completeness := by
    circuit_proof_start [main, Spec, IsWindow, Coords.circuit, coordsMain, coordsSpec,
      rangeCheck, xCheck, yCheck, onCurve, interpolatedX]
    constructor
    · simpa [sub_eq_add_neg] using h_spec.1
    · rcases h_spec.2 with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · simp [h3]
      · simp [h4]
      · simp [h5]
      · simp [h6]
      · simp [h7]

end FullWidth

namespace BaseFieldCanonicity

structure Row (F : Type) where
  alpha : F
  z84Alpha : F
  alpha1 : F
  alpha2 : F
  alpha0Prime : F
  z13Alpha0Prime : F
  z44Alpha : F
  z43Alpha : F
deriving ProvableStruct

def alpha0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 252)] (row : Row K) : K :=
  row.alpha - row.z84Alpha * OfNat.ofNat (2 ^ 252)

def alpha1RangeCheck {K : Type} [One K] [Sub K] [Mul K] [OfNat K 2] [OfNat K 3]
    (row : Row K) : K :=
  row.alpha1 * (1 - row.alpha1) * (2 - row.alpha1) * (3 - row.alpha1)

def z84AlphaCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 4] (row : Row K) : K :=
  row.z84Alpha - (row.alpha1 + row.alpha2 * 4)

def alpha0PrimeCheck {K : Type} [Add K] [Sub K] [Mul K]
    [OfNat K (2 ^ 130)] [OfNat K (2 ^ 252)]
    [OfNat K 45560315531419706090280762371685220353] (row : Row K) : K :=
  row.alpha0Prime - (alpha0 row + OfNat.ofNat (2 ^ 130) - NoteCommit.tP)

def alpha0Hi120 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 120)] (row : Row K) : K :=
  row.z44Alpha - row.z84Alpha * OfNat.ofNat (2 ^ 120)

def a43 {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Row K) : K :=
  row.z43Alpha - row.z44Alpha * 8

def IsAlpha1 (alpha1 : Ecc.PallasBaseField) : Prop :=
  alpha1 = 0 ∨ alpha1 = 1 ∨ alpha1 = 2 ∨ alpha1 = 3

def DecomposesBaseFieldElem (row : Row Ecc.PallasBaseField) : Prop :=
  row.z84Alpha = row.alpha1 + row.alpha2 * 4 ∧
    row.alpha0Prime = alpha0 row + OfNat.ofNat (2 ^ 130) - NoteCommit.tP

def CanonicalHighBit (row : Row Ecc.PallasBaseField) : Prop :=
  row.alpha2 = 1 →
    row.alpha1 = 0 ∧ alpha0Hi120 row = 0 ∧ IsBool (a43 row) ∧ row.z13Alpha0Prime = 0

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  IsAlpha1 row.alpha1 ∧ IsBool row.alpha2 ∧ DecomposesBaseFieldElem row ∧
    CanonicalHighBit row

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (row.alpha2 * row.alpha1)
  assertZero (row.alpha2 * alpha0Hi120 row)
  assertZero (row.alpha2 * NoteCommit.boolPoly (a43 row))
  assertZero (row.alpha2 * row.z13Alpha0Prime)
  assertZero (alpha1RangeCheck row)
  assertZero (NoteCommit.boolPoly row.alpha2)
  assertZero (z84AlphaCheck row)
  assertZero (alpha0PrimeCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, NoteCommit.boolPoly, NoteCommit.tP]
    rcases h_holds with ⟨hAlpha21, hAlpha2Hi, hAlpha2A43, hAlpha2Z13, hAlpha1Range,
      hAlpha2Bool, hZ84, hAlpha0Prime⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp hAlpha1Range with hPrefix | h3
      · rcases mul_eq_zero.mp hPrefix with hPrefix | h2
        · rcases mul_eq_zero.mp hPrefix with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inl (by linear_combination -h1))
        · exact Or.inr (Or.inr (Or.inl (by linear_combination -h2)))
      · exact Or.inr (Or.inr (Or.inr (by linear_combination -h3)))
    · rcases mul_eq_zero.mp hAlpha2Bool with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linear_combination h1)
    · constructor
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hZ84)
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hAlpha0Prime)
    · intro hAlpha2
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAlpha2] at hAlpha21
        simpa using hAlpha21
      · rw [hAlpha2] at hAlpha2Hi
        simpa [sub_eq_add_neg] using hAlpha2Hi
      · have hA43Poly : NoteCommit.boolPoly (input_z43Alpha - input_z44Alpha * 8) = 0 := by
          have hMul :
              input_alpha2 * NoteCommit.boolPoly (input_z43Alpha - input_z44Alpha * 8) = 0 := by
            simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hAlpha2A43
          rw [hAlpha2] at hMul
          simpa using hMul
        exact isBool_of_boolPoly_eq_zero hA43Poly
      · rw [hAlpha2] at hAlpha2Z13
        simpa using hAlpha2Z13
  completeness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, NoteCommit.boolPoly, NoteCommit.tP]
    rcases h_spec with ⟨hAlpha1, hAlpha2, ⟨hZ84, hAlpha0Prime⟩, hCanon⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · exact by
          rw [h1, (hCanon h1).1]
          ring
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1]
        simpa [sub_eq_add_neg] using (hCanon h1).2.1
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · exact by
          have hBoolA43 := boolPoly_eq_zero_of_isBool (hCanon h1).2.2.1
          rw [h1]
          simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBoolA43
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1, (hCanon h1).2.2.2]
        ring
    · rcases hAlpha1 with h0 | h1 | h2 | h3
      · rw [h0]
        ring
      · rw [h1]
        ring
      · rw [h2]
        ring
      · rw [h3]
        ring
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1]
        ring
    · rw [hZ84]
      ring
    · rw [hAlpha0Prime]
      ring

end BaseFieldCanonicity

end FixedBase

namespace FixedShort

structure Row (F : Type) where
  yP : F
  yA : F
  lastWindow : F
  sign : F
deriving ProvableStruct

def signCheck {K : Type} [One K] [Sub K] [Mul K] (row : Row K) : K :=
  row.sign * row.sign - 1

def yCheck {K : Type} [Add K] [Sub K] [Mul K] (row : Row K) : K :=
  (row.yP - row.yA) * (row.yP + row.yA)

def negationCheck {K : Type} [Sub K] [Mul K] (row : Row K) : K :=
  row.sign * row.yP - row.yA

def IsSign (sign : Ecc.PallasBaseField) : Prop :=
  sign = 1 ∨ sign = 0 - 1

def SignedPointSelection (row : Row Ecc.PallasBaseField) : Prop :=
  ∀ x : Ecc.PallasBaseField,
    (row.sign = 1 → (x, row.yP) = (x, row.yA)) ∧
      (row.sign = 0 - 1 →
        (x, row.yP) = CompElliptic.CurveForms.ShortWeierstrass.neg (x, row.yA))

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  IsBool row.lastWindow ∧ IsSign row.sign ∧ SignedPointSelection row

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  assertZero (NoteCommit.boolPoly row.lastWindow)
  assertZero (signCheck row)
  assertZero (yCheck row)
  assertZero (negationCheck row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsSign, SignedPointSelection,
      CompElliptic.CurveForms.ShortWeierstrass.neg, NoteCommit.boolPoly, signCheck, yCheck,
      negationCheck]
    rcases h_holds with ⟨hLastWindow, hSign, _hY, hNegation⟩
    have hSignedY : input_yA = input_sign * input_yP :=
      (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hNegation)).symm
    refine ⟨?_, ?_, ?_⟩
    · exact isBool_of_boolPoly_eq_zero (by
        simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hLastWindow)
    · have hmul : (input_sign - 1) * (input_sign + 1) = 0 := by
        linear_combination hSign
      rcases mul_eq_zero.mp hmul with hPos | hNeg
      · exact Or.inl (sub_eq_zero.mp hPos)
      · exact Or.inr (by linear_combination hNeg)
    · intro x
      constructor
      · intro hPos
        apply Prod.ext
        · rfl
        · rw [hSignedY, hPos]
          simp
      · intro hNeg
        apply Prod.ext
        · rfl
        · rw [hSignedY, hNeg]
          simp
  completeness := by
    circuit_proof_start [main, Spec, IsSign, SignedPointSelection,
      CompElliptic.CurveForms.ShortWeierstrass.neg, NoteCommit.boolPoly, signCheck, yCheck,
      negationCheck]
    rcases h_spec with ⟨hLastWindow, hSign, hPoint⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using
        boolPoly_eq_zero_of_isBool hLastWindow
    · rcases hSign with hSign | hSign <;> rw [hSign] <;> ring
    · rcases hSign with hSign | hSign
      · have hY := congrArg Prod.snd ((hPoint 0).1 hSign)
        simp at hY
        rw [hY]
        ring
      · have hY := congrArg Prod.snd ((hPoint 0).2 hSign)
        simp at hY
        rw [hY]
        ring
    · rcases hSign with hSign | hSign
      · have hY := congrArg Prod.snd ((hPoint 0).1 hSign)
        simp at hY
        rw [hSign, hY]
        ring
      · have hY := congrArg Prod.snd ((hPoint 0).2 hSign)
        simp at hY
        rw [hSign, hY]
        ring

end FixedShort

namespace FixedShort
namespace SignEntry

structure Row (F : Type) where
  x : F
  y : F
  sign : F
  signedY : F
deriving ProvableStruct

def gateRow {K : Type} [Zero K] (row : Row K) : FixedShort.Row K where
  yP := row.signedY
  yA := row.y
  lastWindow := 0
  sign := row.sign

def inputPoint {K : Type} (row : Row K) : K × K :=
  (row.x, row.y)

def outputPoint {K : Type} (row : Row K) : K × K :=
  (row.x, row.signedY)

def Spec (row : Row Ecc.PallasBaseField) : Prop :=
  row.sign = 1 ∧ outputPoint row = inputPoint row ∨
    row.sign = 0 - 1 ∧
      outputPoint row = CompElliptic.CurveForms.ShortWeierstrass.neg (inputPoint row)

def main (row : Var Row Ecc.PallasBaseField) : Circuit Ecc.PallasBaseField Unit := do
  FixedShort.circuit (gateRow row)

def circuit : FormalAssertion Ecc.PallasBaseField Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, gateRow, inputPoint, outputPoint,
      FixedShort.circuit, FixedShort.Spec, FixedShort.IsSign, FixedShort.SignedPointSelection,
      CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_holds with ⟨_, hSign, hPoint⟩
    rcases hSign with hSign | hSign
    · exact Or.inl ⟨hSign, hPoint input_x |>.1 hSign⟩
    · exact Or.inr ⟨hSign, hPoint input_x |>.2 hSign⟩
  completeness := by
    circuit_proof_start [main, Spec, gateRow, inputPoint, outputPoint,
      FixedShort.circuit, FixedShort.Spec, FixedShort.IsSign, FixedShort.SignedPointSelection,
      CompElliptic.CurveForms.ShortWeierstrass.neg]
    refine ⟨?_, ?_, ?_⟩
    · exact Or.inl rfl
    · rcases h_spec with hPos | hNeg
      · exact Or.inl hPos.1
      · exact Or.inr hNeg.1
    · intro x
      constructor
      · intro hSign
        rcases h_spec with hPos | hNeg
        · have hPoint := hPos.2
          have hy := congrArg (fun p : Ecc.PallasBaseField × Ecc.PallasBaseField => p.2) hPoint
          change input_signedY = input_y at hy
          simp [hy]
        · exfalso
          have hEq : (1 : Ecc.PallasBaseField) = 0 - 1 := hSign.symm.trans hNeg.1
          have htwo : (2 : Ecc.PallasBaseField) = 0 := by linear_combination hEq
          exact Ecc.CompleteAdd.pallas_two_ne_zero htwo
      · intro hSign
        rcases h_spec with hPos | hNeg
        · exfalso
          have hEq : (1 : Ecc.PallasBaseField) = 0 - 1 := hPos.1.symm.trans hSign
          have htwo : (2 : Ecc.PallasBaseField) = 0 := by linear_combination hEq
          exact Ecc.CompleteAdd.pallas_two_ne_zero htwo
        · have hPoint := hNeg.2
          have hy := congrArg (fun p : Ecc.PallasBaseField × Ecc.PallasBaseField => p.2) hPoint
          change input_signedY = -input_y at hy
          simp [hy]

end SignEntry
end FixedShort

end ScalarMul
end Orchard
