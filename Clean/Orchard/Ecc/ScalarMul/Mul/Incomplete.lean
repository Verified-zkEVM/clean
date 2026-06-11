import Clean.Orchard.Ecc.ScalarMul.Defs
import Clean.Orchard.Sinsemilla

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/incomplete.rs`.
-/

namespace Orchard.Ecc.ScalarMul.Mul.Incomplete

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

def Spec (row : Row Fp) : Prop :=
  2 * row.yAWitnessed = yADouble row.next

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (poly row)

def circuit : FormalAssertion Fp Row where
  name := "GATE q_mul_1 == 1 checks"
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

def Spec (row : Row Fp) : Prop :=
  IsBool (bit row) ∧
    2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) +
        2 * ((bit row * 2 - 1) * row.yPCur) = yADouble row.cur ∧
    row.cur.lambda2 * row.cur.lambda2 =
        row.xANext + Sinsemilla.DoubleAndAdd.xR row.cur + row.cur.xA ∧
    2 * row.cur.lambda2 * (row.cur.xA - row.xANext) =
        yADouble row.cur + row.yANextDouble

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (gradient1 row)
  assertZero (secantLine row)
  assertZero (gradient2 row)

def circuit : FormalAssertion Fp Row where
  name := "GATE q_mul_3 == 1 checks"
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

def Spec (row : Row Fp) : Prop :=
  row.cur.xP = row.xPNext ∧ row.yPCur = row.yPNext ∧ Loop.Spec row.toRow

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (xPCheck row)
  assertZero (yPCheck row)
  Loop.circuit row.toRow

def circuit : FormalAssertion Fp Row where
  name := "GATE q_mul_2 == 1 checks"
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

end Orchard.Ecc.ScalarMul.Mul.Incomplete
