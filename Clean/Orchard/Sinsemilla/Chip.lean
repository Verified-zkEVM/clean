import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Orchard.Ecc.DoubleAndAdd
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Sinsemilla chip custom gates

Clean ports of the `SinsemillaChip` custom arithmetic gates.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip.rs`
- `Initial y_Q`
- `Sinsemilla gate`

These model the enabled custom-gate polynomials, not the selector/fixed-column/lookup/
row-layout machinery. The synthesis-level circuits that enable them live in
`Sinsemilla/HashToPoint.lean`.
-/

namespace Orchard.Sinsemilla.Chip

open Orchard.Ecc

/-! ### Initial `y_Q` gate -/
namespace InitialYQ

structure Params (F : Type) where
  yQ : F

structure Row (F : Type) where
  doubleAndAdd : DoubleAndAddRow F
deriving ProvableStruct

def Params.toExpr (params : Params Fp) :
    Params (Expression Fp) where
  yQ := params.yQ

def Spec (params : Params Fp) (row : Row Fp) : Prop :=
  DoubleAndAdd.yA row.doubleAndAdd = 2 * params.yQ

def main (params : Params Fp)
    (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (2 * params.toExpr.yQ - DoubleAndAdd.yA row.doubleAndAdd)

def circuit (params : Params Fp) : FormalAssertion Fp Row where
  name := "GATE Initial y_Q"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h_holds)).symm
  completeness := by
    circuit_proof_start [Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end InitialYQ

/-! ### The Sinsemilla gate -/
namespace Gate

structure Params (F : Type) where
  qS2 : F

structure Row (F : Type) where
  cur : DoubleAndAddRow F
  next : DoubleAndAddRow F
deriving ProvableStruct

def Params.toExpr (params : Params Fp) :
    Params (Expression Fp) where
  qS2 := params.qS2

def qS3 {K : Type} [One K] [Sub K] [Mul K] (params : Params K) : K :=
  params.qS2 * (params.qS2 - 1)

def yLhs {K : Type} [Sub K] [Mul K] [OfNat K 4] (row : Row K) : K :=
  4 * row.cur.lambda2 * (row.cur.xA - row.next.xA)

def yRhs {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (params : Params K) (row : Row K) : K :=
  2 * DoubleAndAdd.yA row.cur +
    (2 - qS3 params) * DoubleAndAdd.yA row.next +
    qS3 params * 2 * row.next.lambda1

def Spec (params : Params Fp) (row : Row Fp) : Prop :=
  row.cur.lambda2 * row.cur.lambda2 =
    row.next.xA + DoubleAndAdd.xR row.cur + row.cur.xA ∧
  yLhs row = yRhs params row

def main (params : Params Fp)
    (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.cur.lambda2 * row.cur.lambda2 -
    (row.next.xA + DoubleAndAdd.xR row.cur + row.cur.xA))
  assertZero (yLhs row - yRhs params.toExpr row)

def circuit (params : Params Fp) : FormalAssertion Fp Row where
  name := "GATE Sinsemilla gate"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [yLhs, yRhs, qS3, Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    rcases h_holds with ⟨hSec, hY⟩
    exact ⟨sub_eq_zero.mp hSec, sub_eq_zero.mp hY⟩
  completeness := by
    circuit_proof_start [yLhs, yRhs, qS3, Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all

end Gate

end Orchard.Sinsemilla.Chip
