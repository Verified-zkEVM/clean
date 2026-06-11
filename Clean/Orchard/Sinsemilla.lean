import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard Sinsemilla gates

Clean ports of Sinsemilla custom arithmetic gates.

References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `DoubleAndAdd::x_r`
- `DoubleAndAdd::Y_A`

`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/chip.rs`
- `Initial y_Q`
- `Sinsemilla gate`

These gadgets model the arithmetic constraints, not the Halo2 selector, fixed-column,
lookup, or row-layout machinery.
-/

namespace Orchard
namespace Sinsemilla

variable {F : Type} [Field F]

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

structure DoubleAndAddRow (F : Type) where
  xA : F
  xP : F
  lambda1 : F
  lambda2 : F
deriving ProvableStruct

namespace DoubleAndAdd

def xR {K : Type} [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  row.lambda1 * row.lambda1 - row.xA - row.xP

def yA {K : Type} [Add K] [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  (row.lambda1 + row.lambda2) * (row.xA - xR row)

end DoubleAndAdd

namespace InitialYQ

structure Params (F : Type) where
  yQ : F

structure Row (F : Type) where
  doubleAndAdd : DoubleAndAddRow F
deriving ProvableStruct

def Params.toExpr (params : Params Ecc.Fp) :
    Params (Expression Ecc.Fp) where
  yQ := params.yQ

def poly {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 2]
    (params : Params K) (row : Row K) : K :=
  2 * params.yQ - DoubleAndAdd.yA row.doubleAndAdd

def Spec (params : Params Ecc.Fp) (row : Row Ecc.Fp) : Prop :=
  DoubleAndAdd.yA row.doubleAndAdd = 2 * params.yQ

def main (params : Params Ecc.Fp)
    (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (poly params.toExpr row)

def circuit (params : Params Ecc.Fp) : FormalAssertion Ecc.Fp Row where
  name := "GATE Initial y_Q"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, poly, Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h_holds)).symm
  completeness := by
    circuit_proof_start [main, Spec, poly, Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]

end InitialYQ

/-!
TODO(source-conformance): `hash_to_point` initial-`Q` wiring is not implemented.

Initialization should be built inside the full `hash_to_point` entry circuit, with
`InitialYQ.circuit` used only for the actual initial-y custom gate.
-/

namespace Gate

structure Params (F : Type) where
  qS2 : F

structure Row (F : Type) where
  cur : DoubleAndAddRow F
  next : DoubleAndAddRow F
deriving ProvableStruct

def Params.toExpr (params : Params Ecc.Fp) :
    Params (Expression Ecc.Fp) where
  qS2 := params.qS2

def qS3 {K : Type} [One K] [Sub K] [Mul K] (params : Params K) : K :=
  params.qS2 * (params.qS2 - 1)

def secantLine {K : Type} [Add K] [Sub K] [Mul K] (row : Row K) : K :=
  row.cur.lambda2 * row.cur.lambda2 -
    (row.next.xA + DoubleAndAdd.xR row.cur + row.cur.xA)

def yLhs {K : Type} [Sub K] [Mul K] [OfNat K 4] (row : Row K) : K :=
  4 * row.cur.lambda2 * (row.cur.xA - row.next.xA)

def yRhs {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (params : Params K) (row : Row K) : K :=
  2 * DoubleAndAdd.yA row.cur +
    (2 - qS3 params) * DoubleAndAdd.yA row.next +
    qS3 params * 2 * row.next.lambda1

def yCheck {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2] [OfNat K 4]
    (params : Params K) (row : Row K) : K :=
  yLhs row - yRhs params row

def Spec (params : Params Ecc.Fp) (row : Row Ecc.Fp) : Prop :=
  row.cur.lambda2 * row.cur.lambda2 =
    row.next.xA + DoubleAndAdd.xR row.cur + row.cur.xA ∧
  yLhs row = yRhs params row

def main (params : Params Ecc.Fp)
    (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (secantLine row)
  assertZero (yCheck params.toExpr row)

def circuit (params : Params Ecc.Fp) : FormalAssertion Ecc.Fp Row where
  name := "GATE Sinsemilla gate"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, secantLine, yCheck, yLhs, yRhs, qS3,
      Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    constructor
    · have hSec :
          input_cur_lambda2 * input_cur_lambda2 -
              (input_next_xA +
                (input_cur_lambda1 * input_cur_lambda1 - input_cur_xA - input_cur_xP) +
                input_cur_xA) = 0 := by
        simp_all [sub_eq_add_neg]
      exact sub_eq_zero.mp hSec
    · have hY :
          4 * input_cur_lambda2 * (input_cur_xA - input_next_xA) -
              (2 *
                  ((input_cur_lambda1 + input_cur_lambda2) *
                    (input_cur_xA -
                      (input_cur_lambda1 * input_cur_lambda1 - input_cur_xA - input_cur_xP))) +
                (2 - params.qS2 * (params.qS2 - 1)) *
                  ((input_next_lambda1 + input_next_lambda2) *
                    (input_next_xA -
                      (input_next_lambda1 * input_next_lambda1 - input_next_xA - input_next_xP))) +
                params.qS2 * (params.qS2 - 1) * 2 * input_next_lambda1) = 0 := by
        simp_all [sub_eq_add_neg]
      exact sub_eq_zero.mp hY
  completeness := by
    circuit_proof_start [main, Spec, secantLine, yCheck, yLhs, yRhs, qS3,
      Params.toExpr, DoubleAndAdd.yA, DoubleAndAdd.xR]
    simp_all [sub_eq_add_neg]
    constructor <;> ring

end Gate

/-!
TODO(source-conformance): `CommitDomain::commit` and `CommitDomain::short_commit` are
not implemented.

These should be built only after source-conformant `hash_to_point` and fixed-base
scalar-multiplication entry circuits exist.
-/

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `Decomposition check`
- `MerkleInstructions::hash_layer`

This ports the MerkleCRH decomposition gate that connects the three Sinsemilla message
pieces `a`, `b`, `c` to `(l, left, right)`.
-/

namespace Merkle

structure DecompositionRow (F : Type) where
  aWhole : F
  bWhole : F
  cWhole : F
  leftNode : F
  rightNode : F
  z1A : F
  z1B : F
  b1 : F
  b2 : F
  lWhole : F
deriving ProvableStruct

def twoPow5 {K : Type} [OfNat K (2 ^ 5)] : K := OfNat.ofNat (2 ^ 5)

def twoPow10 {K : Type} [OfNat K (2 ^ 10)] : K := OfNat.ofNat (2 ^ 10)

def twoPow240 {K : Type} [OfNat K (2 ^ 240)] : K := OfNat.ofNat (2 ^ 240)

def a0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 10)] (row : DecompositionRow K) : K :=
  row.aWhole - row.z1A * twoPow10

def b1B2Check {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 5)]
    (row : DecompositionRow K) : K :=
  row.z1B - (row.b1 + row.b2 * twoPow5)

def b0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 10)] (row : DecompositionRow K) : K :=
  row.bWhole - row.z1B * twoPow10

def leftCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 10)]
    [OfNat K (2 ^ 240)] (row : DecompositionRow K) : K :=
  let reconstructed := row.z1A + (b0 row + row.b1 * twoPow10) * twoPow240
  reconstructed - row.leftNode

def rightCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 5)]
    (row : DecompositionRow K) : K :=
  row.b2 + row.cWhole * twoPow5 - row.rightNode

def Spec (row : DecompositionRow Ecc.Fp) : Prop :=
  row.lWhole = a0 row ∧
  row.leftNode = row.z1A + (b0 row + row.b1 * twoPow10) * twoPow240 ∧
  row.rightNode = row.b2 + row.cWhole * twoPow5 ∧
  row.z1B = row.b1 + row.b2 * twoPow5

def main (row : Var DecompositionRow Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (a0 row - row.lWhole)
  assertZero (leftCheck row)
  assertZero (rightCheck row)
  assertZero (b1B2Check row)

def circuit : FormalAssertion Ecc.Fp DecompositionRow where
  name := "GATE Decomposition check"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    rcases h_holds with ⟨hl, hleft, hright, hb⟩
    constructor
    · rw [sub_eq_add_neg]
      exact (left_eq_of_add_neg_eq_zero hl).symm
    constructor
    · rw [sub_eq_add_neg]
      exact (left_eq_of_add_neg_eq_zero hleft).symm
    constructor
    · exact (left_eq_of_add_neg_eq_zero hright).symm
    · exact left_eq_of_add_neg_eq_zero hb
  completeness := by
    circuit_proof_start [main, Spec, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    rcases h_spec with ⟨hl, hleft, hright, hb⟩
    constructor
    · rw [hl]
      ring
    constructor
    · rw [hleft]
      ring
    constructor
    · rw [hright]
      ring
    · rw [hb]
      ring

/-!
TODO(source-conformance): `MerkleInstructions::hash_layer` and
`MerklePath::calculate_root` are not implemented.

These should be built as source-conformant entry circuits after `hash_to_point` exists.
-/

end Merkle

end Sinsemilla
end Orchard
