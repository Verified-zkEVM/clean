import Clean.Circuit
import Clean.Orchard.Ecc
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard Poseidon Pow5 gates and chip entry points

Clean approximations of the Halo2 `Pow5Chip` custom gates used by Orchard's
`P128Pow5T3` nullifier hash.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `full round`
- `partial rounds`
- `pad-and-add`

Orchard configures `Pow5Chip<pallas::Base, 3, 2>` in
`orchard@0.14.0/src/circuit.rs`. These assertions specialize the source polynomials to
width 3 and rate 2.
-/

namespace Orchard
namespace Poseidon

variable {F : Type} [Field F]

def pow5 {K : Type} [Mul K] (x : K) : K :=
  let x2 := x * x
  x2 * x2 * x

private theorem eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : b = a := by
  exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  (eq_of_add_neg_eq_zero h).symm

namespace FullRound

structure Params (F : Type) where
  rcA0 : F
  rcA1 : F
  rcA2 : F
  m00 : F
  m01 : F
  m02 : F
  m10 : F
  m11 : F
  m12 : F
  m20 : F
  m21 : F
  m22 : F

structure Row (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  next0 : F
  next1 : F
  next2 : F
deriving ProvableStruct

def Params.toExpr (params : Params Ecc.Fp) :
    Params (Expression Ecc.Fp) where
  rcA0 := params.rcA0
  rcA1 := params.rcA1
  rcA2 := params.rcA2
  m00 := params.m00
  m01 := params.m01
  m02 := params.m02
  m10 := params.m10
  m11 := params.m11
  m12 := params.m12
  m20 := params.m20
  m21 := params.m21
  m22 := params.m22

def s0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur0 + params.rcA0)

def s1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur1 + params.rcA1)

def s2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur2 + params.rcA2)

def output0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  s0 params row * params.m00 + s1 params row * params.m01 + s2 params row * params.m02

def output1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  s0 params row * params.m10 + s1 params row * params.m11 + s2 params row * params.m12

def output2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  s0 params row * params.m20 + s1 params row * params.m21 + s2 params row * params.m22

def next0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  output0 params row - row.next0

def next1Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  output1 params row - row.next1

def next2Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  output2 params row - row.next2

def Spec (params : Params Ecc.Fp) (row : Row Ecc.Fp) : Prop :=
  row.next0 = output0 params row ∧
    row.next1 = output1 params row ∧
    row.next2 = output2 params row

def main (params : Params Ecc.Fp)
    (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (next0Check paramsExpr row)
  assertZero (next1Check paramsExpr row)
  assertZero (next2Check paramsExpr row)

def circuit (params : Params Ecc.Fp) : FormalAssertion Ecc.Fp Row where
  name := "GATE full round"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, next0Check, next1Check, next2Check,
      output0, output1, output2, s0, s1, s2, pow5, Params.toExpr]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact eq_of_add_neg_eq_zero h0
    constructor
    · exact eq_of_add_neg_eq_zero h1
    · exact eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, next0Check, next1Check, next2Check,
      output0, output1, output2, s0, s1, s2, pow5, Params.toExpr]
    simp_all
    ring_nf
    simp

end FullRound

namespace PartialRounds

structure Params (F : Type) where
  rcA0 : F
  rcA1 : F
  rcA2 : F
  rcB0 : F
  rcB1 : F
  rcB2 : F
  m00 : F
  m01 : F
  m02 : F
  m10 : F
  m11 : F
  m12 : F
  m20 : F
  m21 : F
  m22 : F
  mInv00 : F
  mInv01 : F
  mInv02 : F
  mInv10 : F
  mInv11 : F
  mInv12 : F
  mInv20 : F
  mInv21 : F
  mInv22 : F

structure Row (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  mid0Sbox : F
  next0 : F
  next1 : F
  next2 : F
deriving ProvableStruct

def Params.toExpr (params : Params Ecc.Fp) :
    Params (Expression Ecc.Fp) where
  rcA0 := params.rcA0
  rcA1 := params.rcA1
  rcA2 := params.rcA2
  rcB0 := params.rcB0
  rcB1 := params.rcB1
  rcB2 := params.rcB2
  m00 := params.m00
  m01 := params.m01
  m02 := params.m02
  m10 := params.m10
  m11 := params.m11
  m12 := params.m12
  m20 := params.m20
  m21 := params.m21
  m22 := params.m22
  mInv00 := params.mInv00
  mInv01 := params.mInv01
  mInv02 := params.mInv02
  mInv10 := params.mInv10
  mInv11 := params.mInv11
  mInv12 := params.mInv12
  mInv20 := params.mInv20
  mInv21 := params.mInv21
  mInv22 := params.mInv22

def mid0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (row.cur0 + params.rcA0) - row.mid0Sbox

def mid0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.mid0Sbox * params.m00 + (row.cur1 + params.rcA1) * params.m01 +
    (row.cur2 + params.rcA2) * params.m02

def mid1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.mid0Sbox * params.m10 + (row.cur1 + params.rcA1) * params.m11 +
    (row.cur2 + params.rcA2) * params.m12

def mid2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.mid0Sbox * params.m20 + (row.cur1 + params.rcA1) * params.m21 +
    (row.cur2 + params.rcA2) * params.m22

def nextInv0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.next0 * params.mInv00 + row.next1 * params.mInv01 + row.next2 * params.mInv02

def nextInv1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.next0 * params.mInv10 + row.next1 * params.mInv11 + row.next2 * params.mInv12

def nextInv2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Row K) : K :=
  row.next0 * params.mInv20 + row.next1 * params.mInv21 + row.next2 * params.mInv22

def next0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  pow5 (mid0 params row + params.rcB0) - nextInv0 params row

def next1Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  mid1 params row + params.rcB1 - nextInv1 params row

def next2Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Row K) : K :=
  mid2 params row + params.rcB2 - nextInv2 params row

def Spec (params : Params Ecc.Fp) (row : Row Ecc.Fp) : Prop :=
  row.mid0Sbox = pow5 (row.cur0 + params.rcA0) ∧
    nextInv0 params row = pow5 (mid0 params row + params.rcB0) ∧
    nextInv1 params row = mid1 params row + params.rcB1 ∧
    nextInv2 params row = mid2 params row + params.rcB2

def main (params : Params Ecc.Fp)
    (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (mid0Check paramsExpr row)
  assertZero (next0Check paramsExpr row)
  assertZero (next1Check paramsExpr row)
  assertZero (next2Check paramsExpr row)

def circuit (params : Params Ecc.Fp) : FormalAssertion Ecc.Fp Row where
  name := "GATE partial rounds"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, mid0Check, next0Check, next1Check,
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5,
      Params.toExpr]
    rcases h_holds with ⟨hmid, h0, h1, h2⟩
    constructor
    · exact eq_of_add_neg_eq_zero hmid
    constructor
    · exact eq_of_add_neg_eq_zero h0
    constructor
    · exact eq_of_add_neg_eq_zero h1
    · exact eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, mid0Check, next0Check, next1Check,
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5,
      Params.toExpr]
    simp_all
    ring_nf
    simp

end PartialRounds

namespace PadAndAdd

structure Row (F : Type) where
  initial0 : F
  initial1 : F
  initial2 : F
  input0 : F
  input1 : F
  output0 : F
  output1 : F
  output2 : F
deriving ProvableStruct

def output0Check {K : Type} [Add K] [Sub K] (row : Row K) : K :=
  row.initial0 + row.input0 - row.output0

def output1Check {K : Type} [Add K] [Sub K] (row : Row K) : K :=
  row.initial1 + row.input1 - row.output1

def capacityCheck {K : Type} [Sub K] (row : Row K) : K :=
  row.initial2 - row.output2

def Spec (row : Row Ecc.Fp) : Prop :=
  row.output0 = row.initial0 + row.input0 ∧
    row.output1 = row.initial1 + row.input1 ∧
    row.output2 = row.initial2

def main (row : Var Row Ecc.Fp) : Circuit Ecc.Fp Unit := do
  assertZero (output0Check row)
  assertZero (output1Check row)
  assertZero (capacityCheck row)

def circuit : FormalAssertion Ecc.Fp Row where
  name := "GATE pad-and-add"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, output0Check, output1Check, capacityCheck]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · have h0' : input_initial0 + input_input0 - input_output0 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h0').symm
    constructor
    · have h1' : input_initial1 + input_input1 - input_output1 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h1').symm
    · have h2' : input_initial2 - input_output2 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h2').symm
  completeness := by
    circuit_proof_start [main, Spec, output0Check, output1Check, capacityCheck]
    simp_all
    constructor <;> ring

end PadAndAdd

end Poseidon
end Orchard
