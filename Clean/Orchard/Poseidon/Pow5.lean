import Clean.Circuit
import Clean.Orchard.Poseidon.Pow5.Constants

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

def pow5 {K : Type} [Mul K] (x : K) : K :=
  let x2 := x * x
  x2 * x2 * x

private theorem eq_of_add_neg_eq_zero {a b : Fp} (h : a + -b = 0) : b = a := by
  exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm

private theorem left_eq_of_add_neg_eq_zero {a b : Fp} (h : a + -b = 0) : a = b :=
  (eq_of_add_neg_eq_zero h).symm

namespace FullRound
namespace Gate

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

structure Input (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  next0 : F
  next1 : F
  next2 : F
deriving ProvableStruct

def Params.toExpr (params : Params Fp) :
    Params (Expression Fp) where
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

def s0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  pow5 (row.cur0 + params.rcA0)

def s1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  pow5 (row.cur1 + params.rcA1)

def s2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  pow5 (row.cur2 + params.rcA2)

def output0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  s0 params row * params.m00 + s1 params row * params.m01 + s2 params row * params.m02

def output1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  s0 params row * params.m10 + s1 params row * params.m11 + s2 params row * params.m12

def output2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  s0 params row * params.m20 + s1 params row * params.m21 + s2 params row * params.m22

def next0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Input K) : K :=
  output0 params row - row.next0

def next1Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Input K) : K :=
  output1 params row - row.next1

def next2Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Input K) : K :=
  output2 params row - row.next2

def Spec (params : Params Fp) (row : Input Fp) : Prop :=
  row.next0 = output0 params row ∧
    row.next1 = output1 params row ∧
    row.next2 = output2 params row

def main (params : Params Fp)
    (row : Var Input Fp) : Circuit Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (next0Check paramsExpr row)
  assertZero (next1Check paramsExpr row)
  assertZero (next2Check paramsExpr row)

def circuit (params : Params Fp) : FormalAssertion Fp Input where
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

end Gate
end FullRound

namespace PartialRounds
namespace Gate

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

structure Input (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  mid0Sbox : F
  next0 : F
  next1 : F
  next2 : F
deriving ProvableStruct

def Params.toExpr (params : Params Fp) :
    Params (Expression Fp) where
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

def mid0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Input K) : K :=
  pow5 (row.cur0 + params.rcA0) - row.mid0Sbox

def mid0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  row.mid0Sbox * params.m00 + (row.cur1 + params.rcA1) * params.m01 +
    (row.cur2 + params.rcA2) * params.m02

def mid1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  row.mid0Sbox * params.m10 + (row.cur1 + params.rcA1) * params.m11 +
    (row.cur2 + params.rcA2) * params.m12

def mid2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  row.mid0Sbox * params.m20 + (row.cur1 + params.rcA1) * params.m21 +
    (row.cur2 + params.rcA2) * params.m22

def nextInv0 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  row.next0 * params.mInv00 + row.next1 * params.mInv01 + row.next2 * params.mInv02

def nextInv1 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  row.next0 * params.mInv10 + row.next1 * params.mInv11 + row.next2 * params.mInv12

def nextInv2 {K : Type} [Add K] [Mul K] (params : Params K) (row : Input K) : K :=
  row.next0 * params.mInv20 + row.next1 * params.mInv21 + row.next2 * params.mInv22

def next0Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Input K) : K :=
  pow5 (mid0 params row + params.rcB0) - nextInv0 params row

def next1Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Input K) : K :=
  mid1 params row + params.rcB1 - nextInv1 params row

def next2Check {K : Type} [Add K] [Sub K] [Mul K] (params : Params K) (row : Input K) : K :=
  mid2 params row + params.rcB2 - nextInv2 params row

def Spec (params : Params Fp) (row : Input Fp) : Prop :=
  row.mid0Sbox = pow5 (row.cur0 + params.rcA0) ∧
    nextInv0 params row = pow5 (mid0 params row + params.rcB0) ∧
    nextInv1 params row = mid1 params row + params.rcB1 ∧
    nextInv2 params row = mid2 params row + params.rcB2

def main (params : Params Fp)
    (row : Var Input Fp) : Circuit Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (mid0Check paramsExpr row)
  assertZero (next0Check paramsExpr row)
  assertZero (next1Check paramsExpr row)
  assertZero (next2Check paramsExpr row)

def circuit (params : Params Fp) : FormalAssertion Fp Input where
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

end Gate
end PartialRounds

namespace PadAndAdd

structure Input (F : Type) where
  initial0 : F
  initial1 : F
  initial2 : F
  input0 : F
  input1 : F
  output0 : F
  output1 : F
  output2 : F
deriving ProvableStruct

def output0Check {K : Type} [Add K] [Sub K] (row : Input K) : K :=
  row.initial0 + row.input0 - row.output0

def output1Check {K : Type} [Add K] [Sub K] (row : Input K) : K :=
  row.initial1 + row.input1 - row.output1

def capacityCheck {K : Type} [Sub K] (row : Input K) : K :=
  row.initial2 - row.output2

def Spec (row : Input Fp) : Prop :=
  row.output0 = row.initial0 + row.input0 ∧
    row.output1 = row.initial1 + row.input1 ∧
    row.output2 = row.initial2

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertZero (output0Check row)
  assertZero (output1Check row)
  assertZero (capacityCheck row)

def circuit : FormalAssertion Fp Input where
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

namespace Permute

/-!
Source reference: `poseidon/pow5.rs::Pow5Chip::permute` and
`Pow5State::{load,full_round,partial_round,round}`.

For Orchard's `P128Pow5T3`, `WIDTH = 3`, `RATE = 2`, `R_F = 8`, and `R_P = 56`.
Halo2 lays out one full round per row and two partial rounds per row:

- copy/load the incoming state at row 0;
- 4 first-half full-round rows;
- 28 partial-round rows, each representing rounds `r` and `r+1`;
- 4 second-half full-round rows.

The circuit below mirrors that schedule while keeping the actual constants as Lean
parameters.  This is intentionally the `Pow5Chip::permute` surface: callers supply only
an initial state and receive the final state; intermediate rows are witnessed inside the
circuit.
-/

/-- Constants needed by one width-3 full round. -/
def fullParams (roundConstants : Nat → State Fp) (mds : Nat → Nat → Fp)
    (round : Nat) : FullRound.Gate.Params Fp where
  rcA0 := (roundConstants round).x0
  rcA1 := (roundConstants round).x1
  rcA2 := (roundConstants round).x2
  m00 := mds 0 0
  m01 := mds 0 1
  m02 := mds 0 2
  m10 := mds 1 0
  m11 := mds 1 1
  m12 := mds 1 2
  m20 := mds 2 0
  m21 := mds 2 1
  m22 := mds 2 2

/-- Constants needed by one width-3 partial-round row, which checks two source rounds. -/
def partialParams (roundConstants : Nat → State Fp) (mds mdsInv : Nat → Nat → Fp)
    (round : Nat) : PartialRounds.Gate.Params Fp where
  rcA0 := (roundConstants round).x0
  rcA1 := (roundConstants round).x1
  rcA2 := (roundConstants round).x2
  rcB0 := (roundConstants (round + 1)).x0
  rcB1 := (roundConstants (round + 1)).x1
  rcB2 := (roundConstants (round + 1)).x2
  m00 := mds 0 0
  m01 := mds 0 1
  m02 := mds 0 2
  m10 := mds 1 0
  m11 := mds 1 1
  m12 := mds 1 2
  m20 := mds 2 0
  m21 := mds 2 1
  m22 := mds 2 2
  mInv00 := mdsInv 0 0
  mInv01 := mdsInv 0 1
  mInv02 := mdsInv 0 2
  mInv10 := mdsInv 1 0
  mInv11 := mdsInv 1 1
  mInv12 := mdsInv 1 2
  mInv20 := mdsInv 2 0
  mInv21 := mdsInv 2 1
  mInv22 := mdsInv 2 2

/-- P128Pow5T3 partial-round-row parameters for a source round index. -/
def partialParamsP128 (roundConstants : Nat → State Fp) (round : Nat) :
    PartialRounds.Gate.Params Fp :=
  partialParams roundConstants P128Pow5T3.mds P128Pow5T3.mdsInv round

/-- Value-level full-round transition, matching `Pow5State::full_round`. -/
def fullRoundValue (params : FullRound.Gate.Params Fp) (state : State Fp) : State Fp :=
  let row : FullRound.Gate.Input Fp :=
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      next0 := 0, next1 := 0, next2 := 0 }
  { x0 := FullRound.Gate.output0 params row
    x1 := FullRound.Gate.output1 params row
    x2 := FullRound.Gate.output2 params row }

/-- The first-round S-box value witnessed in a partial-round row. -/
def partialMid0SboxValue (params : PartialRounds.Gate.Params Fp) (state : State Fp) : Fp :=
  pow5 (state.x0 + params.rcA0)

/-- Value-level partial-round-row transition, matching `Pow5State::partial_round`. -/
def partialRoundValue (params : PartialRounds.Gate.Params Fp) (state : State Fp) : State Fp :=
  let rowWithMid : PartialRounds.Gate.Input Fp :=
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      mid0Sbox := partialMid0SboxValue params state,
      next0 := 0, next1 := 0, next2 := 0 }
  let r0 := pow5 (PartialRounds.Gate.mid0 params rowWithMid + params.rcB0)
  let r1 := PartialRounds.Gate.mid1 params rowWithMid + params.rcB1
  let r2 := PartialRounds.Gate.mid2 params rowWithMid + params.rcB2
  { x0 := r0 * params.m00 + r1 * params.m01 + r2 * params.m02
    x1 := r0 * params.m10 + r1 * params.m11 + r2 * params.m12
    x2 := r0 * params.m20 + r1 * params.m21 + r2 * params.m22 }

/-- The concrete row witnessed by the honest P128 partial-round prover. -/
def partialRowValueP128 (roundConstants : Nat → State Fp) (round : Nat)
    (state : State Fp) : PartialRounds.Gate.Input Fp :=
  let params := partialParamsP128 roundConstants round
  let next := partialRoundValue params state
  { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
    mid0Sbox := partialMid0SboxValue params state,
    next0 := next.x0, next1 := next.x1, next2 := next.x2 }

/-- The honest P128 partial-round row satisfies the Halo2 gate relation. -/
theorem partialRowValueP128_spec (roundConstants : Nat → State Fp) (round : Nat)
    (state : State Fp) :
    PartialRounds.Gate.Spec (partialParamsP128 roundConstants round)
      (partialRowValueP128 roundConstants round state) := by
  constructor
  · rfl
  constructor
  · simp [partialRowValueP128, partialRoundValue, partialMid0SboxValue,
      partialParamsP128, partialParams, PartialRounds.Gate.nextInv0, PartialRounds.Gate.mid0,
      PartialRounds.Gate.mid1, PartialRounds.Gate.mid2]
    exact P128Pow5T3.mdsInv_mul_mds_apply ⟨0, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)
  constructor
  · simp [partialRowValueP128, partialRoundValue, partialMid0SboxValue,
      partialParamsP128, partialParams, PartialRounds.Gate.nextInv1, PartialRounds.Gate.mid0,
      PartialRounds.Gate.mid1, PartialRounds.Gate.mid2]
    exact P128Pow5T3.mdsInv_mul_mds_apply ⟨1, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)
  · simp [partialRowValueP128, partialRoundValue, partialMid0SboxValue,
      partialParamsP128, partialParams, PartialRounds.Gate.nextInv2, PartialRounds.Gate.mid0,
      PartialRounds.Gate.mid1, PartialRounds.Gate.mid2]
    exact P128Pow5T3.mdsInv_mul_mds_apply ⟨2, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)

/-! ### Plain Lean permutation specification -/

/-- Apply the four consecutive value-level full rounds used by `Pow5Chip::permute`,
starting at source round `round`. -/
def fullRounds4Value (roundConstants : Nat → State Fp) (mds : Nat → Nat → Fp)
    (round : Nat) (state : State Fp) : State Fp :=
  Fin.foldl 4
    (fun state i => fullRoundValue (fullParams roundConstants mds (round + i.val)) state)
    state

/-- Apply the 28 consecutive P128Pow5T3 value-level partial-round rows used by
`Pow5Chip::permute`, starting at source round 4. -/
def partialRoundRows28P128Value (roundConstants : Nat → State Fp)
    (state : State Fp) : State Fp :=
  Fin.foldl 28
    (fun state i =>
      partialRoundValue (partialParamsP128 roundConstants (4 + 2 * i.val)) state)
    state

/-- Plain Lean implementation of Orchard's `P128Pow5T3` `Pow5Chip::permute` schedule. -/
def permuteP128Value (roundConstants : Nat → State Fp) (input : State Fp) :
    State Fp :=
  let s := fullRounds4Value roundConstants P128Pow5T3.mds 0 input
  let s := partialRoundRows28P128Value roundConstants s
  fullRounds4Value roundConstants P128Pow5T3.mds (4 + 56) s

/-- Parameterized compatibility wrapper for the old skeleton API, now also using the
fixed 28-row fold shape. -/
def permuteValue (roundConstants : Nat → State Fp) (mds mdsInv : Nat → Nat → Fp)
    (input : State Fp) : State Fp :=
  let s := fullRounds4Value roundConstants mds 0 input
  let s := Fin.foldl 28
    (fun state i => partialRoundValue (partialParams roundConstants mds mdsInv (4 + 2 * i.val)) state)
    s
  fullRounds4Value roundConstants mds (4 + 56) s

/-- Source-level permutation spec: the circuit output is the plain Lean permutation. -/
def Spec (roundConstants : Nat → State Fp) (mds mdsInv : Nat → Nat → Fp)
    (input output : State Fp) : Prop :=
  output = permuteValue roundConstants mds mdsInv input

/-! ### Circuit implementation -/

namespace FullRound

/-- One source-shaped full-round row: witness the next state internally and assert the
`full round` gate. -/
def main (params : Orchard.Poseidon.FullRound.Gate.Params Fp) (state : Var State Fp) :
    Circuit Fp (Var State Fp) := do
  let next ← witness fun env => fullRoundValue params (eval env state)
  Orchard.Poseidon.FullRound.Gate.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- Packaged full-round loop body. -/
def circuit (params : Orchard.Poseidon.FullRound.Gate.Params Fp) : FormalCircuit Fp State State where
  name := "Pow5State::full_round"
  main := main params
  Spec input output := output = fullRoundValue params input
  soundness := by
    circuit_proof_start [main, fullRoundValue, Orchard.Poseidon.FullRound.Gate.circuit, Orchard.Poseidon.FullRound.Gate.Spec,
      Orchard.Poseidon.FullRound.Gate.output0, Orchard.Poseidon.FullRound.Gate.output1, Orchard.Poseidon.FullRound.Gate.output2]
    rcases h_holds with ⟨h0, h1, h2⟩
    simp [State.mk.injEq, Orchard.Poseidon.FullRound.Gate.s0, Orchard.Poseidon.FullRound.Gate.s1, Orchard.Poseidon.FullRound.Gate.s2] at h0 h1 h2 ⊢
    exact ⟨h0, h1, h2⟩
  completeness := by
    circuit_proof_start [main, fullRoundValue, Orchard.Poseidon.FullRound.Gate.circuit, Orchard.Poseidon.FullRound.Gate.Spec,
      Orchard.Poseidon.FullRound.Gate.output0, Orchard.Poseidon.FullRound.Gate.output1, Orchard.Poseidon.FullRound.Gate.output2]
    constructor
    · simpa [Orchard.Poseidon.FullRound.Gate.s0, Orchard.Poseidon.FullRound.Gate.s1, Orchard.Poseidon.FullRound.Gate.s2] using h_env ⟨0, by norm_num⟩
    constructor
    · simpa [Orchard.Poseidon.FullRound.Gate.s0, Orchard.Poseidon.FullRound.Gate.s1, Orchard.Poseidon.FullRound.Gate.s2] using h_env ⟨1, by norm_num⟩
    · simpa [Orchard.Poseidon.FullRound.Gate.s0, Orchard.Poseidon.FullRound.Gate.s1, Orchard.Poseidon.FullRound.Gate.s2] using h_env ⟨2, by norm_num⟩

end FullRound

namespace PartialRounds

/-- One source-shaped partial-round row: witness the intermediate S-box and next state
internally and assert the `partial rounds` gate. -/
def main (params : Orchard.Poseidon.PartialRounds.Gate.Params Fp) (state : Var State Fp) :
    Circuit Fp (Var State Fp) := do
  let mid0Sbox ← witness fun env => partialMid0SboxValue params (eval env state)
  let next ← witness fun env => partialRoundValue params (eval env state)
  Orchard.Poseidon.PartialRounds.Gate.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      mid0Sbox,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- One P128Pow5T3 source-shaped partial-round row. -/
def mainP128 (roundConstants : Nat → State Fp) (round : Nat)
    (state : Var State Fp) : Circuit Fp (Var State Fp) :=
  PartialRounds.main (partialParamsP128 roundConstants round) state

/-- Packaged P128Pow5T3 partial-round-row loop body. -/
def circuitP128 (roundConstants : Nat → State Fp) (round : Nat) :
    FormalCircuit Fp State State where
  name := "Pow5State::partial_round[P128]"
  main := mainP128 roundConstants round
  Spec input output := output = partialRoundValue (partialParamsP128 roundConstants round) input
  soundness := by
    circuit_proof_start [mainP128, PartialRounds.main, partialRoundValue, partialMid0SboxValue,
      Orchard.Poseidon.PartialRounds.Gate.circuit, Orchard.Poseidon.PartialRounds.Gate.Spec, partialParamsP128, partialParams,
      Orchard.Poseidon.PartialRounds.Gate.mid0, Orchard.Poseidon.PartialRounds.Gate.mid1, Orchard.Poseidon.PartialRounds.Gate.mid2,
      Orchard.Poseidon.PartialRounds.Gate.nextInv0, Orchard.Poseidon.PartialRounds.Gate.nextInv1, Orchard.Poseidon.PartialRounds.Gate.nextInv2]
    rcases h_holds with ⟨hmid, h0, h1, h2⟩
    simp [State.mk.injEq] at hmid h0 h1 h2 ⊢
    constructor
    · have happ := P128Pow5T3.mds_mul_mdsInv_apply ⟨0, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
    constructor
    · have happ := P128Pow5T3.mds_mul_mdsInv_apply ⟨1, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
    · have happ := P128Pow5T3.mds_mul_mdsInv_apply ⟨2, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
  completeness := by
    circuit_proof_start [mainP128, PartialRounds.main, Orchard.Poseidon.PartialRounds.Gate.circuit,
      Orchard.Poseidon.PartialRounds.Gate.Spec]
    rcases h_env with ⟨hmid, hnext⟩
    have hnext0 := hnext ⟨0, by norm_num⟩
    have hnext1 := hnext ⟨1, by norm_num⟩
    have hnext2 := hnext ⟨2, by norm_num⟩
    norm_num at hnext0 hnext1 hnext2
    simp at hnext0 hnext1 hnext2
    rw [hmid, hnext0, hnext1, hnext2]
    change Orchard.Poseidon.PartialRounds.Gate.Spec (partialParamsP128 roundConstants round)
      (partialRowValueP128 roundConstants round { x0 := input_x0, x1 := input_x1, x2 := input_x2 })
    simp [partialRowValueP128_spec]

end PartialRounds

/-- Apply the 28 consecutive P128Pow5T3 partial-round rows used by `Pow5Chip::permute`,
starting at source round 4.  Each row represents two source partial rounds. -/
def partialRoundRows28P128 (roundConstants : Nat → State Fp)
    (state : Var State Fp) : Circuit Fp (Var State Fp) :=
  Circuit.foldl (.finRange 28) state
    (fun state i => PartialRounds.circuitP128 roundConstants (4 + 2 * i.val) state)
    (by simp only [circuit_norm, PartialRounds.circuitP128])
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      simp [PartialRounds.circuitP128, circuit_norm])

/-- Packaged fixed 28-row P128 partial-round loop. -/
def partialRoundRows28P128Circuit (roundConstants : Nat → State Fp) :
    FormalCircuit Fp State State where
  name := "Pow5State::partial_rounds[28][P128]"
  main := partialRoundRows28P128 roundConstants
  Spec input output := output = partialRoundRows28P128Value roundConstants input
  soundness := by
    circuit_proof_start [partialRoundRows28P128, partialRoundRows28P128Value,
      PartialRounds.circuitP128]
    obtain ⟨h0, h_step⟩ := h_holds
    let inputState : State Fp := { x0 := input_x0, x1 := input_x1, x2 := input_x2 }
    let envState : Nat → State Fp := fun k =>
      if k = 0 then inputState else
        { x0 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1)
          x1 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1 + 1)
          x2 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1 + 1 + 1) }
    have hround : ∀ k (hk : k < 28),
        envState (k + 1) =
          partialRoundValue (partialParamsP128 roundConstants (4 + 2 * k)) (envState k) := by
      intro k hk
      cases k with
      | zero =>
          simp [envState, inputState]
          simpa using h0
      | succ j =>
          have hj := h_step j (by omega)
          simp [envState]
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.mul_add, Nat.add_mul] using hj
    have hind : ∀ k (hk : k ≤ 28),
        envState k = Fin.foldl k
          (fun state i => partialRoundValue (partialParamsP128 roundConstants (4 + 2 * i.val)) state)
          inputState := by
      intro k hk
      induction k with
      | zero => simp [envState, inputState]
      | succ k ih =>
          have hklt : k < 28 := by omega
          have ih' := ih (by omega)
          rw [Fin.foldl_succ_last]
          rw [show (fun x1 (x2 : Fin k) =>
              partialRoundValue (partialParamsP128 roundConstants (4 + 2 * ↑x2.castSucc)) x1) =
              (fun state (i : Fin k) =>
                partialRoundValue (partialParamsP128 roundConstants (4 + 2 * i.val)) state) from rfl]
          rw [← ih']
          simpa [show (Fin.last k).val = k by rfl] using hround k hklt
    have h28 := hind 28 (by omega)
    simpa [envState, inputState] using h28
  completeness := by
    circuit_proof_start [partialRoundRows28P128, partialRoundRows28P128Value,
      PartialRounds.circuitP128]

/-- Apply the four consecutive full-round rows used by `Pow5Chip::permute`, starting
at source round `round`. -/
def fullRounds4 (roundConstants : Nat → State Fp) (mds : Nat → Nat → Fp)
    (round : Nat) (state : Var State Fp) : Circuit Fp (Var State Fp) :=
  Circuit.foldl (.finRange 4) state
    (fun state i => FullRound.circuit (fullParams roundConstants mds (round + i.val)) state)
    (by simp only [circuit_norm, FullRound.circuit])
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      simp [FullRound.circuit, circuit_norm])

/-- Packaged four-full-round loop used by each half of `Pow5Chip::permute`. -/
def fullRounds4Circuit (roundConstants : Nat → State Fp) (mds : Nat → Nat → Fp)
    (round : Nat) : FormalCircuit Fp State State where
  name := "Pow5State::full_rounds[4]"
  main := fullRounds4 roundConstants mds round
  Spec input output := output = fullRounds4Value roundConstants mds round input
  soundness := by
    circuit_proof_start [fullRounds4, fullRounds4Value, FullRound.circuit]
    obtain ⟨h0, h_step⟩ := h_holds
    have h1 := h_step 0 (by norm_num)
    have h2 := h_step 1 (by norm_num)
    have h3 := h_step 2 (by norm_num)
    simp only [Fin.foldl_succ_last, Fin.foldl_zero] at h0 h1 h2 h3 ⊢
    norm_num at h1 h2 h3 ⊢
    rw [h0] at h1
    rw [h1] at h2
    rw [h2] at h3
    simpa using h3
  completeness := by
    circuit_proof_start [fullRounds4, fullRounds4Value, FullRound.circuit]

/-- P128Pow5T3-specialized `Pow5Chip::permute` circuit shape. -/
def mainP128 (roundConstants : Nat → State Fp)
    (input : Var State Fp) : Circuit Fp (Var State Fp) := do
  let s ← fullRounds4Circuit roundConstants P128Pow5T3.mds 0 input
  let s ← partialRoundRows28P128Circuit roundConstants s
  fullRounds4Circuit roundConstants P128Pow5T3.mds (4 + 56) s

/-- Packaged P128Pow5T3 `Pow5Chip::permute` circuit. -/
def mainP128Circuit (roundConstants : Nat → State Fp) :
    FormalCircuit Fp State State where
  name := "Pow5Chip::permute[P128]"
  main := mainP128 roundConstants
  Spec input output := output = permuteP128Value roundConstants input
  soundness := by
    circuit_proof_start [mainP128, permuteP128Value, fullRounds4Circuit,
      partialRoundRows28P128Circuit]
    rcases h_holds with ⟨hfull0, hpartial, hfull1⟩
    rw [hfull0] at hpartial
    rw [hpartial] at hfull1
    simpa using hfull1
  completeness := by
    circuit_proof_start [mainP128, permuteP128Value, fullRounds4Circuit,
      partialRoundRows28P128Circuit]

/-- Concrete P128Pow5T3 value-level permutation using the ported Pallas round constants. -/
def permuteP128ConcreteValue : State Fp → State Fp :=
  permuteP128Value P128Pow5T3.roundConstants

/-- Concrete P128Pow5T3 `Pow5Chip::permute` circuit using the ported Pallas constants. -/
def mainP128Concrete (input : Var State Fp) : Circuit Fp (Var State Fp) :=
  mainP128 P128Pow5T3.roundConstants input

/-- Packaged concrete P128Pow5T3 `Pow5Chip::permute` circuit. -/
def mainP128ConcreteCircuit : FormalCircuit Fp State State :=
  mainP128Circuit P128Pow5T3.roundConstants

end Permute

end Poseidon
end Orchard
