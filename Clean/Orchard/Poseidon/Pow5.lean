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

/-- Width-3 Poseidon state used by Orchard's `P128Pow5T3`. -/
structure State (F : Type) where
  x0 : F
  x1 : F
  x2 : F
deriving ProvableStruct

/-- Constants needed by one width-3 full round. -/
def fullParams (roundConstants : Nat → State Ecc.Fp) (mds : Nat → Nat → Ecc.Fp)
    (round : Nat) : FullRound.Params Ecc.Fp where
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
def partialParams (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp)
    (round : Nat) : PartialRounds.Params Ecc.Fp where
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

/-- Value-level full-round transition, matching `Pow5State::full_round`. -/
def fullRoundValue (params : FullRound.Params Ecc.Fp) (state : State Ecc.Fp) : State Ecc.Fp :=
  let row : FullRound.Row Ecc.Fp :=
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      next0 := 0, next1 := 0, next2 := 0 }
  { x0 := FullRound.output0 params row
    x1 := FullRound.output1 params row
    x2 := FullRound.output2 params row }

/-- The first-round S-box value witnessed in a partial-round row. -/
def partialMid0SboxValue (params : PartialRounds.Params Ecc.Fp) (state : State Ecc.Fp) : Ecc.Fp :=
  pow5 (state.x0 + params.rcA0)

/-- Value-level partial-round-row transition, matching `Pow5State::partial_round`. -/
def partialRoundValue (params : PartialRounds.Params Ecc.Fp) (state : State Ecc.Fp) : State Ecc.Fp :=
  let rowWithMid : PartialRounds.Row Ecc.Fp :=
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      mid0Sbox := partialMid0SboxValue params state,
      next0 := 0, next1 := 0, next2 := 0 }
  let r0 := pow5 (PartialRounds.mid0 params rowWithMid + params.rcB0)
  let r1 := PartialRounds.mid1 params rowWithMid + params.rcB1
  let r2 := PartialRounds.mid2 params rowWithMid + params.rcB2
  { x0 := r0 * params.m00 + r1 * params.m01 + r2 * params.m02
    x1 := r0 * params.m10 + r1 * params.m11 + r2 * params.m12
    x2 := r0 * params.m20 + r1 * params.m21 + r2 * params.m22 }

/-- One source-shaped full-round row: witness the next state internally and assert the
`full round` gate. -/
def fullRound (params : FullRound.Params Ecc.Fp) (state : Var State Ecc.Fp) :
    Circuit Ecc.Fp (Var State Ecc.Fp) := do
  let next ← witness fun env => fullRoundValue params (eval env state)
  FullRound.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- One source-shaped partial-round row: witness the intermediate S-box and next state
internally and assert the `partial rounds` gate. -/
def partialRound (params : PartialRounds.Params Ecc.Fp) (state : Var State Ecc.Fp) :
    Circuit Ecc.Fp (Var State Ecc.Fp) := do
  let mid0Sbox ← witness fun env => partialMid0SboxValue params (eval env state)
  let next ← witness fun env => partialRoundValue params (eval env state)
  PartialRounds.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      mid0Sbox,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- Apply `count` consecutive full-round rows starting at source round `round`. -/
def fullRounds (roundConstants : Nat → State Ecc.Fp) (mds : Nat → Nat → Ecc.Fp) :
    Nat → Nat → Var State Ecc.Fp → Circuit Ecc.Fp (Var State Ecc.Fp)
  | 0, _round, state => return state
  | count + 1, round, state => do
      let state ← fullRound (fullParams roundConstants mds round) state
      fullRounds roundConstants mds count (round + 1) state

/-- Apply `count` consecutive partial-round rows.  Each row represents two source
partial rounds, so the source round index advances by two. -/
def partialRoundRows (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp) :
    Nat → Nat → Var State Ecc.Fp → Circuit Ecc.Fp (Var State Ecc.Fp)
  | 0, _round, state => return state
  | count + 1, round, state => do
      let state ← partialRound (partialParams roundConstants mds mdsInv round) state
      partialRoundRows roundConstants mds mdsInv count (round + 2) state

/-- `Pow5Chip::permute` for Orchard's width-3/rate-2 Poseidon instance. -/
def main (roundConstants : Nat → State Ecc.Fp) (mds mdsInv : Nat → Nat → Ecc.Fp)
    (input : Var State Ecc.Fp) : Circuit Ecc.Fp (Var State Ecc.Fp) := do
  let s ← fullRounds roundConstants mds 4 0 input
  let s ← partialRoundRows roundConstants mds mdsInv 28 4 s
  fullRounds roundConstants mds 4 (4 + 56) s

/-!
The next step is to package `main` as a `FormalCircuit` with an explicit elaborated
instance and a value-level permutation spec.  Keeping the source-shaped `main` separate
for now lets downstream entry APIs compose the real schedule without exposing internal
round rows as caller inputs.
-/

end Permute

end Poseidon
end Orchard
