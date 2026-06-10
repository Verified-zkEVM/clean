import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard Poseidon Pow5 gates

Clean approximations of the Halo2 `Pow5Chip` custom gates used by Orchard's
`P128Pow5T3` nullifier hash.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `full round`
- `partial rounds`
- `pad-and-add`

Orchard configures `Pow5Chip<pallas::Base, 3, 2>` in
`orchard@0.14.0/src/circuit.rs`. These assertions specialize the source polynomials to
width 3 and rate 2. Fixed columns such as round constants and MDS coefficients are
explicit row values in this approximation.
-/

namespace Orchard
namespace Poseidon

variable {F : Type} [Field F]

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

def pow5 (x : R) : R :=
  let x2 := x * x
  x2 * x2 * x

private theorem eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : b = a := by
  exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm

private theorem left_eq_of_add_neg_eq_zero {a b : F} (h : a + -b = 0) : a = b :=
  (eq_of_add_neg_eq_zero h).symm

namespace FullRound

structure Row (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  next0 : F
  next1 : F
  next2 : F
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
deriving ProvableStruct

def s0 (row : Row R) : R := pow5 (row.cur0 + row.rcA0)
def s1 (row : Row R) : R := pow5 (row.cur1 + row.rcA1)
def s2 (row : Row R) : R := pow5 (row.cur2 + row.rcA2)

def output0 (row : Row R) : R :=
  s0 row * row.m00 + s1 row * row.m01 + s2 row * row.m02

def output1 (row : Row R) : R :=
  s0 row * row.m10 + s1 row * row.m11 + s2 row * row.m12

def output2 (row : Row R) : R :=
  s0 row * row.m20 + s1 row * row.m21 + s2 row * row.m22

def next0Check (row : Row R) : R :=
  output0 row - row.next0

def next1Check (row : Row R) : R :=
  output1 row - row.next1

def next2Check (row : Row R) : R :=
  output2 row - row.next2

def Spec (row : Row R) : Prop :=
  row.next0 = output0 row ∧ row.next1 = output1 row ∧ row.next2 = output2 row

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (next0Check row)
  assertZero (next1Check row)
  assertZero (next2Check row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, next0Check, next1Check, next2Check,
      output0, output1, output2, s0, s1, s2, pow5]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · have h0' :
          (input_cur0 + input_rcA0) * (input_cur0 + input_rcA0) *
                  ((input_cur0 + input_rcA0) * (input_cur0 + input_rcA0)) *
                (input_cur0 + input_rcA0) * input_m00 +
              (input_cur1 + input_rcA1) * (input_cur1 + input_rcA1) *
                  ((input_cur1 + input_rcA1) * (input_cur1 + input_rcA1)) *
                (input_cur1 + input_rcA1) * input_m01 +
              (input_cur2 + input_rcA2) * (input_cur2 + input_rcA2) *
                  ((input_cur2 + input_rcA2) * (input_cur2 + input_rcA2)) *
                (input_cur2 + input_rcA2) * input_m02 - input_next0 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h0').symm
    constructor
    · have h1' :
          (input_cur0 + input_rcA0) * (input_cur0 + input_rcA0) *
                  ((input_cur0 + input_rcA0) * (input_cur0 + input_rcA0)) *
                (input_cur0 + input_rcA0) * input_m10 +
              (input_cur1 + input_rcA1) * (input_cur1 + input_rcA1) *
                  ((input_cur1 + input_rcA1) * (input_cur1 + input_rcA1)) *
                (input_cur1 + input_rcA1) * input_m11 +
              (input_cur2 + input_rcA2) * (input_cur2 + input_rcA2) *
                  ((input_cur2 + input_rcA2) * (input_cur2 + input_rcA2)) *
                (input_cur2 + input_rcA2) * input_m12 - input_next1 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h1').symm
    · have h2' :
          (input_cur0 + input_rcA0) * (input_cur0 + input_rcA0) *
                  ((input_cur0 + input_rcA0) * (input_cur0 + input_rcA0)) *
                (input_cur0 + input_rcA0) * input_m20 +
              (input_cur1 + input_rcA1) * (input_cur1 + input_rcA1) *
                  ((input_cur1 + input_rcA1) * (input_cur1 + input_rcA1)) *
                (input_cur1 + input_rcA1) * input_m21 +
              (input_cur2 + input_rcA2) * (input_cur2 + input_rcA2) *
                  ((input_cur2 + input_rcA2) * (input_cur2 + input_rcA2)) *
                (input_cur2 + input_rcA2) * input_m22 - input_next2 = 0 := by
        simp_all [sub_eq_add_neg]
      exact (sub_eq_zero.mp h2').symm
  completeness := by
    circuit_proof_start [main, Spec, next0Check, next1Check, next2Check,
      output0, output1, output2, s0, s1, s2, pow5]
    simp_all
    ring_nf
    simp

end FullRound

namespace PartialRounds

structure Row (F : Type) where
  cur0 : F
  cur1 : F
  cur2 : F
  mid0Sbox : F
  next0 : F
  next1 : F
  next2 : F
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
deriving ProvableStruct

def mid0Check (row : Row R) : R :=
  pow5 (row.cur0 + row.rcA0) - row.mid0Sbox

def mid0 (row : Row R) : R :=
  row.mid0Sbox * row.m00 + (row.cur1 + row.rcA1) * row.m01 +
    (row.cur2 + row.rcA2) * row.m02

def mid1 (row : Row R) : R :=
  row.mid0Sbox * row.m10 + (row.cur1 + row.rcA1) * row.m11 +
    (row.cur2 + row.rcA2) * row.m12

def mid2 (row : Row R) : R :=
  row.mid0Sbox * row.m20 + (row.cur1 + row.rcA1) * row.m21 +
    (row.cur2 + row.rcA2) * row.m22

def nextInv0 (row : Row R) : R :=
  row.next0 * row.mInv00 + row.next1 * row.mInv01 + row.next2 * row.mInv02

def nextInv1 (row : Row R) : R :=
  row.next0 * row.mInv10 + row.next1 * row.mInv11 + row.next2 * row.mInv12

def nextInv2 (row : Row R) : R :=
  row.next0 * row.mInv20 + row.next1 * row.mInv21 + row.next2 * row.mInv22

def next0Check (row : Row R) : R :=
  pow5 (mid0 row + row.rcB0) - nextInv0 row

def next1Check (row : Row R) : R :=
  mid1 row + row.rcB1 - nextInv1 row

def next2Check (row : Row R) : R :=
  mid2 row + row.rcB2 - nextInv2 row

def Spec (row : Row R) : Prop :=
  row.mid0Sbox = pow5 (row.cur0 + row.rcA0) ∧
    nextInv0 row = pow5 (mid0 row + row.rcB0) ∧
    nextInv1 row = mid1 row + row.rcB1 ∧
    nextInv2 row = mid2 row + row.rcB2

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (mid0Check row)
  assertZero (next0Check row)
  assertZero (next1Check row)
  assertZero (next2Check row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, mid0Check, next0Check, next1Check,
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5]
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
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5]
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

def output0Check (row : Row R) : R :=
  row.initial0 + row.input0 - row.output0

def output1Check (row : Row R) : R :=
  row.initial1 + row.input1 - row.output1

def capacityCheck (row : Row R) : R :=
  row.initial2 - row.output2

def Spec (row : Row R) : Prop :=
  row.output0 = row.initial0 + row.input0 ∧
    row.output1 = row.initial1 + row.input1 ∧
    row.output2 = row.initial2

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (output0Check row)
  assertZero (output1Check row)
  assertZero (capacityCheck row)

def circuit : FormalAssertion F Row where
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

/-!
Poseidon permutation row schedule.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon/pow5.rs`
- `Pow5Chip::permute`
- `Pow5State::full_round`
- `Pow5State::partial_round`

For `P128Pow5T3`, the source uses `R_F = 8` and `R_P = 56`. The Halo2 chip assigns
four full-round rows, twenty-eight rows each packing two partial rounds, and four final
full-round rows. The individual row assertions above record the round arithmetic. The
formal assertion below records the copied state between adjacent rows and the permutation
endpoints; fixed constants and matrix entries remain explicit row values.
-/
namespace Permutation

structure State (F : Type) where
  s0 : F
  s1 : F
  s2 : F
deriving ProvableStruct

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

structure FullRows (F : Type) where
  r0 : FullRound.Row F
  r1 : FullRound.Row F
  r2 : FullRound.Row F
  r3 : FullRound.Row F
deriving ProvableStruct

structure PartialRows (F : Type) where
  r0 : PartialRounds.Row F
  r1 : PartialRounds.Row F
  r2 : PartialRounds.Row F
  r3 : PartialRounds.Row F
  r4 : PartialRounds.Row F
  r5 : PartialRounds.Row F
  r6 : PartialRounds.Row F
  r7 : PartialRounds.Row F
  r8 : PartialRounds.Row F
  r9 : PartialRounds.Row F
  r10 : PartialRounds.Row F
  r11 : PartialRounds.Row F
  r12 : PartialRounds.Row F
  r13 : PartialRounds.Row F
  r14 : PartialRounds.Row F
  r15 : PartialRounds.Row F
  r16 : PartialRounds.Row F
  r17 : PartialRounds.Row F
  r18 : PartialRounds.Row F
  r19 : PartialRounds.Row F
  r20 : PartialRounds.Row F
  r21 : PartialRounds.Row F
  r22 : PartialRounds.Row F
  r23 : PartialRounds.Row F
  r24 : PartialRounds.Row F
  r25 : PartialRounds.Row F
  r26 : PartialRounds.Row F
  r27 : PartialRounds.Row F
deriving ProvableStruct

structure Row (F : Type) where
  initial : State F
  firstFull : FullRows F
  partialRows : PartialRows F
  lastFull : FullRows F
  output : State F
deriving ProvableStruct

def fullCur (row : FullRound.Row R) : State R where
  s0 := row.cur0
  s1 := row.cur1
  s2 := row.cur2

def fullNext (row : FullRound.Row R) : State R where
  s0 := row.next0
  s1 := row.next1
  s2 := row.next2

def partialCur (row : PartialRounds.Row R) : State R where
  s0 := row.cur0
  s1 := row.cur1
  s2 := row.cur2

def partialNext (row : PartialRounds.Row R) : State R where
  s0 := row.next0
  s1 := row.next1
  s2 := row.next2

def state0Check (a b : State R) : R := a.s0 - b.s0
def state1Check (a b : State R) : R := a.s1 - b.s1
def state2Check (a b : State R) : R := a.s2 - b.s2

def stateEq (a b : State R) : Prop :=
  state0Check a b = 0 ∧ state1Check a b = 0 ∧ state2Check a b = 0

def stateSame (a b : State R) : Prop :=
  a.s0 = b.s0 ∧ a.s1 = b.s1 ∧ a.s2 = b.s2

theorem stateEq_of_stateSame {a b : State F} (h : stateSame a b) : stateEq a b := by
  rcases h with ⟨h0, h1, h2⟩
  exact ⟨by simp [state0Check, h0], by simp [state1Check, h1], by simp [state2Check, h2]⟩

theorem stateSame_of_stateEq {a b : State F} (h : stateEq a b) : stateSame a b := by
  rcases h with ⟨h0, h1, h2⟩
  exact ⟨sub_eq_zero.mp (by simpa [state0Check] using h0),
    sub_eq_zero.mp (by simpa [state1Check] using h1),
    sub_eq_zero.mp (by simpa [state2Check] using h2)⟩

def assertStateEq (a b : State (Expression F)) : Circuit F Unit := do
  assertZero (state0Check a b)
  assertZero (state1Check a b)
  assertZero (state2Check a b)

def fullSpec (rows : FullRows R) : Prop :=
  FullRound.Spec rows.r0 ∧
    FullRound.Spec rows.r1 ∧
    FullRound.Spec rows.r2 ∧
    FullRound.Spec rows.r3

def partialSpec (rows : PartialRows R) : Prop :=
  PartialRounds.Spec rows.r0 ∧
    PartialRounds.Spec rows.r1 ∧
    PartialRounds.Spec rows.r2 ∧
    PartialRounds.Spec rows.r3 ∧
    PartialRounds.Spec rows.r4 ∧
    PartialRounds.Spec rows.r5 ∧
    PartialRounds.Spec rows.r6 ∧
    PartialRounds.Spec rows.r7 ∧
    PartialRounds.Spec rows.r8 ∧
    PartialRounds.Spec rows.r9 ∧
    PartialRounds.Spec rows.r10 ∧
    PartialRounds.Spec rows.r11 ∧
    PartialRounds.Spec rows.r12 ∧
    PartialRounds.Spec rows.r13 ∧
    PartialRounds.Spec rows.r14 ∧
    PartialRounds.Spec rows.r15 ∧
    PartialRounds.Spec rows.r16 ∧
    PartialRounds.Spec rows.r17 ∧
    PartialRounds.Spec rows.r18 ∧
    PartialRounds.Spec rows.r19 ∧
    PartialRounds.Spec rows.r20 ∧
    PartialRounds.Spec rows.r21 ∧
    PartialRounds.Spec rows.r22 ∧
    PartialRounds.Spec rows.r23 ∧
    PartialRounds.Spec rows.r24 ∧
    PartialRounds.Spec rows.r25 ∧
    PartialRounds.Spec rows.r26 ∧
    PartialRounds.Spec rows.r27

def fullLinks (rows : FullRows R) : Prop :=
  stateEq (fullNext rows.r0) (fullCur rows.r1) ∧
    stateEq (fullNext rows.r1) (fullCur rows.r2) ∧
    stateEq (fullNext rows.r2) (fullCur rows.r3)

def partialLinks (rows : PartialRows R) : Prop :=
  stateEq (partialNext rows.r0) (partialCur rows.r1) ∧
    stateEq (partialNext rows.r1) (partialCur rows.r2) ∧
    stateEq (partialNext rows.r2) (partialCur rows.r3) ∧
    stateEq (partialNext rows.r3) (partialCur rows.r4) ∧
    stateEq (partialNext rows.r4) (partialCur rows.r5) ∧
    stateEq (partialNext rows.r5) (partialCur rows.r6) ∧
    stateEq (partialNext rows.r6) (partialCur rows.r7) ∧
    stateEq (partialNext rows.r7) (partialCur rows.r8) ∧
    stateEq (partialNext rows.r8) (partialCur rows.r9) ∧
    stateEq (partialNext rows.r9) (partialCur rows.r10) ∧
    stateEq (partialNext rows.r10) (partialCur rows.r11) ∧
    stateEq (partialNext rows.r11) (partialCur rows.r12) ∧
    stateEq (partialNext rows.r12) (partialCur rows.r13) ∧
    stateEq (partialNext rows.r13) (partialCur rows.r14) ∧
    stateEq (partialNext rows.r14) (partialCur rows.r15) ∧
    stateEq (partialNext rows.r15) (partialCur rows.r16) ∧
    stateEq (partialNext rows.r16) (partialCur rows.r17) ∧
    stateEq (partialNext rows.r17) (partialCur rows.r18) ∧
    stateEq (partialNext rows.r18) (partialCur rows.r19) ∧
    stateEq (partialNext rows.r19) (partialCur rows.r20) ∧
    stateEq (partialNext rows.r20) (partialCur rows.r21) ∧
    stateEq (partialNext rows.r21) (partialCur rows.r22) ∧
    stateEq (partialNext rows.r22) (partialCur rows.r23) ∧
    stateEq (partialNext rows.r23) (partialCur rows.r24) ∧
    stateEq (partialNext rows.r24) (partialCur rows.r25) ∧
    stateEq (partialNext rows.r25) (partialCur rows.r26) ∧
    stateEq (partialNext rows.r26) (partialCur rows.r27)

def Spec (row : Row R) : Prop :=
  fullSpec row.firstFull ∧
    partialSpec row.partialRows ∧
    fullSpec row.lastFull ∧
    stateEq row.initial (fullCur row.firstFull.r0) ∧
    fullLinks row.firstFull ∧
    stateEq (fullNext row.firstFull.r3) (partialCur row.partialRows.r0) ∧
    partialLinks row.partialRows ∧
    stateEq (partialNext row.partialRows.r27) (fullCur row.lastFull.r0) ∧
    fullLinks row.lastFull ∧
    stateEq (fullNext row.lastFull.r3) row.output

def wiringSpec (row : Row R) : Prop :=
  stateEq row.initial (fullCur row.firstFull.r0) ∧
    fullLinks row.firstFull ∧
    stateEq (fullNext row.firstFull.r3) (partialCur row.partialRows.r0) ∧
    partialLinks row.partialRows ∧
    stateEq (partialNext row.partialRows.r27) (fullCur row.lastFull.r0) ∧
    fullLinks row.lastFull ∧
    stateEq (fullNext row.lastFull.r3) row.output

def main (row : Var Row F) : Circuit F Unit := do
  FullRound.circuit row.firstFull.r0
  FullRound.circuit row.firstFull.r1
  FullRound.circuit row.firstFull.r2
  FullRound.circuit row.firstFull.r3
  PartialRounds.circuit row.partialRows.r0
  PartialRounds.circuit row.partialRows.r1
  PartialRounds.circuit row.partialRows.r2
  PartialRounds.circuit row.partialRows.r3
  PartialRounds.circuit row.partialRows.r4
  PartialRounds.circuit row.partialRows.r5
  PartialRounds.circuit row.partialRows.r6
  PartialRounds.circuit row.partialRows.r7
  PartialRounds.circuit row.partialRows.r8
  PartialRounds.circuit row.partialRows.r9
  PartialRounds.circuit row.partialRows.r10
  PartialRounds.circuit row.partialRows.r11
  PartialRounds.circuit row.partialRows.r12
  PartialRounds.circuit row.partialRows.r13
  PartialRounds.circuit row.partialRows.r14
  PartialRounds.circuit row.partialRows.r15
  PartialRounds.circuit row.partialRows.r16
  PartialRounds.circuit row.partialRows.r17
  PartialRounds.circuit row.partialRows.r18
  PartialRounds.circuit row.partialRows.r19
  PartialRounds.circuit row.partialRows.r20
  PartialRounds.circuit row.partialRows.r21
  PartialRounds.circuit row.partialRows.r22
  PartialRounds.circuit row.partialRows.r23
  PartialRounds.circuit row.partialRows.r24
  PartialRounds.circuit row.partialRows.r25
  PartialRounds.circuit row.partialRows.r26
  PartialRounds.circuit row.partialRows.r27
  FullRound.circuit row.lastFull.r0
  FullRound.circuit row.lastFull.r1
  FullRound.circuit row.lastFull.r2
  FullRound.circuit row.lastFull.r3
  assertStateEq row.initial (fullCur row.firstFull.r0)
  assertStateEq (fullNext row.firstFull.r0) (fullCur row.firstFull.r1)
  assertStateEq (fullNext row.firstFull.r1) (fullCur row.firstFull.r2)
  assertStateEq (fullNext row.firstFull.r2) (fullCur row.firstFull.r3)
  assertStateEq (fullNext row.firstFull.r3) (partialCur row.partialRows.r0)
  assertStateEq (partialNext row.partialRows.r0) (partialCur row.partialRows.r1)
  assertStateEq (partialNext row.partialRows.r1) (partialCur row.partialRows.r2)
  assertStateEq (partialNext row.partialRows.r2) (partialCur row.partialRows.r3)
  assertStateEq (partialNext row.partialRows.r3) (partialCur row.partialRows.r4)
  assertStateEq (partialNext row.partialRows.r4) (partialCur row.partialRows.r5)
  assertStateEq (partialNext row.partialRows.r5) (partialCur row.partialRows.r6)
  assertStateEq (partialNext row.partialRows.r6) (partialCur row.partialRows.r7)
  assertStateEq (partialNext row.partialRows.r7) (partialCur row.partialRows.r8)
  assertStateEq (partialNext row.partialRows.r8) (partialCur row.partialRows.r9)
  assertStateEq (partialNext row.partialRows.r9) (partialCur row.partialRows.r10)
  assertStateEq (partialNext row.partialRows.r10) (partialCur row.partialRows.r11)
  assertStateEq (partialNext row.partialRows.r11) (partialCur row.partialRows.r12)
  assertStateEq (partialNext row.partialRows.r12) (partialCur row.partialRows.r13)
  assertStateEq (partialNext row.partialRows.r13) (partialCur row.partialRows.r14)
  assertStateEq (partialNext row.partialRows.r14) (partialCur row.partialRows.r15)
  assertStateEq (partialNext row.partialRows.r15) (partialCur row.partialRows.r16)
  assertStateEq (partialNext row.partialRows.r16) (partialCur row.partialRows.r17)
  assertStateEq (partialNext row.partialRows.r17) (partialCur row.partialRows.r18)
  assertStateEq (partialNext row.partialRows.r18) (partialCur row.partialRows.r19)
  assertStateEq (partialNext row.partialRows.r19) (partialCur row.partialRows.r20)
  assertStateEq (partialNext row.partialRows.r20) (partialCur row.partialRows.r21)
  assertStateEq (partialNext row.partialRows.r21) (partialCur row.partialRows.r22)
  assertStateEq (partialNext row.partialRows.r22) (partialCur row.partialRows.r23)
  assertStateEq (partialNext row.partialRows.r23) (partialCur row.partialRows.r24)
  assertStateEq (partialNext row.partialRows.r24) (partialCur row.partialRows.r25)
  assertStateEq (partialNext row.partialRows.r25) (partialCur row.partialRows.r26)
  assertStateEq (partialNext row.partialRows.r26) (partialCur row.partialRows.r27)
  assertStateEq (partialNext row.partialRows.r27) (fullCur row.lastFull.r0)
  assertStateEq (fullNext row.lastFull.r0) (fullCur row.lastFull.r1)
  assertStateEq (fullNext row.lastFull.r1) (fullCur row.lastFull.r2)
  assertStateEq (fullNext row.lastFull.r2) (fullCur row.lastFull.r3)
  assertStateEq (fullNext row.lastFull.r3) row.output

def wiringMain (row : Var Row F) : Circuit F Unit := do
  assertStateEq row.initial (fullCur row.firstFull.r0)
  assertStateEq (fullNext row.firstFull.r0) (fullCur row.firstFull.r1)
  assertStateEq (fullNext row.firstFull.r1) (fullCur row.firstFull.r2)
  assertStateEq (fullNext row.firstFull.r2) (fullCur row.firstFull.r3)
  assertStateEq (fullNext row.firstFull.r3) (partialCur row.partialRows.r0)
  assertStateEq (partialNext row.partialRows.r0) (partialCur row.partialRows.r1)
  assertStateEq (partialNext row.partialRows.r1) (partialCur row.partialRows.r2)
  assertStateEq (partialNext row.partialRows.r2) (partialCur row.partialRows.r3)
  assertStateEq (partialNext row.partialRows.r3) (partialCur row.partialRows.r4)
  assertStateEq (partialNext row.partialRows.r4) (partialCur row.partialRows.r5)
  assertStateEq (partialNext row.partialRows.r5) (partialCur row.partialRows.r6)
  assertStateEq (partialNext row.partialRows.r6) (partialCur row.partialRows.r7)
  assertStateEq (partialNext row.partialRows.r7) (partialCur row.partialRows.r8)
  assertStateEq (partialNext row.partialRows.r8) (partialCur row.partialRows.r9)
  assertStateEq (partialNext row.partialRows.r9) (partialCur row.partialRows.r10)
  assertStateEq (partialNext row.partialRows.r10) (partialCur row.partialRows.r11)
  assertStateEq (partialNext row.partialRows.r11) (partialCur row.partialRows.r12)
  assertStateEq (partialNext row.partialRows.r12) (partialCur row.partialRows.r13)
  assertStateEq (partialNext row.partialRows.r13) (partialCur row.partialRows.r14)
  assertStateEq (partialNext row.partialRows.r14) (partialCur row.partialRows.r15)
  assertStateEq (partialNext row.partialRows.r15) (partialCur row.partialRows.r16)
  assertStateEq (partialNext row.partialRows.r16) (partialCur row.partialRows.r17)
  assertStateEq (partialNext row.partialRows.r17) (partialCur row.partialRows.r18)
  assertStateEq (partialNext row.partialRows.r18) (partialCur row.partialRows.r19)
  assertStateEq (partialNext row.partialRows.r19) (partialCur row.partialRows.r20)
  assertStateEq (partialNext row.partialRows.r20) (partialCur row.partialRows.r21)
  assertStateEq (partialNext row.partialRows.r21) (partialCur row.partialRows.r22)
  assertStateEq (partialNext row.partialRows.r22) (partialCur row.partialRows.r23)
  assertStateEq (partialNext row.partialRows.r23) (partialCur row.partialRows.r24)
  assertStateEq (partialNext row.partialRows.r24) (partialCur row.partialRows.r25)
  assertStateEq (partialNext row.partialRows.r25) (partialCur row.partialRows.r26)
  assertStateEq (partialNext row.partialRows.r26) (partialCur row.partialRows.r27)
  assertStateEq (partialNext row.partialRows.r27) (fullCur row.lastFull.r0)
  assertStateEq (fullNext row.lastFull.r0) (fullCur row.lastFull.r1)
  assertStateEq (fullNext row.lastFull.r1) (fullCur row.lastFull.r2)
  assertStateEq (fullNext row.lastFull.r2) (fullCur row.lastFull.r3)
  assertStateEq (fullNext row.lastFull.r3) row.output

namespace InitialToFull

structure Row (F : Type) where
  initial : State F
  first : FullRound.Row F
deriving ProvableStruct

def Spec (row : Row R) : Prop :=
  stateSame row.initial (fullCur row.first)

def main (row : Var Row F) : Circuit F Unit := do
  assertStateEq row.initial (fullCur row.first)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullCur]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact left_eq_of_add_neg_eq_zero h0
    constructor
    · exact left_eq_of_add_neg_eq_zero h1
    · exact left_eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullCur]
    simp_all

end InitialToFull

namespace FullToFull

structure Row (F : Type) where
  prev : FullRound.Row F
  next : FullRound.Row F
deriving ProvableStruct

def Spec (row : Row R) : Prop :=
  stateSame (fullNext row.prev) (fullCur row.next)

def main (row : Var Row F) : Circuit F Unit := do
  assertStateEq (fullNext row.prev) (fullCur row.next)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullCur, fullNext]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact left_eq_of_add_neg_eq_zero h0
    constructor
    · exact left_eq_of_add_neg_eq_zero h1
    · exact left_eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullCur, fullNext]
    simp_all

end FullToFull

namespace FullToPartial

structure Row (F : Type) where
  prev : FullRound.Row F
  next : PartialRounds.Row F
deriving ProvableStruct

def Spec (row : Row R) : Prop :=
  stateSame (fullNext row.prev) (partialCur row.next)

def main (row : Var Row F) : Circuit F Unit := do
  assertStateEq (fullNext row.prev) (partialCur row.next)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullNext, partialCur]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact left_eq_of_add_neg_eq_zero h0
    constructor
    · exact left_eq_of_add_neg_eq_zero h1
    · exact left_eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullNext, partialCur]
    simp_all

end FullToPartial

namespace PartialToPartial

structure Row (F : Type) where
  prev : PartialRounds.Row F
  next : PartialRounds.Row F
deriving ProvableStruct

def Spec (row : Row R) : Prop :=
  stateSame (partialNext row.prev) (partialCur row.next)

def main (row : Var Row F) : Circuit F Unit := do
  assertStateEq (partialNext row.prev) (partialCur row.next)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, partialCur, partialNext]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact left_eq_of_add_neg_eq_zero h0
    constructor
    · exact left_eq_of_add_neg_eq_zero h1
    · exact left_eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, partialCur, partialNext]
    simp_all

end PartialToPartial

namespace PartialToFull

structure Row (F : Type) where
  prev : PartialRounds.Row F
  next : FullRound.Row F
deriving ProvableStruct

def Spec (row : Row R) : Prop :=
  stateSame (partialNext row.prev) (fullCur row.next)

def main (row : Var Row F) : Circuit F Unit := do
  assertStateEq (partialNext row.prev) (fullCur row.next)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullCur, partialNext]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact left_eq_of_add_neg_eq_zero h0
    constructor
    · exact left_eq_of_add_neg_eq_zero h1
    · exact left_eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullCur, partialNext]
    simp_all

end PartialToFull

namespace FullToOutput

structure Row (F : Type) where
  last : FullRound.Row F
  output : State F
deriving ProvableStruct

def Spec (row : Row R) : Prop :=
  stateSame (fullNext row.last) row.output

def main (row : Var Row F) : Circuit F Unit := do
  assertStateEq (fullNext row.last) row.output

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullNext]
    rcases h_holds with ⟨h0, h1, h2⟩
    constructor
    · exact left_eq_of_add_neg_eq_zero h0
    constructor
    · exact left_eq_of_add_neg_eq_zero h1
    · exact left_eq_of_add_neg_eq_zero h2
  completeness := by
    circuit_proof_start [main, Spec, stateSame, assertStateEq, stateEq, state0Check,
      state1Check, state2Check, fullNext]
    simp_all

end FullToOutput

namespace FullRowsBlock

def Spec (rows : FullRows R) : Prop :=
  fullSpec rows ∧ fullLinks rows

def main (rows : Var FullRows F) : Circuit F Unit := do
  FullRound.circuit rows.r0
  FullRound.circuit rows.r1
  FullRound.circuit rows.r2
  FullRound.circuit rows.r3
  FullToFull.circuit { prev := rows.r0, next := rows.r1 }
  FullToFull.circuit { prev := rows.r1, next := rows.r2 }
  FullToFull.circuit { prev := rows.r2, next := rows.r3 }

def circuit : FormalAssertion F FullRows where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, fullSpec, fullLinks,
      FullRound.circuit, FullRound.Spec, FullToFull.circuit, FullToFull.Spec,
      stateSame, stateEq, assertStateEq, fullCur, fullNext]
    rcases h_holds with ⟨h0, h1, h2, h3, h01, h12, h23⟩
    exact ⟨⟨h0, h1, h2, h3⟩, stateEq_of_stateSame h01,
      stateEq_of_stateSame h12, stateEq_of_stateSame h23⟩
  completeness := by
    circuit_proof_start [main, Spec, fullSpec, fullLinks,
      FullRound.circuit, FullRound.Spec, FullToFull.circuit, FullToFull.Spec,
      stateSame, stateEq, assertStateEq, fullCur, fullNext]
    rcases h_spec with ⟨⟨h0, h1, h2, h3⟩, h01, h12, h23⟩
    exact ⟨h0, h1, h2, h3, stateSame_of_stateEq h01,
      stateSame_of_stateEq h12, stateSame_of_stateEq h23⟩

end FullRowsBlock

end Permutation

/-!
Two-input Poseidon hash wiring used by Orchard nullifiers.

References:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon.rs`
- `Hash::init`
- `Hash::hash`

`halo2@halo2_poseidon-0.5.0/src/lib.rs`
- `ConstantLength<2>::initial_capacity_element`
- `ConstantLength<2>::padding`

For Orchard's `P128Pow5T3` nullifier hash, the width is 3 and the rate is 2. The
constant-length domain initializes state words 0 and 1 to zero, state word 2 to the
domain capacity element, absorbs exactly `nk` and `rho`, appends no padding, permutes,
and squeezes state word 0. The permutation result is represented by explicit row values;
the Pow5 gate rows above model the round arithmetic separately.
-/
namespace Hash2

structure Row (F : Type) where
  nk : F
  rho : F
  capacity : F
  absorbed : PadAndAdd.Row F
  permuted0 : F
  hash : F
deriving ProvableStruct

def initial0Check (row : Row R) : R :=
  row.absorbed.initial0

def initial1Check (row : Row R) : R :=
  row.absorbed.initial1

def capacityCheck (row : Row R) : R :=
  row.absorbed.initial2 - row.capacity

def input0Check (row : Row R) : R :=
  row.absorbed.input0 - row.nk

def input1Check (row : Row R) : R :=
  row.absorbed.input1 - row.rho

def hashCheck (row : Row R) : R :=
  row.permuted0 - row.hash

def Spec (row : Row R) : Prop :=
  PadAndAdd.Spec row.absorbed ∧
    row.absorbed.initial0 = 0 ∧
    row.absorbed.initial1 = 0 ∧
    row.absorbed.initial2 = row.capacity ∧
    row.absorbed.input0 = row.nk ∧
    row.absorbed.input1 = row.rho ∧
    row.hash = row.permuted0

def main (row : Var Row F) : Circuit F Unit := do
  PadAndAdd.circuit row.absorbed
  assertZero (initial0Check row)
  assertZero (initial1Check row)
  assertZero (capacityCheck row)
  assertZero (input0Check row)
  assertZero (input1Check row)
  assertZero (hashCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, PadAndAdd.Spec, initial0Check, initial1Check,
      capacityCheck, input0Check, input1Check, hashCheck, PadAndAdd.circuit]
    rcases h_holds with ⟨hAbsorbed, hInit0, hInit1, hCapacity, hInput0,
      hInput1, hHash⟩
    constructor
    · exact hAbsorbed
    constructor
    · exact hInit0
    constructor
    · exact hInit1
    constructor
    · exact left_eq_of_add_neg_eq_zero hCapacity
    constructor
    · exact left_eq_of_add_neg_eq_zero hInput0
    constructor
    · exact left_eq_of_add_neg_eq_zero hInput1
    · exact eq_of_add_neg_eq_zero hHash
  completeness := by
    circuit_proof_start [main, Spec, PadAndAdd.Spec, initial0Check, initial1Check,
      capacityCheck, input0Check, input1Check, hashCheck, PadAndAdd.circuit]
    simp_all

end Hash2

/-!
Boundary wiring between the two-input hash gadget and a Poseidon permutation schedule.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/poseidon.rs`
- `poseidon_sponge`
- `Hash::hash`

After absorption, the source permutes the whole width-3 state and squeezes state word 0.
This assertion connects `Hash2.circuit` to explicit permutation endpoint states. The
round rows and row-to-row schedule copies are represented by `Permutation.*` assertions.
-/
namespace Hash2PermutationBoundary

structure Row (F : Type) where
  hash : Hash2.Row F
  permutationInput : Permutation.State F
  permutationOutput : Permutation.State F
deriving ProvableStruct

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R]

def input0Check (row : Row R) : R :=
  row.hash.absorbed.output0 - row.permutationInput.s0

def input1Check (row : Row R) : R :=
  row.hash.absorbed.output1 - row.permutationInput.s1

def input2Check (row : Row R) : R :=
  row.hash.absorbed.output2 - row.permutationInput.s2

def outputCheck (row : Row R) : R :=
  row.permutationOutput.s0 - row.hash.permuted0

def Spec (row : Row R) : Prop :=
  Hash2.Spec row.hash ∧
    row.hash.absorbed.output0 = row.permutationInput.s0 ∧
    row.hash.absorbed.output1 = row.permutationInput.s1 ∧
    row.hash.absorbed.output2 = row.permutationInput.s2 ∧
    row.hash.permuted0 = row.permutationOutput.s0

def main (row : Var Row F) : Circuit F Unit := do
  Hash2.circuit row.hash
  assertZero (input0Check row)
  assertZero (input1Check row)
  assertZero (input2Check row)
  assertZero (outputCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, input0Check, input1Check, input2Check,
      outputCheck, Hash2.circuit, Hash2.Spec, Hash2.initial0Check,
      Hash2.initial1Check, Hash2.capacityCheck, Hash2.input0Check, Hash2.input1Check,
      Hash2.hashCheck, PadAndAdd.output0Check, PadAndAdd.output1Check,
      PadAndAdd.capacityCheck]
    rcases h_holds with ⟨hHash, h0, h1, h2, hOutput⟩
    constructor
    · exact hHash
    constructor
    · exact left_eq_of_add_neg_eq_zero h0
    constructor
    · exact left_eq_of_add_neg_eq_zero h1
    constructor
    · exact left_eq_of_add_neg_eq_zero h2
    · exact eq_of_add_neg_eq_zero hOutput
  completeness := by
    circuit_proof_start [main, Spec, input0Check, input1Check, input2Check,
      outputCheck, Hash2.circuit, Hash2.Spec, Hash2.initial0Check,
      Hash2.initial1Check, Hash2.capacityCheck, Hash2.input0Check, Hash2.input1Check,
      Hash2.hashCheck, PadAndAdd.output0Check, PadAndAdd.output1Check,
      PadAndAdd.capacityCheck]
    rcases h_spec with ⟨⟨hPad, hInit0, hInit1, hCapacity, hInput0, hInput1, hHash⟩,
      hBoundary0, hBoundary1, hBoundary2, hOutput⟩
    rcases hPad with ⟨hPad0, hPad1, hPad2⟩
    simp_all [PadAndAdd.Spec]

end Hash2PermutationBoundary

end Poseidon
end Orchard
