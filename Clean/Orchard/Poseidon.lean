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

def next0Check (row : Row R) : R :=
  s0 row * row.m00 + s1 row * row.m01 + s2 row * row.m02 - row.next0

def next1Check (row : Row R) : R :=
  s0 row * row.m10 + s1 row * row.m11 + s2 row * row.m12 - row.next1

def next2Check (row : Row R) : R :=
  s0 row * row.m20 + s1 row * row.m21 + s2 row * row.m22 - row.next2

def constraints (row : Row R) : Prop :=
  next0Check row = 0 ∧ next1Check row = 0 ∧ next2Check row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (next0Check row)
  assertZero (next1Check row)
  assertZero (next2Check row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, next0Check, next1Check, next2Check,
      s0, s1, s2, pow5]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, next0Check, next1Check, next2Check,
      s0, s1, s2, pow5]
    simp_all [sub_eq_add_neg]

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

def constraints (row : Row R) : Prop :=
  mid0Check row = 0 ∧
    next0Check row = 0 ∧
    next1Check row = 0 ∧
    next2Check row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (mid0Check row)
  assertZero (next0Check row)
  assertZero (next1Check row)
  assertZero (next2Check row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, mid0Check, next0Check, next1Check,
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, mid0Check, next0Check, next1Check,
      next2Check, mid0, mid1, mid2, nextInv0, nextInv1, nextInv2, pow5]
    simp_all [sub_eq_add_neg]

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

def constraints (row : Row R) : Prop :=
  output0Check row = 0 ∧ output1Check row = 0 ∧ capacityCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (output0Check row)
  assertZero (output1Check row)
  assertZero (capacityCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, output0Check, output1Check, capacityCheck]
    simp_all [sub_eq_add_neg]
  completeness := by
    circuit_proof_start [main, constraints, output0Check, output1Check, capacityCheck]
    simp_all [sub_eq_add_neg]

end PadAndAdd

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

def constraints (row : Row R) : Prop :=
  PadAndAdd.output0Check row.absorbed = 0 ∧
    PadAndAdd.output1Check row.absorbed = 0 ∧
    PadAndAdd.capacityCheck row.absorbed = 0 ∧
    initial0Check row = 0 ∧
    initial1Check row = 0 ∧
    capacityCheck row = 0 ∧
    input0Check row = 0 ∧
    input1Check row = 0 ∧
    hashCheck row = 0

def main (row : Var Row F) : Circuit F Unit := do
  assertZero (PadAndAdd.output0Check row.absorbed)
  assertZero (PadAndAdd.output1Check row.absorbed)
  assertZero (PadAndAdd.capacityCheck row.absorbed)
  assertZero (initial0Check row)
  assertZero (initial1Check row)
  assertZero (capacityCheck row)
  assertZero (input0Check row)
  assertZero (input1Check row)
  assertZero (hashCheck row)

def circuit : FormalAssertion F Row where
  main
  Spec := constraints
  soundness := by
    circuit_proof_start [main, constraints, initial0Check, initial1Check,
      capacityCheck, input0Check, input1Check, hashCheck, PadAndAdd.output0Check,
      PadAndAdd.output1Check, PadAndAdd.capacityCheck]
    simp_all [sub_eq_add_neg]
    constructor
    · have h := h_holds.1
      rw [h_holds.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h
    · have h := h_holds.2.1
      rw [h_holds.2.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h
  completeness := by
    circuit_proof_start [main, constraints, initial0Check, initial1Check,
      capacityCheck, input0Check, input1Check, hashCheck, PadAndAdd.output0Check,
      PadAndAdd.output1Check, PadAndAdd.capacityCheck]
    simp_all [sub_eq_add_neg]
    constructor
    · have h := h_spec.1
      rw [h_spec.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h
    · have h := h_spec.2.1
      rw [h_spec.2.2.2.2.1] at h
      simpa [sub_eq_add_neg] using h

end Hash2

end Poseidon
end Orchard
