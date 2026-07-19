import Clean.Circuit
import Clean.Ironwood.Poseidon.Constants

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

namespace Halo2.Ironwood.Poseidon

def pow5 {K : Type} [Mul K] (x : K) : K :=
  let x2 := x * x
  x2 * x2 * x

/-- `pow5` commutes with witness-IR evaluation, since it is built purely from `*`. -/
theorem pow5_FExpr_eval (ctx : Witgen.Ctx Fp) (x : Witgen.FExpr Fp) :
    Witgen.FExprOver.eval ctx (pow5 x) = pow5 (Witgen.FExprOver.eval ctx x) := by
  simp [pow5, circuit_norm]

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

def Spec (params : Params Fp) (row : Input Fp) : Prop :=
  row.next0 =
    pow5 (row.cur0 + params.rcA0) * params.m00 +
      pow5 (row.cur1 + params.rcA1) * params.m01 +
      pow5 (row.cur2 + params.rcA2) * params.m02 ∧
  row.next1 =
    pow5 (row.cur0 + params.rcA0) * params.m10 +
      pow5 (row.cur1 + params.rcA1) * params.m11 +
      pow5 (row.cur2 + params.rcA2) * params.m12 ∧
  row.next2 =
    pow5 (row.cur0 + params.rcA0) * params.m20 +
      pow5 (row.cur1 + params.rcA1) * params.m21 +
      pow5 (row.cur2 + params.rcA2) * params.m22

end Gate
/-- Constants needed by one width-3 full round. -/
def params (roundConstants : Nat → Permute.State Fp) (mds : Nat → Nat → Fp)
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

/-- Value-level full-round transition, matching `Pow5State::full_round`. -/
def value (params : FullRound.Gate.Params Fp) (state : Permute.State Fp) : Permute.State Fp :=
  let s0 := pow5 (state.x0 + params.rcA0)
  let s1 := pow5 (state.x1 + params.rcA1)
  let s2 := pow5 (state.x2 + params.rcA2)
  { x0 := s0 * params.m00 + s1 * params.m01 + s2 * params.m02
    x1 := s0 * params.m10 + s1 * params.m11 + s2 * params.m12
    x2 := s0 * params.m20 + s1 * params.m21 + s2 * params.m22 }

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

def Params.toFExpr (params : Params Fp) :
    Params (Witgen.FExpr Fp) where
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

def Spec (params : Params Fp) (row : Input Fp) : Prop :=
  let mid0 := row.mid0Sbox * params.m00 + (row.cur1 + params.rcA1) * params.m01 +
    (row.cur2 + params.rcA2) * params.m02
  let mid1 := row.mid0Sbox * params.m10 + (row.cur1 + params.rcA1) * params.m11 +
    (row.cur2 + params.rcA2) * params.m12
  let mid2 := row.mid0Sbox * params.m20 + (row.cur1 + params.rcA1) * params.m21 +
    (row.cur2 + params.rcA2) * params.m22
  let nextInv0 := row.next0 * params.mInv00 + row.next1 * params.mInv01 +
    row.next2 * params.mInv02
  let nextInv1 := row.next0 * params.mInv10 + row.next1 * params.mInv11 +
    row.next2 * params.mInv12
  let nextInv2 := row.next0 * params.mInv20 + row.next1 * params.mInv21 +
    row.next2 * params.mInv22
  row.mid0Sbox = pow5 (row.cur0 + params.rcA0) ∧
    nextInv0 = pow5 (mid0 + params.rcB0) ∧
    nextInv1 = mid1 + params.rcB1 ∧
    nextInv2 = mid2 + params.rcB2

end Gate
/-- Constants needed by one width-3 partial-round row, which checks two source rounds. -/
def params (roundConstants : Nat → Permute.State Fp) (mds mdsInv : Nat → Nat → Fp)
    (round : Nat) : Gate.Params Fp where
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
def paramsP128 (roundConstants : Nat → Permute.State Fp) (round : Nat) :
    Gate.Params Fp :=
  params roundConstants Permute.P128Pow5T3.mds Permute.P128Pow5T3.mdsInv round

/-- The first-round S-box value witnessed in a partial-round row. -/
def mid0SboxValue {K : Type} [Add K] [Mul K] (params : Gate.Params K) (state : Permute.State K) : K :=
  pow5 (state.x0 + params.rcA0)

/-- Value-level partial-round-row transition, matching `Pow5State::partial_round`. -/
def value {K : Type} [Add K] [Mul K] (params : Gate.Params K) (state : Permute.State K) :
    Permute.State K :=
  let mid0Sbox := mid0SboxValue params state
  let mid0 := mid0Sbox * params.m00 + (state.x1 + params.rcA1) * params.m01 +
    (state.x2 + params.rcA2) * params.m02
  let mid1 := mid0Sbox * params.m10 + (state.x1 + params.rcA1) * params.m11 +
    (state.x2 + params.rcA2) * params.m12
  let mid2 := mid0Sbox * params.m20 + (state.x1 + params.rcA1) * params.m21 +
    (state.x2 + params.rcA2) * params.m22
  let r0 := pow5 (mid0 + params.rcB0)
  let r1 := mid1 + params.rcB1
  let r2 := mid2 + params.rcB2
  { x0 := r0 * params.m00 + r1 * params.m01 + r2 * params.m02
    x1 := r0 * params.m10 + r1 * params.m11 + r2 * params.m12
    x2 := r0 * params.m20 + r1 * params.m21 + r2 * params.m22 }

/-- The concrete row witnessed by the honest P128 partial-round prover. -/
def inputP128 (roundConstants : Nat → Permute.State Fp) (round : Nat)
    (state : Permute.State Fp) : Gate.Input Fp :=
  let params := paramsP128 roundConstants round
  let next := value params state
  { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
    mid0Sbox := mid0SboxValue params state,
    next0 := next.x0, next1 := next.x1, next2 := next.x2 }

/-- The honest P128 partial-round row satisfies the Halo2 gate relation. -/
theorem inputP128_spec (roundConstants : Nat → Permute.State Fp) (round : Nat)
    (state : Permute.State Fp) :
    Gate.Spec (paramsP128 roundConstants round)
      (inputP128 roundConstants round state) := by
  constructor
  · rfl
  constructor
  · simp [inputP128, value, mid0SboxValue,
      paramsP128, params]
    exact Permute.P128Pow5T3.mdsInv_mul_mds_apply ⟨0, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)
  constructor
  · simp [inputP128, value, mid0SboxValue,
      paramsP128, params]
    exact Permute.P128Pow5T3.mdsInv_mul_mds_apply ⟨1, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)
  · simp [inputP128, value, mid0SboxValue,
      paramsP128, params]
    exact Permute.P128Pow5T3.mdsInv_mul_mds_apply ⟨2, by norm_num⟩
      (pow5 (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 0 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 0 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 0 2 +
        (roundConstants (round + 1)).x0))
      (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 1 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 1 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 1 2 +
        (roundConstants (round + 1)).x1)
      (pow5 (state.x0 + (roundConstants round).x0) * Permute.P128Pow5T3.mds 2 0 +
        (state.x1 + (roundConstants round).x1) * Permute.P128Pow5T3.mds 2 1 +
        (state.x2 + (roundConstants round).x2) * Permute.P128Pow5T3.mds 2 2 +
        (roundConstants (round + 1)).x2)

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

def Spec (row : Input Fp) : Prop :=
  row.output0 = row.initial0 + row.input0 ∧
    row.output1 = row.initial1 + row.input1 ∧
    row.output2 = row.initial2

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

/-! ### Plain Lean permutation specification -/

/-- Plain Lean implementation of Orchard's `P128Pow5T3` `Pow5Chip::permute` schedule. -/
def value (roundConstants : Nat → State Fp) (input : State Fp) : State Fp :=
  let s := Fin.foldl 4
    (fun state i => FullRound.value
      (FullRound.params roundConstants P128Pow5T3.mds i.val) state)
    input
  let s := Fin.foldl 28
    (fun state i =>
      PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i.val)) state)
    s
  Fin.foldl 4
    (fun state i => FullRound.value
      (FullRound.params roundConstants P128Pow5T3.mds (4 + 56 + i.val)) state)
    s

/-! ### Circuit implementation -/

/-- Concrete P128Pow5T3 value-level permutation using the ported Pallas round constants. -/
def concreteValue : State Fp → State Fp :=
  value P128Pow5T3.roundConstants

end Permute

end Halo2.Ironwood.Poseidon
