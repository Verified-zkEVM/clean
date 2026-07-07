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

namespace Orchard.Poseidon

def pow5 {K : Type} [Mul K] (x : K) : K :=
  let x2 := x * x
  x2 * x2 * x

/-- `pow5` commutes with witness-IR evaluation, since it is built purely from `*`. -/
theorem pow5_FExpr_eval (ctx : Witgen.Ctx Fp) (x : Witgen.FExpr Fp) :
    Witgen.FExpr.eval ctx (pow5 x) = pow5 (Witgen.FExpr.eval ctx x) := by
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

def main (params : Params Fp)
    (row : Var Input Fp) : Circuit Fp Unit := do
  let paramsExpr := params.toExpr
  assertZero (
    pow5 (row.cur0 + paramsExpr.rcA0) * paramsExpr.m00 +
      pow5 (row.cur1 + paramsExpr.rcA1) * paramsExpr.m01 +
      pow5 (row.cur2 + paramsExpr.rcA2) * paramsExpr.m02 - row.next0)
  assertZero (
    pow5 (row.cur0 + paramsExpr.rcA0) * paramsExpr.m10 +
      pow5 (row.cur1 + paramsExpr.rcA1) * paramsExpr.m11 +
      pow5 (row.cur2 + paramsExpr.rcA2) * paramsExpr.m12 - row.next1)
  assertZero (
    pow5 (row.cur0 + paramsExpr.rcA0) * paramsExpr.m20 +
      pow5 (row.cur1 + paramsExpr.rcA1) * paramsExpr.m21 +
      pow5 (row.cur2 + paramsExpr.rcA2) * paramsExpr.m22 - row.next2)

def circuit (params : Params Fp) : FormalAssertion Fp Input where
  name := "GATE full round"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, pow5, Params.toExpr]
    rcases h_holds with ⟨h0, h1, h2⟩
    exact ⟨(sub_eq_zero.mp h0).symm, (sub_eq_zero.mp h1).symm, (sub_eq_zero.mp h2).symm⟩
  completeness := by
    circuit_proof_start [main, Spec, pow5, Params.toExpr]
    simp_all

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

/-- One source-shaped full-round row: witness the next state internally and assert the
`full round` gate. -/
def main (params : Gate.Params Fp) (state : Var Permute.State Fp) :
    Circuit Fp (Var Permute.State Fp) := do
  let next : Var Permute.State Fp ← witnessProgram do
    let s0 ← pow5 (K := Witgen.FExpr Fp) (state.x0 + params.rcA0)
    let s1 ← pow5 (K := Witgen.FExpr Fp) (state.x1 + params.rcA1)
    let s2 ← pow5 (K := Witgen.FExpr Fp) (state.x2 + params.rcA2)
    return Permute.State.mk
      (s0 * params.m00 + s1 * params.m01 + s2 * params.m02)
      (s0 * params.m10 + s1 * params.m11 + s2 * params.m12)
      (s0 * params.m20 + s1 * params.m21 + s2 * params.m22)
  Gate.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- Packaged full-round loop body. -/
def circuit (params : Gate.Params Fp) : FormalCircuit Fp Permute.State Permute.State where
  name := "Pow5State::full_round"
  main := main params
  Spec input output := output = value params input
  soundness := by
    circuit_proof_start [main, value, Gate.circuit, Gate.Spec, pow5]
    rcases h_holds with ⟨h0, h1, h2⟩
    simp [Permute.State.mk.injEq] at h0 h1 h2 ⊢
    exact ⟨h0, h1, h2⟩
  completeness := by
    circuit_proof_start [main, value, Gate.circuit, Gate.Spec, pow5]
    change env.ExtendsVector ((Witgen.M.toIRLiteral (value := Permute.State) _).eval env) i₀ at h_env
    rw [ProverEnvironment.extendsVector_toIRLiteral] at h_env
    simp_all [circuit_norm]

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

def main (params : Params Fp)
    (row : Var Input Fp) : Circuit Fp Unit := do
  let paramsExpr := params.toExpr
  let mid0 := row.mid0Sbox * paramsExpr.m00 + (row.cur1 + paramsExpr.rcA1) * paramsExpr.m01 +
    (row.cur2 + paramsExpr.rcA2) * paramsExpr.m02
  let mid1 := row.mid0Sbox * paramsExpr.m10 + (row.cur1 + paramsExpr.rcA1) * paramsExpr.m11 +
    (row.cur2 + paramsExpr.rcA2) * paramsExpr.m12
  let mid2 := row.mid0Sbox * paramsExpr.m20 + (row.cur1 + paramsExpr.rcA1) * paramsExpr.m21 +
    (row.cur2 + paramsExpr.rcA2) * paramsExpr.m22
  let nextInv0 := row.next0 * paramsExpr.mInv00 + row.next1 * paramsExpr.mInv01 +
    row.next2 * paramsExpr.mInv02
  let nextInv1 := row.next0 * paramsExpr.mInv10 + row.next1 * paramsExpr.mInv11 +
    row.next2 * paramsExpr.mInv12
  let nextInv2 := row.next0 * paramsExpr.mInv20 + row.next1 * paramsExpr.mInv21 +
    row.next2 * paramsExpr.mInv22
  assertZero (pow5 (row.cur0 + paramsExpr.rcA0) - row.mid0Sbox)
  assertZero (pow5 (mid0 + paramsExpr.rcB0) - nextInv0)
  assertZero (mid1 + paramsExpr.rcB1 - nextInv1)
  assertZero (mid2 + paramsExpr.rcB2 - nextInv2)

def circuit (params : Params Fp) : FormalAssertion Fp Input where
  name := "GATE partial rounds"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, pow5, Params.toExpr]
    rcases h_holds with ⟨hmid, h0, h1, h2⟩
    exact ⟨(sub_eq_zero.mp hmid).symm, (sub_eq_zero.mp h0).symm,
      (sub_eq_zero.mp h1).symm, (sub_eq_zero.mp h2).symm⟩
  completeness := by
    circuit_proof_start [main, Spec, pow5, Params.toExpr]
    simp_all

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

/-- One source-shaped partial-round row: witness the intermediate S-box and next state
internally and assert the `partial rounds` gate. -/
def main (params : Gate.Params Fp) (state : Var Permute.State Fp) :
    Circuit Fp (Var Permute.State Fp) := do
  let mid0Sbox ← witness <|
    mid0SboxValue (K := Witgen.FExpr Fp) params.toFExpr (Permute.State.mk state.x0 state.x1 state.x2)
  let next ← witness <|
    value (K := Witgen.FExpr Fp) params.toFExpr (Permute.State.mk state.x0 state.x1 state.x2)
  Gate.circuit params
    { cur0 := state.x0, cur1 := state.x1, cur2 := state.x2,
      mid0Sbox,
      next0 := next.x0, next1 := next.x1, next2 := next.x2 }
  return next

/-- One P128Pow5T3 source-shaped partial-round row. -/
def mainP128 (roundConstants : Nat → Permute.State Fp) (round : Nat)
    (state : Var Permute.State Fp) : Circuit Fp (Var Permute.State Fp) :=
  PartialRounds.main (paramsP128 roundConstants round) state

/-- Packaged P128Pow5T3 partial-round-row loop body. -/
def circuitP128 (roundConstants : Nat → Permute.State Fp) (round : Nat) :
    FormalCircuit Fp Permute.State Permute.State where
  name := "Pow5State::partial_round[P128]"
  main := mainP128 roundConstants round
  Spec input output := output = value (paramsP128 roundConstants round) input
  soundness := by
    circuit_proof_start [mainP128, PartialRounds.main, value, mid0SboxValue,
      Gate.circuit, Gate.Spec, paramsP128, params]
    rcases h_holds with ⟨hmid, h0, h1, h2⟩
    simp [Permute.State.mk.injEq] at hmid h0 h1 h2 ⊢
    constructor
    · have happ := Permute.P128Pow5T3.mds_mul_mdsInv_apply ⟨0, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
    constructor
    · have happ := Permute.P128Pow5T3.mds_mul_mdsInv_apply ⟨1, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
    · have happ := Permute.P128Pow5T3.mds_mul_mdsInv_apply ⟨2, by norm_num⟩
        (env.get (i₀ + 1)) (env.get (i₀ + 1 + 1)) (env.get (i₀ + 1 + 1 + 1))
      rw [h0, h1, h2] at happ
      simpa [hmid] using happ.symm
  completeness := by
    -- TODO(4.30 bump): legacy defeq so `circuit_norm`'s witness-IR completeness lemmas
    -- (`extendsVector_ofFExprs` etc.) keep matching through stuck `size`/`localLength`
    -- indices (lean4#12179).
    set_option backward.isDefEq.respectTransparency false in
    circuit_proof_start [mainP128, PartialRounds.main, Gate.circuit,
      Gate.Spec]
    rcases h_env with ⟨hmid, hnext⟩
    simp [mid0SboxValue, value, Gate.Params.toFExpr, circuit_norm, Permute.State.mk.injEq,
      pow5_FExpr_eval, h_input] at hmid hnext
    obtain ⟨hnext0, hnext1, hnext2⟩ := hnext
    rw [hmid, hnext0, hnext1, hnext2]
    change Gate.Spec (paramsP128 roundConstants round)
      (inputP128 roundConstants round { x0 := input_x0, x1 := input_x1, x2 := input_x2 })
    simp [inputP128_spec]

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

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertZero (row.initial0 + row.input0 - row.output0)
  assertZero (row.initial1 + row.input1 - row.output1)
  assertZero (row.initial2 - row.output2)

def circuit : FormalAssertion Fp Input where
  name := "GATE pad-and-add"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec]
    rcases h_holds with ⟨h0, h1, h2⟩
    exact ⟨(sub_eq_zero.mp h0).symm, (sub_eq_zero.mp h1).symm, (sub_eq_zero.mp h2).symm⟩
  completeness := by
    circuit_proof_start [main, Spec]
    simp_all

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
  Spec input output := output = Fin.foldl 28
    (fun state i =>
      PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i.val)) state)
    input
  soundness := by
    circuit_proof_start [partialRoundRows28P128, PartialRounds.circuitP128]
    obtain ⟨h0, h_step⟩ := h_holds
    let inputState : State Fp := { x0 := input_x0, x1 := input_x1, x2 := input_x2 }
    let envState : Nat → State Fp := fun k =>
      if k = 0 then inputState else
        { x0 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1)
          x1 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1 + 1)
          x2 := env.get (i₀ + (k - 1) * (1 + [1, 1, 1].sum) + 1 + 1 + 1) }
    have hround : ∀ k (hk : k < 28),
        envState (k + 1) =
          PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * k)) (envState k) := by
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
          (fun state i => PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i.val)) state)
          inputState := by
      intro k hk
      induction k with
      | zero => simp [envState, inputState]
      | succ k ih =>
          have hklt : k < 28 := by omega
          have ih' := ih (by omega)
          rw [Fin.foldl_succ_last]
          rw [show (fun x1 (x2 : Fin k) =>
              PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * ↑x2.castSucc)) x1) =
              (fun state (i : Fin k) =>
                PartialRounds.value (PartialRounds.paramsP128 roundConstants (4 + 2 * i.val)) state) from rfl]
          rw [← ih']
          simpa [show (Fin.last k).val = k by rfl] using hround k hklt
    have h28 := hind 28 (by omega)
    simpa [envState, inputState] using h28
  completeness := by
    circuit_proof_start [partialRoundRows28P128, PartialRounds.circuitP128]

/-- Apply the four consecutive full-round rows used by `Pow5Chip::permute`, starting
at source round `round`. -/
def fullRounds4 (roundConstants : Nat → State Fp) (mds : Nat → Nat → Fp)
    (round : Nat) (state : Var State Fp) : Circuit Fp (Var State Fp) :=
  Circuit.foldl (.finRange 4) state
    (fun state i => FullRound.circuit (FullRound.params roundConstants mds (round + i.val)) state)
    (by simp only [circuit_norm, FullRound.circuit])
    (by
      apply Circuit.ConstantLength.fromConstantLength'
      simp [FullRound.circuit, circuit_norm])

/-- Packaged four-full-round loop used by each half of `Pow5Chip::permute`. -/
def fullRounds4Circuit (roundConstants : Nat → State Fp) (mds : Nat → Nat → Fp)
    (round : Nat) : FormalCircuit Fp State State where
  name := "Pow5State::full_rounds[4]"
  main := fullRounds4 roundConstants mds round
  Spec input output := output = Fin.foldl 4
    (fun state i => FullRound.value (FullRound.params roundConstants mds (round + i.val)) state)
    input
  soundness := by
    circuit_proof_start [fullRounds4, FullRound.circuit]
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
    circuit_proof_start [fullRounds4, FullRound.circuit]

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
  Spec input output := output = value roundConstants input
  soundness := by
    circuit_proof_start [mainP128, value, fullRounds4Circuit,
      partialRoundRows28P128Circuit]
    rcases h_holds with ⟨hfull0, hpartial, hfull1⟩
    rw [hfull0] at hpartial
    rw [hpartial] at hfull1
    simpa using hfull1
  completeness := by
    circuit_proof_start [mainP128, value, fullRounds4Circuit,
      partialRoundRows28P128Circuit]

/-- Concrete P128Pow5T3 value-level permutation using the ported Pallas round constants. -/
def concreteValue : State Fp → State Fp :=
  value P128Pow5T3.roundConstants

/-- Packaged concrete P128Pow5T3 `Pow5Chip::permute` circuit. -/
def mainP128ConcreteCircuit : FormalCircuit Fp State State :=
  mainP128Circuit P128Pow5T3.roundConstants

end Permute

end Orchard.Poseidon
