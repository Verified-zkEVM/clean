/-
The challenge field.

Committed values live in the native field `F`. A challenge, and everything computed from it, lives
in a field `K` with `[Algebra F K]`: `F` itself, or an extension of it when `F` is too small for
`deg / |F|` to be a useful error (BabyBear, Goldilocks, Mersenne-31, ...). A value of `K` is laid
out in native cells by a synthetic type `kty : CType F K`, which must be *faithful*: different
layouts mean different values, so that counting the bad layouts of a challenge counts bad values
of `K`, and the soundness error is `deg / |K|`.

`KArith.interface kty` is the arithmetic of `K` that the protocols use, as an ordinary vocabulary
of interfaces over `F`: embed a native value, `+ - *`, scale by a native value, invert, assert
zero, constants. `KArith.native` implements it for `K = F` from `Arith`; `Extension.lean`
implements it for any extension with a basis.
-/
module

public import Clean2.Challenge.Phase
public import Clean2.Gadgets.Inverse
public import Mathlib.Algebra.Algebra.Defs

@[expose] public section

namespace Clean2

/-! ## The arithmetic of the challenge field -/

namespace KArith
variable {F K : Type} [Field F] [Field K] [Algebra F K]

inductive Name (F K : Type) where
  | embed | add | sub | mul | smul | inv | assertZero
  | const (c : K)

variable (kty : CType F K)

@[reducible] def embed : Interface F where
  input := F
  inputCType := .native
  output := K
  outputCType := kty
  Spec v x := x = algebraMap F K v

@[reducible] def add : Interface F where
  input := K × K
  inputCType := kty ×ᵗ kty
  output := K
  outputCType := kty
  Spec x c := c = x.1 + x.2

@[reducible] def sub : Interface F where
  input := K × K
  inputCType := kty ×ᵗ kty
  output := K
  outputCType := kty
  Spec x c := c = x.1 - x.2

@[reducible] def mul : Interface F where
  input := K × K
  inputCType := kty ×ᵗ kty
  output := K
  outputCType := kty
  Spec x c := c = x.1 * x.2

/-- Scale by a native value. -/
@[reducible] def smul : Interface F where
  input := F × K
  inputCType := .native ×ᵗ kty
  output := K
  outputCType := kty
  Spec x c := c = algebraMap F K x.1 * x.2

@[reducible] def inv : Interface F where
  input := K
  inputCType := kty
  output := K
  outputCType := kty
  Spec x y := x ≠ 0 ∧ y = x⁻¹
  ProverAssumptions x := x ≠ 0
  ProverSpec x y := y = x⁻¹

@[reducible] def assertZero : Interface F where
  input := K
  inputCType := kty
  output := Unit
  outputCType := .unit
  Spec x _ := x = 0
  ProverAssumptions x := x = 0

@[reducible] def const (c : K) : Interface F where
  input := Unit
  inputCType := .unit
  output := K
  outputCType := kty
  Spec _ x := x = c

/-- The arithmetic of `K`, laid out by `kty`, by name. -/
@[reducible]
def interface : Name F K → Interface F
  | .embed => embed kty
  | .add => add kty
  | .sub => sub kty
  | .mul => mul kty
  | .smul => smul kty
  | .inv => inv kty
  | .assertZero => assertZero kty
  | .const c => const kty c

attribute [circuit_norm] interface

/-! ### `K = F`: the arithmetic of the native field -/

section Native
variable {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) (inverse : Impl B Inverse.interface)

local notation "nat" => (CType.native : CType B.Native B.Native)

def nativeEmbed : Impl B (embed nat) where
  main v := pure v
  soundness := by intro s env v _ _; simp [circuit_norm]
  completeness := by intro s env v _ _; simp [circuit_norm]

def nativeAdd : Impl B (add nat) where
  main x := arith .add x
  soundness := by intro s env (a, b) _ h; simp_all [circuit_norm]
  completeness := by intro s env (a, b) _ _; simp [circuit_norm]

def nativeSub : Impl B (sub nat) where
  main x := arith .sub x
  soundness := by intro s env (a, b) _ h; simp_all [circuit_norm]
  completeness := by intro s env (a, b) _ _; simp [circuit_norm]

def nativeMul : Impl B (mul nat) where
  main x := arith .mul x
  soundness := by intro s env (a, b) _ h; simp_all [circuit_norm]
  completeness := by intro s env (a, b) _ _; simp [circuit_norm]

def nativeSmul : Impl B (smul nat) where
  main x := arith .mul x
  soundness := by intro s env (a, b) _ h; simp_all [circuit_norm]
  completeness := by intro s env (a, b) _ _; simp [circuit_norm]

def nativeInv : Impl B (inv nat) where
  main x := inverse x
  soundness := by intro s env x _ h; simp_all [circuit_norm]
  completeness := by intro s env x h h_prover; simp_all [circuit_norm]

def nativeAssertZero : Impl B (assertZero nat) where
  main x := arith .assertZero x
  soundness := by intro s env x _ h; simp_all [circuit_norm]
  completeness := by intro s env x _ h; simp_all [circuit_norm]

def nativeConst (c : B.Native) : Impl B (const nat c) where
  main _ := arith (.const c) ()
  soundness := by intro s env _ _ h; simp_all [circuit_norm]
  completeness := by intro s env _ _ _; simp [circuit_norm]

/-- The arithmetic of the native field, as a challenge field. -/
def native : ∀ n, Impl B (interface nat n)
  | .embed => nativeEmbed
  | .add => nativeAdd arith
  | .sub => nativeSub arith
  | .mul => nativeMul arith
  | .smul => nativeSmul arith
  | .inv => nativeInv inverse
  | .assertZero => nativeAssertZero arith
  | .const c => nativeConst arith c

end Native

end KArith

end Clean2
