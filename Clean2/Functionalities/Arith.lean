/-
The basic functionalities: arithmetic on variables, constants, assertions, witnesses.

None of these is primitive. Each is an interface; `Arith.interface` collects them into one
vocabulary, indexed by names. A backend implements the ones it can implement natively
(`Base.interface` is what R1CS has), and `Arith.ofBase` derives the rest.
-/
module

public import Clean2.Core
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Clean2
variable {Native : Type}

/-! ## The interfaces -/

namespace Add
@[reducible]
def interface [Add Native] : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Spec := fun (a, b) c => c = a + b
end Add

namespace Sub
@[reducible]
def interface [Sub Native] : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Spec := fun (a, b) c => c = a - b
end Sub

namespace Mul
@[reducible]
def interface [Mul Native] : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Spec := fun (a, b) c => c = a * b
end Mul

/- Multiplication by a constant. The constant is a parameter: one implementation produces
them all. Linear, so free on the backends whose variables are linear combinations. -/
namespace Scale
@[reducible]
def interface [Mul Native] (c : Native) : Interface Native where
  input := Native
  inputCType := .native
  output := Native
  outputCType := .native
  Spec := fun x y => y = c * x
end Scale

/- A constant. The constant is a parameter: one implementation produces them all. -/
namespace Const
@[reducible]
def interface (c : Native) : Interface Native where
  input := Unit
  inputCType := .unit
  output := Native
  outputCType := .native
  Spec := fun _ x => x = c
end Const

/- Assert that a variable is zero. An assertion: the honest prover has to make it true. -/
namespace AssertZero
@[reducible]
def interface [Zero Native] : Interface Native where
  input := Native
  inputCType := .native
  output := Unit
  outputCType := .unit
  Spec := fun x _ => x = 0
  ProverAssumptions := fun x => x = 0
end AssertZero

/- Assert `a * b = c`. Included as its own functionality because it is the native
constraint of R1CS; a backend that decomposed it into `mul` and `assertZero` would pay
an extra cell. -/
namespace MulEq
@[reducible]
def interface [Mul Native] : Interface Native where
  input := Native × Native × Native
  inputCType := .nativeTriple
  output := Unit
  outputCType := .unit
  Spec := fun (a, b, c) _ => a * b = c
  ProverAssumptions := fun (a, b, c) => a * b = c
end MulEq

/- An unconstrained value, which the honest prover computes from the input values.
Nothing is known about it for soundness; for completeness, its value is known.
The computation, together with the shape of its input, is the parameter. -/
namespace Witness

structure Params (Native : Type) : Type 1 where
  Input : TypeMap
  [inst : ProvableType Input]
  f : Input Native → Native

attribute [instance] Params.inst

@[reducible]
def interface (p : Params Native) : Interface Native where
  input := p.Input Native
  inputCType := .ofProvable p.Input
  output := Native
  outputCType := .native
  ProverSpec := fun x out => out = p.f x

end Witness

/-! ## The vocabulary -/

namespace Arith

inductive Name (Native : Type) : Type 1 where
  | add | sub | mul
  | scale (c : Native)
  | const (c : Native)
  | mulEq | assertZero
  | witness (Input : TypeMap) [ProvableType Input] (f : Input Native → Native)

/-- All the arithmetic functionalities, by name. -/
@[reducible]
def interface [Add Native] [Sub Native] [Mul Native] [Zero Native] : Name Native → Interface Native
  | .add => Add.interface
  | .sub => Sub.interface
  | .mul => Mul.interface
  | .scale c => Scale.interface c
  | .const c => Const.interface c
  | .mulEq => MulEq.interface
  | .assertZero => AssertZero.interface
  | @Name.witness _ Input inst f => letI := inst; Witness.interface ⟨Input, f⟩

attribute [circuit_norm] interface

end Arith

namespace Base

inductive Name (Native : Type) : Type 1 where
  | add | sub
  | scale (c : Native)
  | const (c : Native)
  | mulEq
  | witness (Input : TypeMap) [ProvableType Input] (f : Input Native → Native)

def Name.toArith : Name Native → Arith.Name Native
  | .add => .add
  | .sub => .sub
  | .scale c => .scale c
  | .const c => .const c
  | .mulEq => .mulEq
  | @Name.witness _ Input inst f => letI := inst; .witness Input f

/-- The native set of an R1CS-like backend: linear arithmetic, `a * b = c`, and witnesses.
A sub-family of `Arith.interface`. -/
@[reducible]
def interface [Add Native] [Sub Native] [Mul Native] [Zero Native] (n : Name Native) : Interface Native :=
  Arith.interface n.toArith

end Base

/-! ## Lowering: the full arithmetic vocabulary from the base one -/

namespace Mul

/-- `c ← witness (a * b); assert a * b = c`. This is how R1CS multiplies. The witness
implementation is generic in the computation; the computation is chosen here. -/
def ofWitnessMulEq {B : Backend} [Field B.Native]
    (witness : ∀ p, Impl B (Witness.interface p)) (mulEq : Impl B MulEq.interface) : Impl B Mul.interface where
  main | (a, b) => do
    let c ← witness ⟨nativePair, fun (a, b) => a * b⟩ (a, b)
    mulEq (a, b, c)
    return c
  soundness := by
    intro s env (a, b) _ h
    simp only [circuit_norm] at h ⊢
    exact h.symm
  completeness := by
    intro s env (a, b) h _
    simp only [circuit_norm] at h ⊢
    exact h.symm

/-- Its measure: a witness and a `mulEq`. -/
instance measured_ofWitnessMulEq {B : Backend} [Field B.Native] {M : Type} [AddCommMonoid M] (μ : B.Measure M)
    (witness : ∀ p, Impl B (Witness.interface p)) (mulEq : Impl B MulEq.interface)
    [∀ p, Impl.Measured μ (witness p)] [Impl.Measured μ mulEq] :
    Impl.Measured μ (ofWitnessMulEq witness mulEq) where
  value := μ.of (witness ⟨nativePair, fun (a, b) => a * b⟩) + μ.of mulEq
  value_eq := by measure [ofWitnessMulEq]

end Mul

namespace AssertZero

/-- `x * 1 = 0`. -/
def ofMulEq {B : Backend} [Field B.Native] (const : ∀ c, Impl B (Const.interface c)) (mulEq : Impl B MulEq.interface) :
    Impl B AssertZero.interface where
  main x := do
    let one ← const 1 ()
    let zero ← const 0 ()
    mulEq (x, one, zero)
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨hone, hzero, h⟩ := h
    rw [hone, hzero, mul_one] at h
    exact h
  completeness := by
    intro s env x h hx
    simp only [circuit_norm] at h hx ⊢
    simp_all

/-- Its measure: two constants and a `mulEq`. -/
instance measured_ofMulEq {B : Backend} [Field B.Native] {M : Type} [AddCommMonoid M] (μ : B.Measure M)
    (const : ∀ c, Impl B (Const.interface c)) (mulEq : Impl B MulEq.interface)
    [∀ c, Impl.Measured μ (const c)] [Impl.Measured μ mulEq] :
    Impl.Measured μ (ofMulEq const mulEq) where
  value := μ.of (const 1) + μ.of (const 0) + μ.of mulEq
  value_eq := by measure [ofMulEq]

end AssertZero

namespace Arith

/-- A backend that provides `Base.interface` provides all of `Arith.interface`. -/
def ofBase {B : Backend} [Field B.Native] (base : ∀ n, Impl B (Base.interface n)) : ∀ n, Impl B (Arith.interface n)
  | .add => base .add
  | .sub => base .sub
  | .scale c => base (.scale c)
  | .const c => base (.const c)
  | .mulEq => base .mulEq
  | @Arith.Name.witness _ Input inst f => letI := inst; base (.witness Input f)
  | .mul => Mul.ofWitnessMulEq (fun p => base (.witness p.Input p.f)) (base .mulEq)
  | .assertZero => AssertZero.ofMulEq (fun c => base (.const c)) (base .mulEq)

/-- The measure of the derived vocabulary, from that of the base one. The derived cases are
spelled out: `Base.interface (.witness ..)` is `Witness.interface _` only after unfolding
`Base.Name.toArith`, which instance resolution does not do. -/
instance measured_ofBase {B : Backend} [Field B.Native] {M : Type} [AddCommMonoid M] (μ : B.Measure M)
    (base : ∀ n, Impl B (Base.interface n)) [inst : ∀ n, Impl.Measured μ (base n)] :
    ∀ n, Impl.Measured μ (ofBase base n)
  | .add => inst .add
  | .sub => inst .sub
  | .scale c => inst (.scale c)
  | .const c => inst (.const c)
  | .mulEq => inst .mulEq
  | @Arith.Name.witness _ Input _ f => inst (.witness Input f)
  | .mul => @Mul.measured_ofWitnessMulEq B _ M _ μ (fun p => base (.witness p.Input p.f)) (base .mulEq)
      (fun p => inst (.witness p.Input p.f)) (inst .mulEq)
  | .assertZero => @AssertZero.measured_ofMulEq B _ M _ μ (fun c => base (.const c)) (base .mulEq)
      (fun c => inst (.const c)) (inst .mulEq)

end Arith

end Clean2
