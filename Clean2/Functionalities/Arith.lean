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
abbrev interface [Add Native] : Interface Native Unit := fun _ =>
  { Input := nativePair, Output := native
    Spec := fun (a, b) c => c = a + b }
end Add

namespace Sub
abbrev interface [Sub Native] : Interface Native Unit := fun _ =>
  { Input := nativePair, Output := native
    Spec := fun (a, b) c => c = a - b }
end Sub

namespace Mul
abbrev interface [Mul Native] : Interface Native Unit := fun _ =>
  { Input := nativePair, Output := native
    Spec := fun (a, b) c => c = a * b }
end Mul

/- A constant. The constant is a parameter: one implementation produces them all. -/
namespace Const
abbrev interface : Interface Native Native := fun c =>
  { Input := unit, Output := native
    Spec := fun _ x => x = c }
end Const

/- Assert that a variable is zero. An assertion: the honest prover has to make it true. -/
namespace AssertZero
abbrev interface [Zero Native] : Interface Native Unit := fun _ =>
  { Input := native, Output := unit
    Spec := fun x _ => x = 0
    ProverAssumptions := fun x => x = 0 }
end AssertZero

/- Assert `a * b = c`. Included as its own functionality because it is the native
constraint of R1CS; a backend that decomposed it into `mul` and `assertZero` would pay
an extra cell. -/
namespace MulEq
abbrev interface [Mul Native] : Interface Native Unit := fun _ =>
  { Input := nativeTriple, Output := unit
    Spec := fun (a, b, c) _ => a * b = c
    ProverAssumptions := fun (a, b, c) => a * b = c }
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

abbrev interface : Interface Native (Params Native) := fun p =>
  { Input := p.Input, Output := native
    ProverSpec := fun x out => out = p.f x }

end Witness

/-! ## The vocabulary -/

namespace Arith

inductive Name (Native : Type) : Type 1 where
  | add | sub | mul
  | const (c : Native)
  | mulEq | assertZero
  | witness (Input : TypeMap) [ProvableType Input] (f : Input Native → Native)

/-- All the arithmetic functionalities, by name. -/
abbrev interface [Add Native] [Sub Native] [Mul Native] [Zero Native] : Interface Native (Name Native)
  | .add => Add.interface ()
  | .sub => Sub.interface ()
  | .mul => Mul.interface ()
  | .const c => Const.interface c
  | .mulEq => MulEq.interface ()
  | .assertZero => AssertZero.interface ()
  | @Name.witness _ Input inst f => letI := inst; Witness.interface ⟨Input, f⟩

attribute [circuit_norm] interface

end Arith

namespace Base

inductive Name (Native : Type) : Type 1 where
  | add | sub
  | const (c : Native)
  | mulEq
  | witness (Input : TypeMap) [ProvableType Input] (f : Input Native → Native)

def Name.toArith : Name Native → Arith.Name Native
  | .add => .add
  | .sub => .sub
  | .const c => .const c
  | .mulEq => .mulEq
  | @Name.witness _ Input inst f => letI := inst; .witness Input f

/-- The native set of an R1CS-like backend: linear arithmetic, `a * b = c`, and witnesses.
A sub-interface of `Arith.interface`. -/
abbrev interface [Add Native] [Sub Native] [Mul Native] [Zero Native] : Interface Native (Name Native) :=
  Arith.interface.restrict Name.toArith

end Base

/-! ## Lowering: the full arithmetic vocabulary from the base one -/

namespace Mul

/-- `c ← witness (a * b); assert a * b = c`. This is how R1CS multiplies. The witness
implementation is generic in the computation; the computation is chosen here. -/
def ofWitnessMulEq {B : Backend} [Field B.Native]
    (witness : Impl B Witness.interface) (mulEq : Impl B MulEq.interface) : Impl B Mul.interface where
  main | _, (a, b) => do
    let c ← witness ⟨nativePair, fun (a, b) => a * b⟩ (a, b)
    mulEq (a, b, c)
    return c
  soundness := by
    intro _ s env (a, b) _ h
    simp only [circuit_norm] at h ⊢
    exact h.symm
  completeness := by
    intro _ s env (a, b) h _
    simp only [circuit_norm] at h ⊢
    exact h.symm

end Mul

namespace AssertZero

/-- `x * 1 = 0`. -/
def ofMulEq {B : Backend} [Field B.Native] (const : Impl B Const.interface) (mulEq : Impl B MulEq.interface) :
    Impl B AssertZero.interface where
  main _ x := do
    let one ← const 1
    let zero ← const 0
    mulEq (x, one, zero)
  soundness := by
    intro _ s env x _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨hone, hzero, h⟩ := h
    rw [hone, hzero, mul_one] at h
    exact h
  completeness := by
    intro _ s env x h hx
    simp only [circuit_norm] at h hx ⊢
    simp_all

end AssertZero

namespace Arith

/-- A backend that provides `Base.interface` provides all of `Arith.interface`. -/
def ofBase {B : Backend} [Field B.Native] (base : Impl B Base.interface) : Impl B Arith.interface :=
  Impl.ofFun fun
  | .add => base.fix .add
  | .sub => base.fix .sub
  | .const c => base.fix (.const c)
  | .mulEq => base.fix .mulEq
  | @Arith.Name.witness _ Input inst f => letI := inst; base.fix (.witness Input f)
  | .mul => Mul.ofWitnessMulEq (base.restrict fun (p : Witness.Params B.Native) => .witness p.Input p.f) (base.fix .mulEq)
  | .assertZero => AssertZero.ofMulEq (base.restrict .const) (base.fix .mulEq)

end Arith

end Clean2
