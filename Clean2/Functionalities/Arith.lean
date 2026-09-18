/-
The basic functionalities: arithmetic on variables, constants, assertions, witnesses.

None of these is primitive. Each is an interface; `Arith.sig` collects them into a signature.
A backend implements the ones it can implement natively (`Base.sig` is what R1CS has), and
`Arith.ofBase` derives the rest.
-/
module

public import Clean2.Core
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

/-! ## The interfaces -/

namespace Add
abbrev iface : Interface F fieldPair field where
  Spec | (a, b), c => c = a + b
end Add

namespace Sub
abbrev iface : Interface F fieldPair field where
  Spec | (a, b), c => c = a - b
end Sub

namespace Mul
abbrev iface : Interface F fieldPair field where
  Spec | (a, b), c => c = a * b
end Mul

namespace Const
abbrev iface (c : F) : Interface F unit field where
  Spec _ x := x = c
end Const

/- Assert that a variable is zero. An assertion: the honest prover has to make it true. -/
namespace AssertZero
abbrev iface : Interface F field unit where
  Spec x _ := x = 0
  ProverAssumptions x := x = 0
end AssertZero

/- Assert `a * b = c`. Included as its own functionality because it is the native
constraint of R1CS; a backend that decomposed it into `mul` and `assertZero` would pay
an extra cell. -/
namespace MulEq
abbrev iface : Interface F fieldTriple unit where
  Spec | (a, b, c), _ => a * b = c
  ProverAssumptions | (a, b, c) => a * b = c
end MulEq

/- An unconstrained value, which the honest prover computes from the input values.
Nothing is known about it for soundness; for completeness, its value is known. -/
namespace Witness
abbrev iface {Input : TypeMap} (f : Input F → F) : Interface F Input field where
  ProverSpec x out := out = f x
end Witness

-- interfaces are reducible and part of the simp set: unfolding them inside the type of an
-- `Impl` must keep terms well-typed at reducible transparency
attribute [circuit_norm] Add.iface Sub.iface Mul.iface Const.iface AssertZero.iface MulEq.iface
  Witness.iface

/-! ## The signatures -/

namespace Arith

inductive Name (F : Type) : Type 1 where
  | add | sub | mul
  | const (c : F)
  | mulEq | assertZero
  | witness (Input : TypeMap) [ProvableType Input] (f : Input F → F)

/-- All the arithmetic functionalities. -/
abbrev sig : Sig.{1} F where
  Name := Name F
  method
    | .add => Add.iface.toMethod
    | .sub => Sub.iface.toMethod
    | .mul => Mul.iface.toMethod
    | .const c => (Const.iface c).toMethod
    | .mulEq => MulEq.iface.toMethod
    | .assertZero => AssertZero.iface.toMethod
    | @Name.witness _ _Input inst f => letI := inst; (Witness.iface f).toMethod

attribute [circuit_norm] sig

end Arith

namespace Base

inductive Name (F : Type) : Type 1 where
  | add | sub
  | const (c : F)
  | mulEq
  | witness (Input : TypeMap) [ProvableType Input] (f : Input F → F)

def Name.toArith : Name F → Arith.Name F
  | .add => .add
  | .sub => .sub
  | .const c => .const c
  | .mulEq => .mulEq
  | @Name.witness _ Input inst f => letI := inst; .witness Input f

/-- The native set of an R1CS-like backend: linear arithmetic, `a * b = c`, and witnesses.
A sub-signature of `Arith.sig`. -/
abbrev sig : Sig.{1} F := Arith.sig.restrict Name.toArith

end Base

/-! ## Lowering: the full arithmetic signature from the base one -/

namespace Mul

/-- `c ← witness (a * b); assert a * b = c`. This is how R1CS multiplies. -/
def viaWitnessMulEq {B : Backend F}
    (witness : Impl B (Witness.iface fun (p : fieldPair F) => p.1 * p.2))
    (mulEq : Impl B MulEq.iface) : Impl B Mul.iface where
  main | (a, b) => do
    let c ← witness (a, b)
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

end Mul

namespace AssertZero

/-- `x * 1 = 0`. -/
def viaMulEq {B : Backend F} (const : (c : F) → Impl B (Const.iface c)) (mulEq : Impl B MulEq.iface) :
    Impl B AssertZero.iface where
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

end AssertZero

namespace Arith

/-- A backend that provides `Base.sig` provides all of `Arith.sig`. -/
def ofBase {B : Backend F} (base : Sig.Impl B Base.sig) : Sig.Impl B Arith.sig
  | .add => base .add
  | .sub => base .sub
  | .const c => base (.const c)
  | .mulEq => base .mulEq
  | @Arith.Name.witness _ Input inst f => letI := inst; base (.witness Input f)
  | .mul => Mul.viaWitnessMulEq (base (.witness fieldPair fun p => p.1 * p.2)) (base .mulEq)
  | .assertZero => AssertZero.viaMulEq (fun c => base (.const c)) (base .mulEq)

end Arith

end Clean2
