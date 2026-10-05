/-
Equality: the assertion `a = b`, and the predicate `a =? b`.

`IsEqual` is the first gadget whose implementation is parametrized by a *witnessing* gadget:
it subtracts and hands the difference to `IsZero`. Its proof uses `IsZero.interface` and nothing
else — in particular it never learns that `IsZero` witnesses an inverse.
-/
module

public import Clean2.Gadgets.IsZero

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

/-! ## `assertEq`: an assertion, so the honest prover has to make it true -/

namespace AssertEq

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Unit
  outputCType := .unit
  Spec := fun (a, b) _ => a = b
  ProverAssumptions := fun (a, b) => a = b

def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
  main | (a, b) => do
    let d ← arith .sub (a, b)
    arith .assertZero d
  soundness := by
    intro s env (a, b) _ h
    simp only [circuit_norm] at h ⊢
    -- `d = a - b` and `d = 0`
    obtain ⟨h_sub, h_zero⟩ := h
    rw [h_sub] at h_zero
    exact sub_eq_zero.mp h_zero
  completeness := by
    intro s env (a, b) h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    -- the honest prover has `a = b`, so the difference the `sub` child returns is zero
    rw [h, h_prover, sub_self]

end AssertEq

/-! ## `isEqual`: `out = 1` if `a = b`, and `out = 0` otherwise -/

namespace IsEqual

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Spec := fun (a, b) out => (a = b → out = 1) ∧ (a ≠ b → out = 0)

/-- Generic over the arithmetic *and* over the zero test. -/
def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) (isZero : Impl B IsZero.interface) :
    Impl B interface where
  main | (a, b) => do
    let d ← arith .sub (a, b)
    isZero d
  soundness := by
    intro s env (a, b) _ h
    simp only [circuit_norm] at h ⊢
    -- `d = a - b`, plus the two halves of `IsZero.interface.Spec d out`
    obtain ⟨h_sub, h_one, h_zero⟩ := h
    rw [h_sub, sub_eq_zero] at h_one
    rw [h_sub, sub_ne_zero] at h_zero
    exact ⟨h_one, h_zero⟩
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end IsEqual

end Clean2
