/-
Equality: the assertion `a = b`, and the predicate `a =? b`.

`IsEqual` is the first gadget whose implementation is parametrized by a *witnessing* gadget:
it subtracts and hands the difference to `IsZero`. Its proof uses `IsZero.iface` and nothing
else — in particular it never learns that `IsZero` witnesses an inverse.
-/
module

public import Clean2.Gadgets.IsZero

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

/-! ## `assertEq`: an assertion, so the honest prover has to make it true -/

namespace AssertEq

abbrev iface : Interface F fieldPair unit where
  Spec | (a, b), _ => a = b
  ProverAssumptions | (a, b) => a = b

attribute [circuit_norm] iface

def viaArith {B : Backend F} (arith : Sig.Impl B Arith.sig) : Impl B iface where
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

abbrev iface : Interface F fieldPair field where
  Spec | (a, b), out => (a = b → out = 1) ∧ (a ≠ b → out = 0)

attribute [circuit_norm] iface

/-- Generic over the arithmetic *and* over the zero test. -/
def viaIsZero {B : Backend F} (arith : Sig.Impl B Arith.sig) (isZero : Impl B IsZero.iface) :
    Impl B iface where
  main | (a, b) => do
    let d ← arith .sub (a, b)
    isZero d
  soundness := by
    intro s env (a, b) _ h
    simp only [circuit_norm] at h ⊢
    -- `d = a - b`, plus the two halves of `IsZero.iface.Spec d out`
    obtain ⟨h_sub, h_one, h_zero⟩ := h
    rw [h_sub, sub_eq_zero] at h_one
    rw [h_sub, sub_ne_zero] at h_zero
    exact ⟨h_one, h_zero⟩
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end IsEqual

/-! ## On both backends -/

def assertEqExpr : Impl (ExprBackend F) AssertEq.iface := AssertEq.viaArith ExprBackend.arith
def assertEqR1CS : Impl (R1CS F) AssertEq.iface := AssertEq.viaArith R1CS.arith

def isEqualExpr : Impl (ExprBackend F) IsEqual.iface := IsEqual.viaIsZero ExprBackend.arith isZeroExpr
def isEqualR1CS : Impl (R1CS F) IsEqual.iface := IsEqual.viaIsZero R1CS.arith isZeroR1CS

/-- Asserting an equality allocates nothing on either backend. -/
example (a b : Expr F) (s : ℕ) : (assertEqExpr (F := F)).advance (a, b) s = s := rfl
example (a b : LinComb F) (s : ℕ) : (assertEqR1CS (F := F)).advance (a, b) s = s := rfl

/-- On R1CS, `assertZero` is not native: it is lowered to `(a - b) * 1 = 0`. -/
example (a b : LinComb F) (s : ℕ) :
    ((assertEqR1CS (F := F)).main (a, b) |>.operations s).toFlat =
      [.constraint (a - b) (.ofConst 1) (.ofConst 0)] := rfl

/-- `isEqual` costs exactly what `isZero` costs. -/
example (a b : LinComb F) (s : ℕ) : (isEqualR1CS (F := F)).advance (a, b) s = s + 2 := rfl
example (a b : Expr F) (s : ℕ) : (isEqualExpr (F := F)).advance (a, b) s = s + 1 := rfl

end Clean2
