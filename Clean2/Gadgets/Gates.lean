/-
Boolean gates: the smallest interesting family of functionalities, and the first place where
gadgets are built on *gadgets* rather than on arithmetic.

Two tiers:
- `NOT`, `AND`, `OR` are implemented directly over `Arith.interface`;
- `NAND`, `NOR` are implemented over `NOT.interface` and `AND.interface`/`OR.interface`. Their proofs never
  look at a circuit: they only compose the specs of the gates they call.

A gate's spec says what the output *means*: it is a boolean, and it is true exactly when the
corresponding proposition about the inputs holds. The field encoding (`1 - x`, `a * b`, ...)
is implementation, and never appears in an interface.
-/
module

public import Clean2.Gadgets.Bool

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

namespace Gates

/-! ## `NOT`: `out = 1 - x` -/

namespace NOT

abbrev interface : Interface Native :=
  { input := Native, inputCType := .native,
    output := Native, outputCType := .native
    Assumptions := fun x => IsBool x
    Spec := fun x out => IsBool out ∧ (out = 1 ↔ x ≠ 1) }

def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
  main x := do
    let one ← arith (.const 1) ()
    arith .sub (one, x)
  soundness := by
    intro s env x hx h
    simp only [circuit_norm, IsBool] at hx h ⊢
    obtain ⟨hone, hout⟩ := h
    rw [hout, hone]
    rcases hx with hx | hx <;> simp [hx]
  completeness := by
    intro s env x _ _
    simp only [circuit_norm]

end NOT

/-! ## `AND`: `out = a * b` -/

namespace AND

abbrev interface : Interface Native :=
  { input := Native × Native, inputCType := .nativePair,
    output := Native, outputCType := .native
    Assumptions := fun (a, b) => IsBool a ∧ IsBool b
    Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ a = 1 ∧ b = 1) }

def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
  main | (a, b) => arith .mul (a, b)
  soundness := by
    intro s env (a, b) h_as h
    simp only [circuit_norm, IsBool] at h_as h ⊢
    obtain ⟨ha, hb⟩ := h_as
    rw [h]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end AND

/-! ## `OR`: `out = a + b - a * b` -/

namespace OR

abbrev interface : Interface Native :=
  { input := Native × Native, inputCType := .nativePair,
    output := Native, outputCType := .native
    Assumptions := fun (a, b) => IsBool a ∧ IsBool b
    Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ a = 1 ∨ b = 1) }

def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
  main | (a, b) => do
    let ab ← arith .mul (a, b)
    let sum ← arith .add (a, b)
    arith .sub (sum, ab)
  soundness := by
    intro s env (a, b) h_as h
    simp only [circuit_norm, IsBool] at h_as h ⊢
    obtain ⟨ha, hb⟩ := h_as
    obtain ⟨hab, hsum, hout⟩ := h
    rw [hout, hsum, hab]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end OR

/-! ## `NAND` and `NOR`: gates built out of gates.

Both implementations are parametrized by the gates they use, and both proofs are pure spec
composition — the circuits of `and`, `or`, `not` are never unfolded. -/

namespace NAND

abbrev interface : Interface Native :=
  { input := Native × Native, inputCType := .nativePair,
    output := Native, outputCType := .native
    Assumptions := fun (a, b) => IsBool a ∧ IsBool b
    Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ∧ b = 1)) }

def impl {B : Backend} [Field B.Native] (and : Impl B AND.interface) (not : Impl B NOT.interface) : Impl B interface where
  main | (a, b) => do
    let ab ← and (a, b)
    not ab
  soundness := by
    intro s env (a, b) h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨h_and, h_not⟩ := h
    obtain ⟨h_bool, h_iff⟩ := h_and h_as
    obtain ⟨h_bool', h_iff'⟩ := h_not h_bool
    exact ⟨h_bool', by rw [h_iff']; simp only [ne_eq, h_iff]⟩
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end NAND

namespace NOR

abbrev interface : Interface Native :=
  { input := Native × Native, inputCType := .nativePair,
    output := Native, outputCType := .native
    Assumptions := fun (a, b) => IsBool a ∧ IsBool b
    Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ∨ b = 1)) }

def impl {B : Backend} [Field B.Native] (or : Impl B OR.interface) (not : Impl B NOT.interface) : Impl B interface where
  main | (a, b) => do
    let ab ← or (a, b)
    not ab
  soundness := by
    intro s env (a, b) h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨h_or, h_not⟩ := h
    obtain ⟨h_bool, h_iff⟩ := h_or h_as
    obtain ⟨h_bool', h_iff'⟩ := h_not h_bool
    exact ⟨h_bool', by rw [h_iff']; simp only [ne_eq, h_iff]⟩
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end NOR
end Gates

/-! ## The whole family, on both backends. -/

section
open Gates

def notExpr : Impl (ExprBackend Native) NOT.interface := NOT.impl ExprBackend.arith
def andExpr : Impl (ExprBackend Native) AND.interface := AND.impl ExprBackend.arith
def orExpr : Impl (ExprBackend Native) OR.interface := OR.impl ExprBackend.arith
def nandExpr : Impl (ExprBackend Native) NAND.interface := NAND.impl andExpr notExpr
def norExpr : Impl (ExprBackend Native) NOR.interface := NOR.impl orExpr notExpr

def notR1CS : Impl (R1CS Native) NOT.interface := NOT.impl R1CS.arith
def andR1CS : Impl (R1CS Native) AND.interface := AND.impl R1CS.arith
def orR1CS : Impl (R1CS Native) OR.interface := OR.impl R1CS.arith
def nandR1CS : Impl (R1CS Native) NAND.interface := NAND.impl andR1CS notR1CS
def norR1CS : Impl (R1CS Native) NOR.interface := NOR.impl orR1CS notR1CS

/-! The same gadget, two arithmetizations. On the expression backend every gate is free except
for the constants; on R1CS each multiplication costs one cell and one constraint, and the linear
parts are folded into the linear combinations. -/

example (x : Expr Native) (s : ℕ) : (notExpr (Native := Native)).advance x s = s := rfl
example (a b : Expr Native) (s : ℕ) : (andExpr (Native := Native)).advance (a, b) s = s := rfl
example (a b : Expr Native) (s : ℕ) : (nandExpr (Native := Native)).advance (a, b) s = s := rfl

example (x : LinComb Native) (s : ℕ) : (notR1CS (Native := Native)).advance x s = s := rfl
example (a b : LinComb Native) (s : ℕ) : (andR1CS (Native := Native)).advance (a, b) s = s + 1 := rfl
example (a b : LinComb Native) (s : ℕ) : (norR1CS (Native := Native)).advance (a, b) s = s + 1 := rfl

/-- `NOT` is pure linear algebra: on R1CS it emits no constraint at all. -/
example (x : LinComb Native) (s : ℕ) : ((notR1CS (Native := Native)).main x |>.operations s).toFlat = [] := rfl

/-- `NAND` on R1CS: one product cell, one constraint; the negation is free. -/
example (a b : LinComb Native) (s : ℕ) :
    ((nandR1CS (Native := Native)).main (a, b) |>.operations s).toFlat =
      [.witness 2 #v[a, b] (fun v => v[0] * v[1]), .constraint a b (.cell s)] := rfl

end
end Clean2
