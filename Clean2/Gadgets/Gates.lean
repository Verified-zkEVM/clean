/-
Boolean gates: the smallest interesting family of functionalities, and the first place where
gadgets are built on *gadgets* rather than on arithmetic.

Two tiers:
- `NOT`, `AND`, `OR` are implemented directly over `Arith.sig`;
- `NAND`, `NOR` are implemented over `NOT.iface` and `AND.iface`/`OR.iface`. Their proofs never
  look at a circuit: they only compose the specs of the gates they call.

A gate's spec says what the output *means*: it is a boolean, and it is true exactly when the
corresponding proposition about the inputs holds. The field encoding (`1 - x`, `a * b`, ...)
is implementation, and never appears in an interface.
-/
module

public import Clean2.Gadgets.Bool

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

namespace Gates

/-! ## `NOT`: `out = 1 - x` -/

namespace NOT

abbrev iface : Interface F field field where
  Assumptions x := IsBool x
  Spec x out := IsBool out ∧ (out = 1 ↔ x ≠ 1)

attribute [circuit_norm] iface

def viaArith {B : Backend F} (arith : Sig.Impl B Arith.sig) : Impl B iface where
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

abbrev iface : Interface F fieldPair field where
  Assumptions | (a, b) => IsBool a ∧ IsBool b
  Spec | (a, b), c => IsBool c ∧ (c = 1 ↔ a = 1 ∧ b = 1)

attribute [circuit_norm] iface

def viaArith {B : Backend F} (arith : Sig.Impl B Arith.sig) : Impl B iface where
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

abbrev iface : Interface F fieldPair field where
  Assumptions | (a, b) => IsBool a ∧ IsBool b
  Spec | (a, b), c => IsBool c ∧ (c = 1 ↔ a = 1 ∨ b = 1)

attribute [circuit_norm] iface

def viaArith {B : Backend F} (arith : Sig.Impl B Arith.sig) : Impl B iface where
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

abbrev iface : Interface F fieldPair field where
  Assumptions | (a, b) => IsBool a ∧ IsBool b
  Spec | (a, b), c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ∧ b = 1))

attribute [circuit_norm] iface

def viaGates {B : Backend F} (and : Impl B AND.iface) (not : Impl B NOT.iface) : Impl B iface where
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

abbrev iface : Interface F fieldPair field where
  Assumptions | (a, b) => IsBool a ∧ IsBool b
  Spec | (a, b), c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ∨ b = 1))

attribute [circuit_norm] iface

def viaGates {B : Backend F} (or : Impl B OR.iface) (not : Impl B NOT.iface) : Impl B iface where
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

def notExpr : Impl (ExprBackend F) NOT.iface := NOT.viaArith ExprBackend.arith
def andExpr : Impl (ExprBackend F) AND.iface := AND.viaArith ExprBackend.arith
def orExpr : Impl (ExprBackend F) OR.iface := OR.viaArith ExprBackend.arith
def nandExpr : Impl (ExprBackend F) NAND.iface := NAND.viaGates andExpr notExpr
def norExpr : Impl (ExprBackend F) NOR.iface := NOR.viaGates orExpr notExpr

def notR1CS : Impl (R1CS F) NOT.iface := NOT.viaArith R1CS.arith
def andR1CS : Impl (R1CS F) AND.iface := AND.viaArith R1CS.arith
def orR1CS : Impl (R1CS F) OR.iface := OR.viaArith R1CS.arith
def nandR1CS : Impl (R1CS F) NAND.iface := NAND.viaGates andR1CS notR1CS
def norR1CS : Impl (R1CS F) NOR.iface := NOR.viaGates orR1CS notR1CS

/-! The same gadget, two arithmetizations. On the expression backend every gate is free except
for the constants; on R1CS each multiplication costs one cell and one constraint, and the linear
parts are folded into the linear combinations. -/

example (x : Expr F) (s : ℕ) : (notExpr (F := F)).advance x s = s := rfl
example (a b : Expr F) (s : ℕ) : (andExpr (F := F)).advance (a, b) s = s := rfl
example (a b : Expr F) (s : ℕ) : (nandExpr (F := F)).advance (a, b) s = s := rfl

example (x : LinComb F) (s : ℕ) : (notR1CS (F := F)).advance x s = s := rfl
example (a b : LinComb F) (s : ℕ) : (andR1CS (F := F)).advance (a, b) s = s + 1 := rfl
example (a b : LinComb F) (s : ℕ) : (norR1CS (F := F)).advance (a, b) s = s + 1 := rfl

/-- `NOT` is pure linear algebra: on R1CS it emits no constraint at all. -/
example (x : LinComb F) (s : ℕ) : ((notR1CS (F := F)).main x |>.operations s).toFlat = [] := rfl

/-- `NAND` on R1CS: one product cell, one constraint; the negation is free. -/
example (a b : LinComb F) (s : ℕ) :
    ((nandR1CS (F := F)).main (a, b) |>.operations s).toFlat =
      [.witness 2 #v[a, b] (fun v => v[0] * v[1]), .constraint a b (.cell s)] := rfl

end
end Clean2
