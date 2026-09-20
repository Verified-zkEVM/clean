/-
Gadgets: functionalities implemented on top of other functionalities, generically in the
backend. Instantiating them on a backend is function application.
-/
module

public import Clean2.Functionalities.Arith
public import Clean2.Backends.Expr
public import Clean2.Backends.R1CS
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

def IsBool (x : F) : Prop := x = 0 ∨ x = 1

/-! ## `assertBool`, implemented via `mulEq` -/

namespace AssertBool

def interface : Interface F field unit where
  Spec x _ := IsBool x
  ProverAssumptions x := IsBool x

/-- `x * x = x` forces `x ∈ {0, 1}`. -/
def impl {B : Backend} [Field B.Native] (mulEq : Impl B MulEq.interface) : Impl B interface where
  main x := mulEq (x, x, x)
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    simp only [circuit_norm, interface, MulEq.interface, IsBool] at h ⊢
    have h : (B.eval env x) * (B.eval env x - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  completeness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    simp only [circuit_norm, interface, MulEq.interface, IsBool] at h ⊢
    rcases h with h | h <;> simp [h]

end AssertBool

/-- The same gadget on two backends. -/
def assertBoolExpr : Impl (ExprBackend F) AssertBool.interface := AssertBool.impl ExprBackend.mulEq
def assertBoolR1CS : Impl (R1CS F) AssertBool.interface := AssertBool.impl R1CS.mulEq

/-- On R1CS, the fully resolved circuit is a single native constraint. -/
example (x : LinComb F) (s : ℕ) :
    ((assertBoolR1CS (F := F)).main x |>.operations s).toFlat = [.constraint x x x] := rfl

/-- On the expression backend, it is `x*x + (-1)*x = 0`. -/
example (x : Expr F) (s : ℕ) :
    ((assertBoolExpr (F := F)).main x |>.operations s).toFlat =
      [.assertZero (.add (.mul x x) (.mul (.const (-1)) x))] := rfl

/-! ## `xor`, implemented via the arithmetic functionalities -/

namespace Xor

def interface : Interface F fieldPair field where
  Assumptions | (a, b) => IsBool a ∧ IsBool b
  Spec | (a, b), c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ↔ b = 1))

/-- `a ⊕ b = a + b - 2ab`. Generic over how arithmetic is done. -/
def impl {B : Backend} [Field B.Native] (arith : Sig.Impl B Arith.sig) : Impl B interface where
  main | (a, b) => do
    let t ← arith .mul (a, b)
    let s ← arith .add (a, b)
    let u ← arith .add (t, t)
    arith .sub (s, u)
  soundness := by
    intro s env (a, b) h_as h
    simp only [circuit_norm] at h_as h ⊢
    simp only [circuit_norm, interface, Add.interface, Sub.interface, Mul.interface, IsBool] at h_as h ⊢
    obtain ⟨ha, hb⟩ := h_as
    obtain ⟨ht, hs, hu, hc⟩ := h
    rw [hc, hu, hs, ht]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]
    simp only [circuit_norm, interface, Add.interface, Sub.interface, Mul.interface]

end Xor

def xorExpr : Impl (ExprBackend F) Xor.interface := Xor.impl ExprBackend.arith
def xorR1CS : Impl (R1CS F) Xor.interface := Xor.impl R1CS.arith

/-- On the expression backend, `xor` allocates nothing and emits nothing: it is an expression. -/
example (a b : Expr F) (s : ℕ) : (xorExpr (F := F)).advance (a, b) s = s := rfl
example (a b : Expr F) (s : ℕ) : ((xorExpr (F := F)).main (a, b) |>.operations s).toFlat = [] := rfl

/-- On R1CS it costs one cell (the product) and one constraint; the linear part is free. -/
example (a b : LinComb F) (s : ℕ) : (xorR1CS (F := F)).advance (a, b) s = s + 1 := rfl
example (a b : LinComb F) (s : ℕ) :
    ((xorR1CS (F := F)).main (a, b) |>.operations s).toFlat =
      [.witness 2 #v[a, b] (fun v => v[0] * v[1]), .constraint a b (.cell s)] := rfl

/-! ## Stacking: a gadget generic over gadget-level interfaces -/

namespace Xor3

/-- The output is the three-way xor `a ⊕ b ⊕ c`: it is 1 exactly when an odd number of the
inputs are 1. -/
def interface : Interface F fieldTriple field where
  Assumptions | (a, b, c) => IsBool a ∧ IsBool b ∧ IsBool c
  Spec | (a, b, c), d => IsBool d ∧ (d = 1 ↔ Xor (a = 1) (Xor (b = 1) (c = 1)))

/-- Xor of propositions is associative — the reason `xor (xor a b) c` is the three-way xor.
Mathlib has this for `Bool` but not for `Prop`. -/
theorem xor_assoc (A B C : Prop) : Xor (Xor A B) C ↔ Xor A (Xor B C) := by
  simp only [Xor]; tauto

/-- `a ⊕ b ⊕ c`, generic over the `xor` implementation. Its proof only uses `Xor.interface`. -/
def impl {B : Backend} [Field B.Native] (xor : Impl B Xor.interface) : Impl B interface where
  main | (a, b, c) => do
    let ab ← xor (a, b)
    xor (ab, c)
  soundness := by
    intro s env (a, b, c) h_as h
    simp only [circuit_norm] at h_as h ⊢
    simp only [circuit_norm, interface, Xor.interface] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h_bool, h_iff⟩ := h1 ⟨ha, hb⟩
    obtain ⟨h_bool', h_iff'⟩ := h2 ⟨h_bool, hc⟩
    refine ⟨h_bool', ?_⟩
    rw [h_iff', h_iff, ← xor_iff_not_iff, ← xor_iff_not_iff]
    exact xor_assoc ..
  completeness := by
    intro s env (a, b, c) _ _
    simp only [circuit_norm]
    simp only [circuit_norm, interface, Xor.interface]

end Xor3

def xor3R1CS : Impl (R1CS F) Xor3.interface := Xor3.impl xorR1CS
def xor3Expr : Impl (ExprBackend F) Xor3.interface := Xor3.impl xorExpr

example (a b c : LinComb F) (s : ℕ) : (xor3R1CS (F := F)).advance (a, b, c) s = s + 2 := rfl
example (a b c : Expr F) (s : ℕ) : (xor3Expr (F := F)).advance (a, b, c) s = s := rfl

end Clean2
