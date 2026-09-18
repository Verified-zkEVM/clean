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

abbrev iface : Interface F field unit where
  Spec x _ := IsBool x
  ProverAssumptions x := IsBool x

attribute [circuit_norm] iface

/-- `x * x = x` forces `x ∈ {0, 1}`. -/
def viaMulEq {B : Backend F} (mulEq : Impl B MulEq.iface) : Impl B iface where
  main x := mulEq (x, x, x)
  soundness := by
    intro s env x _ h
    simp only [circuit_norm, IsBool] at h ⊢
    have h : (B.eval env x) * (B.eval env x - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  completeness := by
    intro s env x _ h
    simp only [circuit_norm, IsBool] at h ⊢
    rcases h with h | h <;> simp [h]

end AssertBool

/-- The same gadget on two backends. -/
def assertBoolExpr : Impl (ExprBackend F) AssertBool.iface := AssertBool.viaMulEq ExprBackend.mulEq
def assertBoolR1CS : Impl (R1CS F) AssertBool.iface := AssertBool.viaMulEq R1CS.mulEq

/-- On R1CS, the fully resolved circuit is a single native constraint. -/
example (x : LinComb F) (s : ℕ) :
    ((assertBoolR1CS (F := F)).main x |>.operations s).toFlat = [.constraint x x x] := rfl

/-- On the expression backend, it is `x*x + (-1)*x = 0`. -/
example (x : Expr F) (s : ℕ) :
    ((assertBoolExpr (F := F)).main x |>.operations s).toFlat =
      [.assertZero (.add (.mul x x) (.mul (.const (-1)) x))] := rfl

/-! ## `xor`, implemented via the arithmetic functionalities -/

namespace Xor

abbrev iface : Interface F fieldPair field where
  Assumptions | (a, b) => IsBool a ∧ IsBool b
  Spec | (a, b), c => c = a + b - 2 * (a * b)

attribute [circuit_norm] iface

/-- `a ⊕ b = a + b - 2ab`. Generic over how arithmetic is done. -/
def viaArith {B : Backend F} (arith : Sig.Impl B Arith.sig) : Impl B iface where
  main | (a, b) => do
    let t ← arith .mul (a, b)
    let s ← arith .add (a, b)
    let u ← arith .add (t, t)
    arith .sub (s, u)
  soundness := by
    intro s env (a, b) _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨ht, hs, hu, hc⟩ := h
    rw [hc, hu, hs, ht]
    ring
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end Xor

def xorExpr : Impl (ExprBackend F) Xor.iface := Xor.viaArith ExprBackend.arith
def xorR1CS : Impl (R1CS F) Xor.iface := Xor.viaArith R1CS.arith

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

abbrev iface : Interface F fieldTriple field where
  Assumptions | (a, b, c) => IsBool a ∧ IsBool b ∧ IsBool c
  Spec | (a, b, c), d => d = (a + b - 2 * (a * b)) + c - 2 * ((a + b - 2 * (a * b)) * c)

attribute [circuit_norm] iface

/-- `a ⊕ b ⊕ c`, generic over the `xor` implementation. Its proof only uses `Xor.iface`. -/
def viaXor {B : Backend F} (xor : Impl B Xor.iface) : Impl B iface where
  main | (a, b, c) => do
    let ab ← xor (a, b)
    xor (ab, c)
  soundness := by
    intro s env (a, b, c) h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h1, h2⟩ := h
    have h1 := h1 ⟨ha, hb⟩
    have h_ab : IsBool (B.eval env (xor.output (a, b) s)) := by
      rw [h1]
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> norm_num [ha, hb, IsBool]
    rw [h2 ⟨h_ab, hc⟩, h1]
  completeness := by
    intro s env (a, b, c) _ _
    simp only [circuit_norm]

end Xor3

def xor3R1CS : Impl (R1CS F) Xor3.iface := Xor3.viaXor xorR1CS
def xor3Expr : Impl (ExprBackend F) Xor3.iface := Xor3.viaXor xorExpr

example (a b c : LinComb F) (s : ℕ) : (xor3R1CS (F := F)).advance (a, b, c) s = s + 2 := rfl
example (a b c : Expr F) (s : ℕ) : (xor3Expr (F := F)).advance (a, b, c) s = s := rfl

end Clean2
