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
variable {Native : Type} [Field Native]

def IsBool (x : Native) : Prop := x = 0 ∨ x = 1

/-- A bit is one native element, which is `0` or `1`: the synthetic type of `Bool`. -/
@[reducible]
def bit (Native : Type) [Field Native] [DecidableEq Native] : CType Native Bool where
  Shape := native
  Valid := IsBool
  decode x := decide (x = 1)

/-! ## `assertBool`, implemented via `mulEq` -/

namespace AssertBool

@[reducible]
def interface : Interface Native where
  input := Native
  inputCType := .native
  output := Unit
  outputCType := .unit
  Spec := fun x _ => IsBool x
  ProverAssumptions := fun x => IsBool x

/-- `x * x = x` forces `x ∈ {0, 1}`. -/
def impl {B : Backend} [Field B.Native] (mulEq : Impl B MulEq.interface) : Impl B interface where
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

/-! ## `xor`, implemented via the arithmetic functionalities -/

namespace Xor

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Assumptions := fun (a, b) => IsBool a ∧ IsBool b
  Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ↔ b = 1))

/-- `a ⊕ b = a + b - 2ab`. Generic over how arithmetic is done. -/
def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
  main | (a, b) => do
    let t ← arith .mul (a, b)
    let s ← arith .add (a, b)
    let u ← arith .add (t, t)
    arith .sub (s, u)
  soundness := by
    intro s env (a, b) h_as h
    simp only [circuit_norm, IsBool] at h_as h ⊢
    obtain ⟨ha, hb⟩ := h_as
    obtain ⟨ht, hs, hu, hc⟩ := h
    rw [hc, hu, hs, ht]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  completeness := by
    intro s env (a, b) _ _
    simp only [circuit_norm]

end Xor

/-! ## Stacking: a gadget generic over gadget-level interfaces -/

namespace Xor3

/-- The output is the three-way xor `a ⊕ b ⊕ c`: it is 1 exactly when an odd number of the
inputs are 1. -/
@[reducible]
def interface : Interface Native where
  input := Native × Native × Native
  inputCType := .nativeTriple
  output := Native
  outputCType := .native
  Assumptions := fun (a, b, c) => IsBool a ∧ IsBool b ∧ IsBool c
  Spec := fun (a, b, c) d => IsBool d ∧ (d = 1 ↔ Xor (a = 1) (Xor (b = 1) (c = 1)))

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

end Xor3

end Clean2
