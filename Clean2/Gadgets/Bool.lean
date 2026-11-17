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

/-! ## `toBit`: where native elements become booleans -/

namespace ToBit

/-- A native element is a bit. An assertion; its output is the same element, as a boolean. -/
@[reducible]
def interface [DecidableEq Native] : Interface Native where
  input := Native
  inputCType := .native
  output := Bool
  outputCType := bit Native
  Spec := fun x b => IsBool x ∧ b = decide (x = 1)
  ProverAssumptions := fun x => IsBool x

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (assertBool : Impl B AssertBool.interface) :
    Impl B interface where
  main x := do
    assertBool x
    return x
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    exact ⟨h, h, rfl⟩
  completeness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    exact ⟨h, h⟩

end ToBit

/-! ## `xor`, implemented via the arithmetic functionalities -/

namespace Xor

/-- The xor of two booleans, laid out as `bool`. -/
@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool
  inputCType := bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b) c => c = (a ^^ b)

/-- `a ⊕ b = a + b - 2ab`, on bits. Generic over how arithmetic is done. -/
def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (arith : ∀ n, Impl B (Arith.interface n)) :
    Impl B (interface (bit B.Native)) where
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
    intro s env (a, b) h h_as
    simp only [circuit_norm, IsBool] at h h_as ⊢
    obtain ⟨ha, hb⟩ := h_as
    obtain ⟨ht, hs, hu, hc⟩ := h
    rw [hc, hu, hs, ht]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

end Xor

/-! ## Stacking: a gadget generic over gadget-level interfaces, and over the layout of booleans -/

namespace Xor3

/-- The three-way xor `a ⊕ b ⊕ c`. -/
@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool × Bool
  inputCType := bool ×ᵗ bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b, c) d => d = (a ^^ b ^^ c)

/-- `a ⊕ b ⊕ c`, generic over the `xor` implementation and the layout of a boolean. Its proof only
uses `Xor.interface`. -/
def impl {B : Backend} {bool : CType B.Native Bool} (xor : Impl B (Xor.interface bool)) :
    Impl B (interface bool) where
  main | (a, b, c) => do
    let ab ← xor (a, b)
    xor (ab, c)
  spatial := by
    rintro ⟨a, b, c⟩ s h_in
    obtain ⟨ha, hb, hc⟩ := (Backend.footprintT_ctypeProd_subset.mp h_in).imp_right Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Set.union_subset ha hb, fun h_ab h_mono => ⟨Set.union_subset h_ab (hc.trans h_mono), fun h_d _ => h_d⟩⟩
  soundness := by
    rintro s env ⟨a, b, c⟩ h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨v_ab, e_ab⟩ := h.1 ⟨ha, hb⟩
    obtain ⟨v_d, e_d⟩ := h.2 ⟨v_ab, hc⟩
    exact ⟨v_d, by rw [e_d, e_ab]⟩
  completeness := by
    rintro s env ⟨a, b, c⟩ h h_as
    simp only [circuit_norm] at h h_as ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    have v_ab := (h.1 ⟨ha, hb⟩).2
    exact ⟨⟨⟨ha, hb⟩, v_ab, hc⟩, (h.2 ⟨v_ab, hc⟩).2⟩

end Xor3

end Clean2
