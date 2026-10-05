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

@[reducible]
def interface : Interface Native where
  input := Native
  inputCType := .native
  output := Native
  outputCType := .native
  Assumptions := fun x => IsBool x
  Spec := fun x out => IsBool out ∧ (out = 1 ↔ x ≠ 1)

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

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Assumptions := fun (a, b) => IsBool a ∧ IsBool b
  Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ a = 1 ∧ b = 1)

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

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Assumptions := fun (a, b) => IsBool a ∧ IsBool b
  Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ a = 1 ∨ b = 1)

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

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Assumptions := fun (a, b) => IsBool a ∧ IsBool b
  Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ∧ b = 1))

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

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Assumptions := fun (a, b) => IsBool a ∧ IsBool b
  Spec := fun (a, b) c => IsBool c ∧ (c = 1 ↔ ¬(a = 1 ∨ b = 1))

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

end Clean2
