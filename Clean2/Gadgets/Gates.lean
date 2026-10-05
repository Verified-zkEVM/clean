/-
Boolean gates: the smallest interesting family of functionalities, and the first place where
gadgets are built on *gadgets* rather than on arithmetic.

Two tiers:
- `NOT`, `AND`, `OR` are implemented directly over `Arith.interface`;
- `NAND`, `NOR` are implemented over `NOT.interface` and `AND.interface`/`OR.interface`. Their proofs never
  look at a circuit: they only compose the specs of the gates they call.

A gate's interface is stated on `Bool`, at a synthetic type `bool : CType Native Bool` it is
given: its spec is the boolean function it computes. The field encoding (`1 - x`, `a * b`, ...)
is implementation, and never appears in an interface: the direct gates are implemented at
`bit`, where a boolean is one native element that is `0` or `1`, and the gates built on gates
are generic in `bool`.
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
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool
  inputCType := bool
  output := Bool
  outputCType := bool
  Spec := fun x out => out = !x

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (arith : ∀ n, Impl B (Arith.interface n)) :
    Impl B (interface (bit B.Native)) where
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
    intro s env x h hx
    simp only [circuit_norm, IsBool] at h hx ⊢
    obtain ⟨hone, hout⟩ := h
    rw [hout, hone]
    rcases hx with hx | hx <;> simp [hx]

end NOT

/-! ## `AND`: `out = a * b` -/

namespace AND

@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool
  inputCType := bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b) c => c = (a && b)

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (arith : ∀ n, Impl B (Arith.interface n)) :
    Impl B (interface (bit B.Native)) where
  main | (a, b) => arith .mul (a, b)
  soundness := by
    intro s env (a, b) h_as h
    simp only [circuit_norm, IsBool] at h_as h ⊢
    obtain ⟨ha, hb⟩ := h_as
    simp only [h]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
  completeness := by
    intro s env (a, b) h h_as
    simp only [circuit_norm, IsBool] at h h_as ⊢
    obtain ⟨ha, hb⟩ := h_as
    simp only [h]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

end AND

/-! ## `OR`: `out = a + b - a * b` -/

namespace OR

@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool
  inputCType := bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b) c => c = (a || b)

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (arith : ∀ n, Impl B (Arith.interface n)) :
    Impl B (interface (bit B.Native)) where
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
    intro s env (a, b) h h_as
    simp only [circuit_norm, IsBool] at h h_as ⊢
    obtain ⟨ha, hb⟩ := h_as
    obtain ⟨hab, hsum, hout⟩ := h
    rw [hout, hsum, hab]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

end OR

/-! ## `NAND` and `NOR`: gates built out of gates.

Both implementations are parametrized by the gates they use, and by the layout of a boolean;
both proofs are pure spec composition — the circuits of `and`, `or`, `not` are never unfolded,
and the validity of each output is only carried to the next input. -/

namespace NAND

@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool
  inputCType := bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b) c => c = !(a && b)

def impl {B : Backend} {bool : CType B.Native Bool} (and : Impl B (AND.interface bool))
    (not : Impl B (NOT.interface bool)) : Impl B (interface bool) where
  main | (a, b) => do
    let ab ← and (a, b)
    not ab
  spatial := by
    rintro ⟨a, b⟩ s h_in
    obtain ⟨ha, hb⟩ := Backend.footprintT_ctypeProd_subset.mp h_in
    simp only [circuit_norm]
    exact ⟨Set.union_subset ha hb, fun h_ab _ => ⟨h_ab, fun h_c _ => h_c⟩⟩
  soundness := by
    rintro s env ⟨a, b⟩ h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨v_ab, e_ab⟩ := h.1 h_as
    obtain ⟨v_c, e_c⟩ := h.2 v_ab
    exact ⟨v_c, by rw [e_c, e_ab]⟩
  completeness := by
    rintro s env ⟨a, b⟩ h h_as
    simp only [circuit_norm] at h h_as ⊢
    have v_ab := (h.1 h_as).2
    exact ⟨⟨h_as, v_ab⟩, (h.2 v_ab).2⟩

end NAND

namespace NOR

@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool
  inputCType := bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b) c => c = !(a || b)

def impl {B : Backend} {bool : CType B.Native Bool} (or : Impl B (OR.interface bool))
    (not : Impl B (NOT.interface bool)) : Impl B (interface bool) where
  main | (a, b) => do
    let ab ← or (a, b)
    not ab
  spatial := by
    rintro ⟨a, b⟩ s h_in
    obtain ⟨ha, hb⟩ := Backend.footprintT_ctypeProd_subset.mp h_in
    simp only [circuit_norm]
    exact ⟨Set.union_subset ha hb, fun h_ab _ => ⟨h_ab, fun h_c _ => h_c⟩⟩
  soundness := by
    rintro s env ⟨a, b⟩ h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨v_ab, e_ab⟩ := h.1 h_as
    obtain ⟨v_c, e_c⟩ := h.2 v_ab
    exact ⟨v_c, by rw [e_c, e_ab]⟩
  completeness := by
    rintro s env ⟨a, b⟩ h h_as
    simp only [circuit_norm] at h h_as ⊢
    have v_ab := (h.1 h_as).2
    exact ⟨⟨h_as, v_ab⟩, (h.2 v_ab).2⟩

end NOR
end Gates

end Clean2
