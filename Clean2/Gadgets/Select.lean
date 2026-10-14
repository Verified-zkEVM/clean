/-
Selection: `mux`, and the two SHA-256 bit functions `ch` and `maj`.

`mux` is arithmetic, and takes its condition at `bit`. `ch` and `maj` are the top of the stack in
this file: they are written purely against `AND.interface`, `OR.interface` and `NOT.interface`, for
any layout of a boolean, so their proofs are boolean identities.
-/
module

public import Clean2.Gadgets.Gates

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

namespace Gates

/-! ## `mux`: `out = b + c * (a - b)`, a conditional over arbitrary field values -/

namespace MUX

@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Native × Native
  inputCType := bool ×ᵗ .native ×ᵗ .native
  output := Native
  outputCType := .native
  Spec := fun (c, a, b) out => out = bif c then a else b

def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (arith : ∀ n, Impl B (Arith.interface n)) :
    Impl B (interface (bit B.Native)) where
  main | (c, a, b) => do
    let d ← arith .sub (a, b)
    let t ← arith .mul (c, d)
    arith .add (t, b)
  spatial := by
    rintro ⟨c, a, b⟩ s h_in
    obtain ⟨hc, ha, hb⟩ := (Backend.footprintT_ctypeProd_subset.mp h_in).imp_right Backend.footprintT_ctypeProd_subset.mp
    rw [Backend.footprintT_native_subset] at hc ha hb
    simp only [circuit_norm]
    exact ⟨Set.union_subset ha hb, fun h_d m₁ => ⟨Set.union_subset (hc.trans m₁) h_d, fun h_t m₂ =>
      ⟨Set.union_subset h_t (hb.trans (m₁.trans m₂)), fun h_out _ => h_out⟩⟩⟩
  soundness := by
    intro s env (c, a, b) h_as h
    simp only [circuit_norm, IsBool] at h_as h ⊢
    obtain ⟨hd, ht, hout⟩ := h
    rw [hout, ht, hd]
    rcases h_as with hc | hc <;> simp [hc]
  completeness := by
    intro s env (c, a, b) _ _
    simp only [circuit_norm]

end MUX

/-! ## `ch a b c = if a then b else c`, on booleans -/

namespace CH

@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool × Bool
  inputCType := bool ×ᵗ bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b, c) out => out = bif a then b else c

/-- `(a ∧ b) ∨ (¬a ∧ c)`. No arithmetic appears in this definition or in its proof. -/
def impl {B : Backend} {bool : CType B.Native Bool} (and : Impl B (AND.interface bool))
    (or : Impl B (OR.interface bool)) (not : Impl B (NOT.interface bool)) : Impl B (interface bool) where
  main | (a, b, c) => do
    let ab ← and (a, b)
    let na ← not a
    let nac ← and (na, c)
    or (ab, nac)
  spatial := by
    rintro ⟨a, b, c⟩ s h_in
    obtain ⟨ha, hb, hc⟩ := (Backend.footprintT_ctypeProd_subset.mp h_in).imp_right Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Set.union_subset ha hb, fun h_ab m₁ => ⟨ha.trans m₁, fun h_na m₂ =>
      ⟨Set.union_subset h_na (hc.trans (m₁.trans m₂)), fun h_nac m₃ =>
        ⟨Set.union_subset (h_ab.trans (m₂.trans m₃)) h_nac, fun h_out _ => h_out⟩⟩⟩⟩
  soundness := by
    rintro s env ⟨a, b, c⟩ h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h_and, h_not, h_and', h_or⟩ := h
    obtain ⟨v_ab, e_ab⟩ := h_and ⟨ha, hb⟩
    obtain ⟨v_na, e_na⟩ := h_not ha
    obtain ⟨v_nac, e_nac⟩ := h_and' ⟨v_na, hc⟩
    obtain ⟨v_out, e_out⟩ := h_or ⟨v_ab, v_nac⟩
    refine ⟨v_out, ?_⟩
    rw [e_out, e_ab, e_nac, e_na]
    cases bool.decode (ProvableType.map (B.eval env) a) <;> simp
  completeness := by
    rintro s env ⟨a, b, c⟩ h h_as
    simp only [circuit_norm] at h h_as ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h_and, h_not, h_and', h_or⟩ := h
    have v_ab := (h_and ⟨ha, hb⟩).2
    have v_na := (h_not ha).2
    have v_nac := (h_and' ⟨v_na, hc⟩).2
    exact ⟨⟨⟨ha, hb⟩, ha, ⟨v_na, hc⟩, v_ab, v_nac⟩, (h_or ⟨v_ab, v_nac⟩).2⟩

end CH

/-! ## `maj a b c`: the majority of three booleans -/

namespace MAJ

@[reducible]
def interface (bool : CType Native Bool) : Interface Native where
  input := Bool × Bool × Bool
  inputCType := bool ×ᵗ bool ×ᵗ bool
  output := Bool
  outputCType := bool
  Spec := fun (a, b, c) out => out = (a && b || a && c || b && c)

/-- `(a ∧ b) ∨ (a ∧ c) ∨ (b ∧ c)`. -/
def impl {B : Backend} {bool : CType B.Native Bool} (and : Impl B (AND.interface bool))
    (or : Impl B (OR.interface bool)) : Impl B (interface bool) where
  main | (a, b, c) => do
    let ab ← and (a, b)
    let ac ← and (a, c)
    let bc ← and (b, c)
    let t ← or (ab, ac)
    or (t, bc)
  spatial := by
    rintro ⟨a, b, c⟩ s h_in
    obtain ⟨ha, hb, hc⟩ := (Backend.footprintT_ctypeProd_subset.mp h_in).imp_right Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Set.union_subset ha hb, fun h_ab m₁ => ⟨Set.union_subset (ha.trans m₁) (hc.trans m₁), fun h_ac m₂ =>
      ⟨Set.union_subset (hb.trans (m₁.trans m₂)) (hc.trans (m₁.trans m₂)), fun h_bc m₃ =>
        ⟨Set.union_subset (h_ab.trans (m₂.trans m₃)) (h_ac.trans m₃), fun h_t m₄ =>
          ⟨Set.union_subset h_t (h_bc.trans m₄), fun h_out _ => h_out⟩⟩⟩⟩⟩
  soundness := by
    rintro s env ⟨a, b, c⟩ h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h_ab, h_ac, h_bc, h_t, h_or⟩ := h
    obtain ⟨v_ab, e_ab⟩ := h_ab ⟨ha, hb⟩
    obtain ⟨v_ac, e_ac⟩ := h_ac ⟨ha, hc⟩
    obtain ⟨v_bc, e_bc⟩ := h_bc ⟨hb, hc⟩
    obtain ⟨v_t, e_t⟩ := h_t ⟨v_ab, v_ac⟩
    obtain ⟨v_out, e_out⟩ := h_or ⟨v_t, v_bc⟩
    refine ⟨v_out, ?_⟩
    rw [e_out, e_t, e_ab, e_ac, e_bc]
  completeness := by
    rintro s env ⟨a, b, c⟩ h h_as
    simp only [circuit_norm] at h h_as ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h_ab, h_ac, h_bc, h_t, h_or⟩ := h
    have v_ab := (h_ab ⟨ha, hb⟩).2
    have v_ac := (h_ac ⟨ha, hc⟩).2
    have v_bc := (h_bc ⟨hb, hc⟩).2
    have v_t := (h_t ⟨v_ab, v_ac⟩).2
    exact ⟨⟨⟨ha, hb⟩, ⟨ha, hc⟩, ⟨hb, hc⟩, ⟨v_ab, v_ac⟩, v_t, v_bc⟩, (h_or ⟨v_t, v_bc⟩).2⟩

end MAJ
end Gates

end Clean2
