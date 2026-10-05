/-
Selection: `mux`, and the two SHA-256 bit functions `ch` and `maj`.

`mux` is arithmetic. `ch` and `maj` are the top of the stack in this file: they are written
purely against `AND.interface`, `OR.interface` and `NOT.interface`, so they are simultaneously a statement
about circuits and about booleans, and their proofs are propositional.
-/
module

public import Clean2.Gadgets.Gates

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

namespace Gates

/-! ## `mux`: `out = b + c * (a - b)`, a conditional over arbitrary field values -/

namespace MUX

abbrev interface : Interface Native :=
  { input := Native × Native × Native, inputCType := .nativeTriple,
    output := Native, outputCType := .native
    Assumptions := fun (c, _, _) => IsBool c
    Spec := fun (c, a, b) out => (c = 1 → out = a) ∧ (c = 0 → out = b) }

def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
  main | (c, a, b) => do
    let d ← arith .sub (a, b)
    let t ← arith .mul (c, d)
    arith .add (t, b)
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

/-! ## `ch a b c = if a then b else c`, on bits -/

namespace CH

abbrev interface : Interface Native :=
  { input := Native × Native × Native, inputCType := .nativeTriple,
    output := Native, outputCType := .native
    Assumptions := fun (a, b, c) => IsBool a ∧ IsBool b ∧ IsBool c
    Spec := fun (a, b, c) out => IsBool out ∧ (out = 1 ↔ (a = 1 ∧ b = 1) ∨ (a ≠ 1 ∧ c = 1)) }

/-- `(a ∧ b) ∨ (¬a ∧ c)`. No arithmetic appears in this definition or in its proof. -/
def impl {B : Backend} [Field B.Native] (and : Impl B AND.interface) (or : Impl B OR.interface)
    (not : Impl B NOT.interface) : Impl B interface where
  main | (a, b, c) => do
    let ab ← and (a, b)
    let na ← not a
    let nac ← and (na, c)
    or (ab, nac)
  soundness := by
    intro s env (a, b, c) h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h_and, h_not, h_and', h_or⟩ := h
    obtain ⟨hbool_ab, hiff_ab⟩ := h_and ⟨ha, hb⟩
    obtain ⟨hbool_na, hiff_na⟩ := h_not ha
    obtain ⟨hbool_nac, hiff_nac⟩ := h_and' ⟨hbool_na, hc⟩
    obtain ⟨hbool_out, hiff_out⟩ := h_or ⟨hbool_ab, hbool_nac⟩
    refine ⟨hbool_out, ?_⟩
    rw [hiff_out, hiff_ab, hiff_nac, hiff_na]
  completeness := by
    intro s env (a, b, c) _ _
    simp only [circuit_norm]

end CH

/-! ## `maj a b c`: the majority of three bits -/

namespace MAJ

abbrev interface : Interface Native :=
  { input := Native × Native × Native, inputCType := .nativeTriple,
    output := Native, outputCType := .native
    Assumptions := fun (a, b, c) => IsBool a ∧ IsBool b ∧ IsBool c
    Spec := fun (a, b, c) out => IsBool out ∧ (out = 1 ↔ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨ (b = 1 ∧ c = 1)) }

/-- `(a ∧ b) ∨ (a ∧ c) ∨ (b ∧ c)`. -/
def impl {B : Backend} [Field B.Native] (and : Impl B AND.interface) (or : Impl B OR.interface) : Impl B interface where
  main | (a, b, c) => do
    let ab ← and (a, b)
    let ac ← and (a, c)
    let bc ← and (b, c)
    let t ← or (ab, ac)
    or (t, bc)
  soundness := by
    intro s env (a, b, c) h_as h
    simp only [circuit_norm] at h_as h ⊢
    obtain ⟨ha, hb, hc⟩ := h_as
    obtain ⟨h_ab, h_ac, h_bc, h_t, h_or⟩ := h
    obtain ⟨hbool_ab, hiff_ab⟩ := h_ab ⟨ha, hb⟩
    obtain ⟨hbool_ac, hiff_ac⟩ := h_ac ⟨ha, hc⟩
    obtain ⟨hbool_bc, hiff_bc⟩ := h_bc ⟨hb, hc⟩
    obtain ⟨hbool_t, hiff_t⟩ := h_t ⟨hbool_ab, hbool_ac⟩
    obtain ⟨hbool_out, hiff_out⟩ := h_or ⟨hbool_t, hbool_bc⟩
    refine ⟨hbool_out, ?_⟩
    rw [hiff_out, hiff_t, hiff_ab, hiff_ac, hiff_bc, or_assoc]
  completeness := by
    intro s env (a, b, c) _ _
    simp only [circuit_norm]

end MAJ
end Gates

/-! ## On both backends -/

section
open Gates

def muxExpr : Impl (ExprBackend Native) MUX.interface := MUX.impl ExprBackend.arith
def muxR1CS : Impl (R1CS Native) MUX.interface := MUX.impl R1CS.arith

def chExpr : Impl (ExprBackend Native) CH.interface := CH.impl andExpr orExpr notExpr
def chR1CS : Impl (R1CS Native) CH.interface := CH.impl andR1CS orR1CS notR1CS

def majExpr : Impl (ExprBackend Native) MAJ.interface := MAJ.impl andExpr orExpr
def majR1CS : Impl (R1CS Native) MAJ.interface := MAJ.impl andR1CS orR1CS

example (c a b : Expr Native) (s : ℕ) : (muxExpr (Native := Native)).advance (c, a, b) s = s := rfl
example (c a b : LinComb Native) (s : ℕ) : (muxR1CS (Native := Native)).advance (c, a, b) s = s + 1 := rfl

/-- `ch` uses two `AND`s and one `OR`, so three product cells on R1CS and none on the expression backend. -/
example (a b c : Expr Native) (s : ℕ) : (chExpr (Native := Native)).advance (a, b, c) s = s := rfl
example (a b c : LinComb Native) (s : ℕ) : (chR1CS (Native := Native)).advance (a, b, c) s = s + 3 := rfl

/-- `maj` uses three `AND`s and two `OR`s. -/
example (a b c : LinComb Native) (s : ℕ) : (majR1CS (Native := Native)).advance (a, b, c) s = s + 5 := rfl

end
end Clean2
