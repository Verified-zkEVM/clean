import Clean.Circuit
import Clean.Orchard.Ecc.Defs
import Clean.Orchard.NoteCommit
import Clean.Utils.Tactics
import Mathlib.Tactic

/-!
Shared definitions for Orchard scalar multiplication gates.
-/

namespace Orchard.Ecc.ScalarMul

def ternary {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K]
    (choice ifTrue ifFalse : K) : K :=
  choice * ifTrue + (1 - choice) * ifFalse

def tQ {K : Type} [OfNat K 45560315531506369815346746415080538113] : K :=
  OfNat.ofNat 45560315531506369815346746415080538113

def IsBool {K : Type} [Zero K] [One K] (x : K) : Prop :=
  x = 0 ∨ x = 1

theorem isBool_of_boolPoly_eq_zero {F : Type} [Field F] {x : F}
    (h : NoteCommit.boolPoly x = 0) :
    IsBool x := by
  unfold NoteCommit.boolPoly at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem boolPoly_eq_zero_of_isBool {F : Type} [Field F] {x : F} (h : IsBool x) :
    NoteCommit.boolPoly x = 0 := by
  rcases h with h | h <;> rw [h] <;> simp [NoteCommit.boolPoly]

end Orchard.Ecc.ScalarMul
