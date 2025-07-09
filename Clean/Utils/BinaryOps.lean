import Clean.Utils.Vector
import Clean.Utils.Bitwise
import Clean.Utils.Field
import Clean.Gadgets.Boolean

/-!
# Binary Operations Utilities

This file contains general lemmas about binary operations on lists and vectors,
particularly for AND operations on binary values (0 or 1).
-/

namespace BinaryOps

variable {p : ℕ} [Fact p.Prime]

open Bitwise (and_zero_absorb and_one_id_binary)

section ListOperations

/-- Folding AND over a list of natural numbers with IsBool gives an IsBool result -/
theorem List.foldl_and_IsBool (l : List ℕ) :
    (∀ x ∈ l, IsBool x) →
    IsBool (List.foldl (· &&& ·) 1 l : ℕ) := by
  intro h_all_binary
  induction l with
  | nil =>
    simp only [List.foldl_nil]
    exact IsBool.one
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h_x_binary : IsBool x := h_all_binary x (List.Mem.head xs)
    have h_xs_binary : ∀ y ∈ xs, IsBool y := fun y hy =>
      h_all_binary y (List.Mem.tail x hy)
    have h_tail_binary := ih h_xs_binary
    cases h_x_binary with
    | inl h_x_zero =>
      rw [h_x_zero]
      simp only [HAnd.hAnd, AndOp.and]
      left
      suffices h : List.foldl (· &&& ·) (1 &&& 0) xs = 0 by
        simp only [List.foldl_cons, HAnd.hAnd, AndOp.and] at h ⊢
        exact h
      have h_one_zero : (1 : ℕ) &&& 0 = 0 := by
        simp only [HAnd.hAnd, AndOp.and]
        rfl
      rw [h_one_zero]
      clear h_one_zero h_x_zero h_all_binary h_xs_binary h_tail_binary ih
      generalize hxs : xs = xs'
      clear xs hxs
      induction xs' with
      | nil => simp [List.foldl_nil]
      | cons y ys ih =>
        simp only [List.foldl_cons, HAnd.hAnd, AndOp.and]
        have h_zero_y : (0 : ℕ).land y = 0 := by
          unfold Nat.land
          simp [Nat.bitwise]
        rw [h_zero_y]
        exact ih
    | inr h_x_one =>
      rw [h_x_one]
      have h_one_one : (1 : ℕ) &&& 1 = 1 := by
        simp only [HAnd.hAnd, AndOp.and]
        rfl
      rw [h_one_one]
      exact h_tail_binary

/-- For binary values and binary lists, a &&& foldl orig l = foldl (a &&& orig) l -/
theorem List.and_foldl_eq_foldl_of_all_binary (a : ℕ) (orig : ℕ) (l : List ℕ)
    (_ha : IsBool a) (hl : ∀ x ∈ l, IsBool x) :
    a &&& List.foldl (· &&& ·) orig l = List.foldl (· &&& ·) (a &&& orig) l := by
  induction l generalizing orig with
  | nil =>
    simp only [List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hhd : hd = 0 ∨ hd = 1 := hl hd (List.Mem.head _)
    have htl : ∀ x ∈ tl, x = 0 ∨ x = 1 := fun x hx => hl x (List.mem_cons_of_mem hd hx)
    rw [ih (orig &&& hd) htl]
    congr 1
    simp only [HAnd.hAnd, AndOp.and]
    show a &&& (orig &&& hd) = (a &&& orig) &&& hd
    exact (Nat.land_assoc a orig hd).symm

end ListOperations

section VectorOperations

/-- If all elements of a vector are binary, then all elements of its list are binary -/
theorem Vector.toList_binary {α : Type*} {n : ℕ} (v : Vector α n)
    (isBinary : α → Prop) :
    (∀ i : Fin n, isBinary v[i]) →
    (∀ x ∈ v.toList, isBinary x) := by
  intro h_vec x h_mem
  rw [Vector.mem_toList_iff_get] at h_mem
  rcases h_mem with ⟨i, hi⟩
  rw [hi]
  exact h_vec i

/-- Specialized version for F p where binary means IsBool -/
theorem Vector.toList_binary_field {n : ℕ} (v : Vector (F p) n) :
    (∀ i : Fin n, IsBool v[i]) →
    (∀ x ∈ v.toList, IsBool x) :=
  Vector.toList_binary v IsBool

end VectorOperations

end BinaryOps
