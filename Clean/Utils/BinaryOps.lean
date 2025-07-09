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

-- Import theorems from Bitwise module

section ListOperations

/-- Folding AND over any list of natural numbers starting from 1 gives an IsBool result -/
theorem List.foldl_and_IsBool (l : List ℕ) :
    IsBool (List.foldl (· &&& ·) 1 l : ℕ) := by
  -- We'll prove a more general statement: folding with any IsBool initial value
  -- preserves the IsBool property
  suffices h_general : ∀ (init : ℕ), IsBool init → IsBool (List.foldl (· &&& ·) init l) by
    exact h_general 1 IsBool.one

  intro init h_init
  induction l generalizing init with
  | nil =>
    simp only [List.foldl_nil]
    exact h_init
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    apply IsBool.land_inherit_left
    assumption

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


end BinaryOps
