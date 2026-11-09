import Clean.Halo2.Keygen.CompressSelectors
import Clean.Halo2.Keygen.FloorPlanner.RegionShape
import Mathlib.Data.Nat.Bitwise

/-!
# Bitset computation of selector conflicts

Each selector is represented by a natural number whose set bits are its active rows.
Local region masks are shifted by their placement and combined with bitwise OR; two
selectors conflict precisely when their masks have nonempty intersection. This lets
kernel evaluation run the existing greedy packing algorithm on compact masks without
searching the flattened activation list at each comparison.
-/

namespace Halo2.SelectorBitsets

/-- The active rows of one selector, represented by the set bits of a natural number. -/
def rowMask (sites : List (Nat × Nat)) (selector : Nat) : Nat :=
  sites.foldl (fun mask site =>
    if site.1 = selector then mask ||| (1 <<< site.2) else mask) 0

theorem testBit_rowMask_fold (sites : List (Nat × Nat)) (selector row initial : Nat) :
    (sites.foldl (fun mask site =>
      if site.1 = selector then mask ||| (1 <<< site.2) else mask) initial).testBit row = true ↔
      initial.testBit row = true ∨ (selector, row) ∈ sites := by
  induction sites generalizing initial with
  | nil => simp
  | cons site rest ih =>
    rw [List.foldl_cons, ih]
    rcases site with ⟨s, r⟩
    by_cases hSelectorEq : s = selector
    · subst s
      simp only [↓reduceIte, Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, Prod.mk.injEq, true_and]
      rw [eq_comm (a := r), or_assoc]
    · simp only [hSelectorEq, ↓reduceIte, List.mem_cons, Prod.mk.injEq, Ne.symm hSelectorEq,
        false_and, false_or]

/-- Bit membership exactly records selector activation, including duplicate sites. -/
theorem testBit_rowMask (sites : List (Nat × Nat)) (selector row : Nat) :
    (rowMask sites selector).testBit row = true ↔ (selector, row) ∈ sites := by
  unfold rowMask
  rw [testBit_rowMask_fold]
  simp

theorem land_ne_zero_iff (left right : Nat) :
    left &&& right ≠ 0 ↔ ∃ row, left.testBit row = true ∧ right.testBit row = true := by
  constructor
  · intro h
    obtain ⟨row, hRow⟩ := Nat.exists_testBit_of_ne_zero h
    simp only [Nat.testBit_land, Bool.and_eq_true] at hRow
    exact ⟨row, hRow⟩
  · rintro ⟨row, hLeft, hRight⟩ hZero
    have hBit := congrArg (fun n => n.testBit row) hZero
    simp [hLeft, hRight] at hBit

/-- Bitset intersection computes the original activation-list conflict predicate. -/
theorem selectorActivationsConflict_eq (sites : List (Nat × Nat)) (left right : Nat) :
    selectorActivationsConflict sites left right =
      (rowMask sites left &&& rowMask sites right != 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectorActivationsConflict, List.any_eq_true,
    decide_eq_true_eq, mem_selectorActivationRows_iff, bne_iff_ne,
    land_ne_zero_iff, testBit_rowMask]

theorem rowMask_append (left right : List (Nat × Nat)) (selector : Nat) :
    rowMask (left ++ right) selector = rowMask left selector ||| rowMask right selector := by
  apply Nat.eq_of_testBit_eq
  intro row
  apply Bool.eq_iff_iff.mpr
  simp only [testBit_rowMask, Nat.testBit_lor, Bool.or_eq_true, List.mem_append]

theorem rowMask_shift (sites : List (Nat × Nat)) (selector start : Nat) :
    rowMask (sites.map (fun site => (site.1, start + site.2))) selector =
      rowMask sites selector <<< start := by
  apply Nat.eq_of_testBit_eq
  intro row
  apply Bool.eq_iff_iff.mpr
  simp only [testBit_rowMask, Nat.testBit_shiftLeft, Bool.and_eq_true,
    decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨⟨s, r⟩, hMem, hEq⟩
    cases hEq
    refine ⟨Nat.le_add_right _ _, ?_⟩
    simp only [Nat.add_sub_cancel_left]
    exact hMem
  · rintro ⟨hLe, hMem⟩
    exact ⟨(selector, row - start), hMem, by simp [Nat.add_sub_of_le hLe]⟩

/-- Combine local region masks after shifting each by its assigned start row.
The region boundary avoids constructing a single large flattened activation list. -/
def placedRowMask (starts : List Nat) (initial : Nat)
    (regions : List (List (Nat × Nat))) (selector : Nat) : Nat :=
  (regions.zipIdx initial).foldl (fun mask (sites, i) =>
    mask ||| (rowMask sites selector <<< starts.getD i 0)) 0

theorem placedRowMask_fold (starts : List Nat) (initial : Nat)
    (regions : List (List (Nat × Nat))) (selector accumulator : Nat) :
    (regions.zipIdx initial).foldl (fun mask (sites, i) =>
      mask ||| (rowMask sites selector <<< starts.getD i 0)) accumulator =
        accumulator ||| rowMask (placeSelectorActivations starts initial regions) selector := by
  induction regions generalizing initial accumulator with
  | nil => simp [placeSelectorActivations, rowMask]
  | cons sites rest ih =>
    rw [List.zipIdx_cons, List.foldl_cons, ih, placeSelectorActivations,
      rowMask_append, rowMask_shift, Nat.lor_assoc]

/-- Computing region by region gives exactly the bitset of the placed activations. -/
theorem placedRowMask_eq (starts : List Nat) (initial : Nat)
    (regions : List (List (Nat × Nat))) (selector : Nat) :
    placedRowMask starts initial regions selector =
      rowMask (placeSelectorActivations starts initial regions) selector := by
  rw [placedRowMask, placedRowMask_fold, Nat.zero_or]

/-- Materialize the masks once so the packing algorithm can share them across comparisons. -/
def placedRowMasks (starts : List Nat) (initial : Nat)
    (regions : List (List (Nat × Nat))) (numSelectors : Nat) : Array Nat :=
  ((List.range numSelectors).map (placedRowMask starts initial regions)).toArray

/-- Each materialized mask represents precisely that selector's placed activations. -/
theorem getElem!_placedRowMasks (starts : List Nat) (initial : Nat)
    (regions : List (List (Nat × Nat))) (numSelectors selector : Nat)
    (hSelector : selector < numSelectors) :
    (placedRowMasks starts initial regions numSelectors)[selector]! =
      rowMask (placeSelectorActivations starts initial regions) selector := by
  simp only [placedRowMasks, List.getElem!_toArray]
  rw [getElem!_pos, List.getElem_map, List.getElem_range, placedRowMask_eq]
  simp only [List.length_map, List.length_range]
  exact hSelector

end Halo2.SelectorBitsets
