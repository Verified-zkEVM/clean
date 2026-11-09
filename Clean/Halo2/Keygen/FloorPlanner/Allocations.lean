import Clean.Halo2.Keygen.FloorPlanner.RegionShape

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

/-! ## Column allocations (`v1/strategy.rs` `Allocations` / `CircuitAllocations`)

Per-column set of disjoint `[start, start+length)` allocated intervals, kept sorted by
`start` (Rust `BTreeSet<AllocatedRegion>` ordered by `start`). -/

/-- Disjointness of two half-open row intervals. -/
def RowIntervalsDisjoint
    (leftStart leftLength rightStart rightLength : ℕ) : Prop :=
  leftStart + leftLength ≤ rightStart ∨
    rightStart + rightLength ≤ leftStart

/-- A column's allocated intervals `(start, length)`, sorted by `start`, disjoint. -/
abbrev Allocations := Array (ℕ × ℕ)

/-- List-level core of sorted interval insertion. -/
def Allocations.insertList (start length : ℕ) :
    List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(start, length)]
  | head :: rest =>
      if start < head.1 then
        (start, length) :: head :: rest
      else
        head :: insertList start length rest

/-- Insert an allocated interval keeping the sort by `start` (`BTreeSet::insert`). -/
def Allocations.insert (a : Allocations) (start len : ℕ) : Allocations :=
  (insertList start len a.toList).toArray

private theorem Allocations.insertList_comm_of_ne
    (items : List (ℕ × ℕ)) {leftStart rightStart leftLength rightLength : ℕ}
    (hne : leftStart ≠ rightStart) :
    insertList rightStart rightLength
        (insertList leftStart leftLength items) =
      insertList leftStart leftLength
        (insertList rightStart rightLength items) := by
  induction items with
  | nil =>
      simp only [insertList]
      by_cases horder : leftStart < rightStart
      · simp [horder, Nat.not_lt.mpr (Nat.le_of_lt horder)]
      · have hreverse : rightStart < leftStart := by omega
        simp [horder, hreverse]
  | cons head rest inductionHypothesis =>
      by_cases hleft : leftStart < head.1
      · by_cases hright : rightStart < head.1
        · by_cases horder : leftStart < rightStart
          · have hnotReverse : ¬ rightStart < leftStart := by omega
            simp only [insertList, hleft, hright, horder, hnotReverse,
              if_pos, if_false]
          · have hreverse : rightStart < leftStart := by omega
            simp only [insertList, hleft, hright, horder, hreverse,
              if_pos, if_false]
        · have hnotRightLeft : ¬ rightStart < leftStart := by omega
          simp only [insertList, hleft, hright, hnotRightLeft,
            if_pos, if_false]
      · by_cases hright : rightStart < head.1
        · have hnotLeftRight : ¬ leftStart < rightStart := by omega
          simp only [insertList, hleft, hright, hnotLeftRight,
            if_pos, if_false]
        · simp only [insertList, hleft, hright, if_false]
          rw [inductionHypothesis]

/-- Intervals with distinct starts are inserted in a canonical order,
independently of insertion order. -/
theorem Allocations.insert_comm_of_ne
    (allocations : Allocations)
    {leftStart rightStart leftLength rightLength : ℕ}
    (hne : leftStart ≠ rightStart) :
    (allocations.insert leftStart leftLength).insert
        rightStart rightLength =
      (allocations.insert rightStart rightLength).insert
        leftStart leftLength := by
  simp only [insert]
  congr 1
  simpa using insertList_comm_of_ne allocations.toList hne

/-- Strict row ordering carried by adjacent allocated intervals. -/
def Allocations.IntervalBefore (left right : ℕ × ℕ) : Prop :=
  left.1 + left.2 ≤ right.1

/-- The representation invariant of a column's allocation set. -/
def Allocations.Valid (allocations : Allocations) : Prop :=
  allocations.toList.Pairwise IntervalBefore

/-- A proposed interval is disjoint from every existing allocation. -/
def Allocations.Fits
    (allocations : Allocations) (start length : ℕ) : Prop :=
  ∀ allocated ∈ allocations.toList,
    RowIntervalsDisjoint start length allocated.1 allocated.2

private theorem Allocations.mem_insertList
    (items : List (ℕ × ℕ)) (start length : ℕ) :
    (start, length) ∈ insertList start length items := by
  induction items with
  | nil => simp [insertList]
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split <;> simp_all

private theorem Allocations.mem_insertList_of_mem
    (items : List (ℕ × ℕ)) (start length : ℕ)
    {allocated : ℕ × ℕ} (hallocated : allocated ∈ items) :
    allocated ∈ insertList start length items := by
  induction items with
  | nil => simp at hallocated
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split
      · simp_all
      · simp only [List.mem_cons] at hallocated ⊢
        exact hallocated.imp_right inductionHypothesis

private theorem Allocations.mem_insertList_iff
    (items : List (ℕ × ℕ)) (start length : ℕ)
    (item : ℕ × ℕ) :
    item ∈ insertList start length items ↔
      item = (start, length) ∨ item ∈ items := by
  induction items with
  | nil => simp [insertList]
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split <;> simp_all [or_left_comm]

private theorem Allocations.valid_head_before
    {head : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hvalid : (head :: rest).Pairwise IntervalBefore)
    {item : ℕ × ℕ} (hitem : item ∈ rest) :
    IntervalBefore head item := by
  exact List.pairwise_cons.mp hvalid |>.1 item hitem

private theorem Allocations.valid_insertList
    (items : List (ℕ × ℕ)) (start length : ℕ)
    (hvalid : items.Pairwise IntervalBefore)
    (hfits : ∀ allocated ∈ items,
      RowIntervalsDisjoint start length allocated.1 allocated.2)
    (hlength : 0 < length) :
    (insertList start length items).Pairwise IntervalBefore := by
  induction items with
  | nil => simp [insertList]
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split
      next hlt =>
        rw [List.pairwise_cons]
        constructor
        · intro item hitem
          have hdisjoint := hfits item (by simp_all)
          rcases hdisjoint with hbefore | hafter
          · exact hbefore
          · have hstartLe : head.1 ≤ item.1 := by
              simp only [List.mem_cons] at hitem
              rcases hitem with rfl | hrest
              · exact le_rfl
              · exact (Nat.le_add_right head.1 head.2).trans
                  (valid_head_before hvalid hrest)
            omega
        · exact hvalid
      next hge =>
        rw [List.pairwise_cons] at hvalid ⊢
        constructor
        · intro item hitem
          by_cases hnew : item = (start, length)
          · subst item
            have hheadFits := hfits head (by simp)
            rcases hheadFits with hnewBefore | hheadBefore
            · omega
            · exact hheadBefore
          · rw [mem_insertList_iff] at hitem
            exact hvalid.1 item (hitem.resolve_left hnew)
        · apply inductionHypothesis hvalid.2
          intro allocated hallocated
          exact hfits allocated (by simp [hallocated])

/-- Inserting a positive fitting interval preserves sorted disjointness. -/
theorem Allocations.Valid.insert
    (allocations : Allocations) (start length : ℕ)
    (hvalid : allocations.Valid)
    (hfits : allocations.Fits start length)
    (hlength : 0 < length) :
    (allocations.insert start length).Valid := by
  simpa [Valid, insert] using
    valid_insertList allocations.toList start length hvalid hfits hlength

theorem Allocations.mem_insert
    (allocations : Allocations) (start length : ℕ) :
    (start, length) ∈ (allocations.insert start length).toList := by
  simpa [insert] using mem_insertList allocations.toList start length

theorem Allocations.mem_insert_iff
    (allocations : Allocations) (start length : ℕ)
    (interval : ℕ × ℕ) :
    interval ∈ (allocations.insert start length).toList ↔
      interval = (start, length) ∨ interval ∈ allocations.toList := by
  simpa [insert] using
    mem_insertList_iff allocations.toList start length interval

theorem Allocations.mem_insert_of_mem
    (allocations : Allocations) (start length : ℕ)
    {allocated : ℕ × ℕ} (hallocated : allocated ∈ allocations.toList) :
    allocated ∈ (allocations.insert start length).toList := by
  simpa [insert] using
    mem_insertList_of_mem allocations.toList start length hallocated

/-- `unbounded_interval_start` (`strategy.rs:53-59`): the row after the last allocated
interval, or 0. -/
def Allocations.unboundedStart (a : Allocations) : ℕ :=
  match a.toList.getLast? with
  | some (s, l) => s + l
  | none => 0

/-- Recursive core of `free_intervals`. The second component is the first row after
all processed allocations; the first contains the bounded gaps encountered so far. -/
def Allocations.scanFreeIntervals (endBound : Option ℕ) :
    List (ℕ × ℕ) → ℕ → List (ℕ × Option ℕ) × ℕ
  | [], row => ([], row)
  | (regionStart, regionLength) :: rest, row =>
      let past : Bool := match endBound with
        | some endRow => decide (regionStart ≥ endRow)
        | none => false
      if !past then
        let tail := scanFreeIntervals endBound rest
          (max row (regionStart + regionLength))
        (if row < regionStart then
            (row, some regionStart) :: tail.1
          else tail.1,
          tail.2)
      else
        scanFreeIntervals endBound rest row

/-- `free_intervals(start, end)` (`strategy.rs:64-98`): the unallocated intervals of this
column intersecting `[start, end)`, as `(spaceStart, spaceEnd?)` (`end? = none` unbounded).
The recursive scan is extensionally the Rust iterator: a region with `start ≥ end` is
skipped without advancing `row`, and the final item emits `[row, end)` when
`end = none ∨ row < end`. -/
def Allocations.freeIntervals (a : Allocations) (start : ℕ) (endBound : Option ℕ) :
    List (ℕ × Option ℕ) :=
  let result := scanFreeIntervals endBound a.toList start
  match endBound with
  | some endRow =>
      if result.2 < endRow then
        result.1 ++ [(result.2, some endRow)]
      else result.1
  | none => result.1 ++ [(result.2, none)]

/-- A candidate interval lies within a free-space descriptor. -/
def Allocations.SpaceAllows
    (space : ℕ × Option ℕ) (start length : ℕ) : Prop :=
  space.1 ≤ start ∧
    ∀ stop, space.2 = some stop → start + length ≤ stop

/-- If the requested interval already fits at the search boundary, the scan either
publishes that boundary as its first free interval or reaches the final free interval
without advancing it. -/
private theorem Allocations.scanFreeIntervals_head_of_fits
    (items : List (ℕ × ℕ)) (start length : ℕ)
    (endBound : Option ℕ)
    (hvalid : items.Pairwise IntervalBefore)
    (hfits : ∀ allocated ∈ items,
      RowIntervalsDisjoint start length allocated.1 allocated.2)
    (hlength : 0 < length)
    (hbound : ∀ stop, endBound = some stop → start + length ≤ stop) :
    let result := scanFreeIntervals endBound items start
    (∃ stop rest,
      result.1 = (start, stop) :: rest ∧
        SpaceAllows (start, stop) start length) ∨
      (result.1 = [] ∧ result.2 = start) := by
  induction items with
  | nil =>
      exact Or.inr ⟨rfl, rfl⟩
  | cons head rest inductionHypothesis =>
      have hrestValid := List.pairwise_cons.mp hvalid |>.2
      have hrestFits : ∀ allocated ∈ rest,
          RowIntervalsDisjoint start length allocated.1 allocated.2 := by
        intro allocated hallocated
        exact hfits allocated (by simp [hallocated])
      have hheadFits := hfits head (by simp)
      rcases hheadFits with hcandidateBefore | hheadBefore
      · cases endBound with
        | none =>
            simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
            have hgap : start < head.1 := by omega
            rw [if_pos hgap]
            exact Or.inl ⟨some head.1,
              (scanFreeIntervals none rest
                (max start (head.1 + head.2))).1,
              rfl, ⟨le_rfl, by
                intro stop hstop
                simp only [Option.some.injEq] at hstop
                subst stop
                exact hcandidateBefore⟩⟩
        | some endRow =>
            by_cases hpast : endRow ≤ head.1
            · simp only [scanFreeIntervals, hpast, decide_true,
                Bool.not_true]
              exact inductionHypothesis hrestValid hrestFits
            · simp only [scanFreeIntervals, hpast, decide_false,
                Bool.not_false, ↓reduceIte]
              have hgap : start < head.1 := by omega
              rw [if_pos hgap]
              exact Or.inl ⟨some head.1,
                (scanFreeIntervals (some endRow) rest
                  (max start (head.1 + head.2))).1,
                rfl, ⟨le_rfl, by
                  intro stop hstop
                  simp only [Option.some.injEq] at hstop
                  subst stop
                  exact hcandidateBefore⟩⟩
      · have hheadEnd : head.1 + head.2 ≤ start := hheadBefore
        have hnotPast : ∀ endRow, endBound = some endRow →
            ¬ endRow ≤ head.1 := by
          intro endRow hend hpast
          have := hbound endRow hend
          omega
        cases endBound with
        | none =>
            simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
            have hnoGap : ¬ start < head.1 := by omega
            rw [if_neg hnoGap, max_eq_left hheadEnd]
            exact inductionHypothesis hrestValid hrestFits
        | some endRow =>
            have hpast : ¬ endRow ≤ head.1 := hnotPast endRow rfl
            simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            have hnoGap : ¬ start < head.1 := by omega
            rw [if_neg hnoGap, max_eq_left hheadEnd]
            exact inductionHypothesis hrestValid hrestFits

/-- A fitting interval at the requested start is the first interval enumerated by
`freeIntervals`. -/
theorem Allocations.freeIntervals_starts_with_of_fits
    (allocations : Allocations) (start length : ℕ)
    (endBound : Option ℕ)
    (hvalid : allocations.Valid)
    (hfits : allocations.Fits start length)
    (hlength : 0 < length)
    (hbound : ∀ stop, endBound = some stop → start + length ≤ stop) :
    ∃ stop rest,
      allocations.freeIntervals start endBound = (start, stop) :: rest ∧
        SpaceAllows (start, stop) start length := by
  have hscan := scanFreeIntervals_head_of_fits allocations.toList
    start length endBound (by simpa [Valid] using hvalid) hfits hlength hbound
  cases endBound with
  | none =>
      rcases hscan with ⟨stop, rest, hresult, hallows⟩ | ⟨hresult, hend⟩
      · refine ⟨stop, rest ++ [((scanFreeIntervals none
            allocations.toList start).2, none)], ?_, hallows⟩
        simp only [freeIntervals, hresult, List.cons_append]
      · refine ⟨none, [], ?_, ⟨le_rfl, by simp⟩⟩
        simp [freeIntervals, hresult, hend]
  | some endRow =>
      have hstartEnd : start < endRow := by
        have := hbound endRow rfl
        omega
      rcases hscan with ⟨stop, rest, hresult, hallows⟩ | ⟨hresult, hend⟩
      · simp only [freeIntervals, hresult]
        split <;> rename_i hfinal
        · exact ⟨stop, rest ++
            [((scanFreeIntervals (some endRow)
              allocations.toList start).2, some endRow)], by
              simp only [List.cons_append], hallows⟩
        · exact ⟨stop, rest, rfl, hallows⟩
      · have hfinal :
            (scanFreeIntervals (some endRow)
              allocations.toList start).2 < endRow := by
          rw [hend]
          exact hstartEnd
        refine ⟨some endRow, [], ?_, ⟨le_rfl, ?_⟩⟩
        · simp [freeIntervals, hresult, hend, hstartEnd]
        · intro stop hstop
          have : stop = endRow := Option.some.inj hstop.symm
          subst stop
          exact hbound endRow rfl

private def Allocations.EndsBefore
    (items : List (ℕ × ℕ)) (row : ℕ) : Prop :=
  ∀ item ∈ items, item.1 + item.2 ≤ row

private theorem Allocations.valid_head_start_le
    {head : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hvalid : (head :: rest).Pairwise IntervalBefore)
    {item : ℕ × ℕ} (hitem : item ∈ head :: rest) :
    head.1 ≤ item.1 := by
  simp only [List.mem_cons] at hitem
  rcases hitem with rfl | hrest
  · exact le_rfl
  · exact (Nat.le_add_right head.1 head.2).trans
      (List.pairwise_cons.mp hvalid |>.1 item hrest)

private theorem Allocations.valid_suffix
    {previous items : List (ℕ × ℕ)}
    (hvalid : (previous ++ items).Pairwise IntervalBefore) :
    items.Pairwise IntervalBefore := by
  exact (List.pairwise_append.mp hvalid).2.1

private theorem Allocations.fits_of_before_and_after
    {previous suffix : List (ℕ × ℕ)} {boundary start length : ℕ}
    (hprevious : EndsBefore previous boundary)
    (hstart : boundary ≤ start)
    (hsuffix : ∀ item ∈ suffix, start + length ≤ item.1) :
    ∀ item ∈ previous ++ suffix,
      RowIntervalsDisjoint start length item.1 item.2 := by
  intro item hitem
  rw [List.mem_append] at hitem
  rcases hitem with hpast | hsuffixItem
  · exact Or.inr ((hprevious item hpast).trans hstart)
  · exact Or.inl (hsuffix item hsuffixItem)

private theorem Allocations.scanFreeIntervals_fst_eq_nil_of_starts_ge
    (items : List (ℕ × ℕ)) (row endRow : ℕ)
    (hstarts : ∀ item ∈ items, endRow ≤ item.1) :
    (scanFreeIntervals (some endRow) items row).1 = [] := by
  induction items with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      have hhead := hstarts head (by simp)
      simp only [scanFreeIntervals, hhead, decide_true, Bool.not_true]
      apply inductionHypothesis
      intro item hitem
      exact hstarts item (by simp [hitem])

private theorem Allocations.endsBefore_append_singleton
    {previous : List (ℕ × ℕ)} {head : ℕ × ℕ} {row : ℕ}
    (hprevious : EndsBefore previous row) :
    EndsBefore (previous ++ [head])
      (max row (head.1 + head.2)) := by
  intro item hitem
  rw [List.mem_append, List.mem_singleton] at hitem
  rcases hitem with hpast | rfl
  · exact (hprevious item hpast).trans (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

private theorem Allocations.scanFreeIntervals_spaces_fit
    (previous items : List (ℕ × ℕ)) (row : ℕ)
    (endBound : Option ℕ)
    (hvalid : (previous ++ items).Pairwise IntervalBefore)
    (hprevious : EndsBefore previous row)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1)
    {start length : ℕ} (hallows : SpaceAllows space start length) :
    ∀ allocated ∈ previous ++ items,
      RowIntervalsDisjoint start length allocated.1 allocated.2 := by
  cases endBound with
  | none =>
      induction items generalizing previous row with
      | nil => simp [scanFreeIntervals] at hspace
      | cons head rest inductionHypothesis =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace
          split at hspace
          next hgap =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · apply fits_of_before_and_after hprevious hallows.1
              intro item hitem
              exact hallows.2 head.1 rfl |>.trans
                (valid_head_start_le (valid_suffix hvalid) hitem)
            · intro allocated hallocated
              exact inductionHypothesis (previous := previous ++ [head])
                (row := max row (head.1 + head.2))
                (by simpa only [List.append_assoc] using hvalid)
                (endsBefore_append_singleton hprevious)
                htail allocated
                (by simpa only [List.append_assoc] using hallocated)
          next hnoGap =>
            intro allocated hallocated
            exact inductionHypothesis (previous := previous ++ [head])
              (row := max row (head.1 + head.2))
              (by simpa only [List.append_assoc] using hvalid)
              (endsBefore_append_singleton hprevious)
              hspace allocated
              (by simpa only [List.append_assoc] using hallocated)
  | some endRow =>
      induction items generalizing previous row with
      | nil => simp [scanFreeIntervals] at hspace
      | cons head rest inductionHypothesis =>
          by_cases hpast : endRow ≤ head.1
          · have hstarts : ∀ item ∈ head :: rest, endRow ≤ item.1 := by
              intro item hitem
              exact hpast.trans
                (valid_head_start_le (valid_suffix hvalid) hitem)
            rw [scanFreeIntervals_fst_eq_nil_of_starts_ge
              (head :: rest) row endRow hstarts] at hspace
            contradiction
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace
            split at hspace
            next hgap =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · apply fits_of_before_and_after hprevious hallows.1
                intro item hitem
                exact hallows.2 head.1 rfl |>.trans
                  (valid_head_start_le (valid_suffix hvalid) hitem)
              · intro allocated hallocated
                exact inductionHypothesis (previous := previous ++ [head])
                  (row := max row (head.1 + head.2))
                  (by simpa only [List.append_assoc] using hvalid)
                  (endsBefore_append_singleton hprevious)
                  htail allocated
                  (by simpa only [List.append_assoc] using hallocated)
            next hnoGap =>
              intro allocated hallocated
              exact inductionHypothesis (previous := previous ++ [head])
                (row := max row (head.1 + head.2))
                (by simpa only [List.append_assoc] using hvalid)
                (endsBefore_append_singleton hprevious)
                hspace allocated
                (by simpa only [List.append_assoc] using hallocated)

private theorem Allocations.row_le_scanFreeIntervals
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ) :
    row ≤ (scanFreeIntervals endBound items row).2 := by
  induction items generalizing row with
  | nil => exact le_rfl
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          exact (Nat.le_max_left _ _).trans (inductionHypothesis _)
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true]
            exact inductionHypothesis row
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            exact (Nat.le_max_left _ _).trans (inductionHypothesis _)

private theorem Allocations.scanFreeIntervals_boundary
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ) :
    ∀ item ∈ items,
      item.1 + item.2 ≤ (scanFreeIntervals endBound items row).2 ∨
        ∃ endRow, endBound = some endRow ∧ endRow ≤ item.1 := by
  intro item hitem
  induction items generalizing row with
  | nil => simp at hitem
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hitem
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          rcases hitem with heq | hrest
          · subst item
            exact Or.inl ((Nat.le_max_right row (head.1 + head.2)).trans
              (row_le_scanFreeIntervals rest
                (max row (head.1 + head.2)) none))
          · exact inductionHypothesis (max row (head.1 + head.2)) hrest
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true]
            rcases hitem with heq | hrest
            · subst item
              exact Or.inr ⟨endRow, rfl, hpast⟩
            · exact inductionHypothesis row hrest
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            rcases hitem with heq | hrest
            · subst item
              exact Or.inl (Nat.le_max_right row (head.1 + head.2) |>.trans
                (row_le_scanFreeIntervals rest
                  (max row (head.1 + head.2)) (some endRow)))
            · exact inductionHypothesis (max row (head.1 + head.2)) hrest

/-- Every interval admitted by `freeIntervals` is disjoint from all allocations. -/
theorem Allocations.freeIntervals_fits
    (allocations : Allocations) (start : ℕ) (endBound : Option ℕ)
    (hvalid : allocations.Valid)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ allocations.freeIntervals start endBound)
    {candidate length : ℕ}
    (hallows : SpaceAllows space candidate length) :
    allocations.Fits candidate length := by
  cases endBound with
  | none =>
      simp only [freeIntervals, List.mem_append,
        List.mem_singleton] at hspace
      rcases hspace with hscan | rfl
      · exact scanFreeIntervals_spaces_fit [] allocations.toList start none
          (by simpa [Valid] using hvalid) (by simp [EndsBefore]) hscan hallows
      · intro item hitem
        have hboundary :=
          scanFreeIntervals_boundary allocations.toList start none item hitem
        rcases hboundary with hbefore | ⟨_, hnone, _⟩
        · exact Or.inr (hbefore.trans hallows.1)
        · contradiction
  | some endRow =>
      simp only [freeIntervals] at hspace
      split at hspace
      next hfinal =>
        simp only [List.mem_append, List.mem_singleton] at hspace
        rcases hspace with hscan | rfl
        · exact scanFreeIntervals_spaces_fit [] allocations.toList start
            (some endRow) (by simpa [Valid] using hvalid)
            (by simp [EndsBefore]) hscan hallows
        · intro item hitem
          have hboundary := scanFreeIntervals_boundary allocations.toList
            start (some endRow) item hitem
          rcases hboundary with hbefore | ⟨foundEnd, heq, hafter⟩
          · exact Or.inr (hbefore.trans hallows.1)
          · simp only [Option.some.injEq] at heq
            subst foundEnd
            exact Or.inl ((hallows.2 endRow rfl).trans hafter)
      next hnoFinal =>
        exact scanFreeIntervals_spaces_fit [] allocations.toList start
          (some endRow) (by simpa [Valid] using hvalid)
          (by simp [EndsBefore]) hspace hallows

private theorem Allocations.scanFreeIntervals_end_le
    (items : List (ℕ × ℕ)) (row endRow : ℕ)
    {spaceStart spaceEnd : ℕ}
    (hspace : (spaceStart, some spaceEnd) ∈
      (scanFreeIntervals (some endRow) items row).1) :
    spaceEnd ≤ endRow := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      by_cases hpast : endRow ≤ head.1
      · simp only [scanFreeIntervals, hpast, decide_true,
          Bool.not_true] at hspace
        exact inductionHypothesis row hspace
      · simp only [scanFreeIntervals, hpast, decide_false,
          Bool.not_false, ↓reduceIte] at hspace
        split at hspace
        next hgap =>
          simp only [List.mem_cons, Prod.mk.injEq,
            Option.some.injEq] at hspace
          rcases hspace with ⟨rfl, rfl⟩ | htail
          · omega
          · exact inductionHypothesis _ htail
        next hnoGap =>
          exact inductionHypothesis _ hspace

/-- Every bounded free interval ends within the requested upper bound. -/
theorem Allocations.freeIntervals_end_le
    (allocations : Allocations) (start endRow : ℕ)
    {intervalStart intervalEnd : ℕ}
    (hinterval :
      (intervalStart, some intervalEnd) ∈
        allocations.freeIntervals start (some endRow)) :
    intervalEnd ≤ endRow := by
  simp only [Allocations.freeIntervals] at hinterval
  split at hinterval
  next hfinal =>
    simp only [List.mem_append, List.mem_singleton,
      Prod.mk.injEq, Option.some.injEq] at hinterval
    rcases hinterval with hscan | ⟨_, rfl⟩
    · exact scanFreeIntervals_end_le allocations.toList start endRow hscan
    · exact le_rfl
  next hnoFinal =>
    exact scanFreeIntervals_end_le allocations.toList start endRow hinterval

private theorem Allocations.scanFreeIntervals_start_le
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1) :
    row ≤ space.1 := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace
          split at hspace
          next hgap =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · exact le_rfl
            · exact (Nat.le_max_left _ _).trans
                (inductionHypothesis _ htail)
          next =>
            exact (Nat.le_max_left _ _).trans
              (inductionHypothesis _ hspace)
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true] at hspace
            exact inductionHypothesis row hspace
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace
            split at hspace
            next hgap =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · exact le_rfl
              · exact (Nat.le_max_left _ _).trans
                  (inductionHypothesis _ htail)
            next =>
              exact (Nat.le_max_left _ _).trans
                (inductionHypothesis _ hspace)

theorem Allocations.freeIntervals_start_le
    (allocations : Allocations) (start : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ allocations.freeIntervals start endBound) :
    start ≤ space.1 := by
  cases endBound with
  | none =>
      simp only [Allocations.freeIntervals, List.mem_append,
        List.mem_singleton] at hspace
      rcases hspace with hscan | rfl
      · exact scanFreeIntervals_start_le _ _ _ hscan
      · exact row_le_scanFreeIntervals _ _ _
  | some endRow =>
      simp only [Allocations.freeIntervals] at hspace
      split at hspace
      next =>
        simp only [List.mem_append, List.mem_singleton] at hspace
        rcases hspace with hscan | rfl
        · exact scanFreeIntervals_start_le _ _ _ hscan
        · exact row_le_scanFreeIntervals _ _ _
      next => exact scanFreeIntervals_start_le _ _ _ hspace

private theorem Allocations.scanFreeIntervals_contains_fitting_candidate
    (items : List (ℕ × ℕ)) (row candidate length : ℕ)
    (endBound : Option ℕ)
    (hvalid : items.Pairwise IntervalBefore)
    (hrow : row ≤ candidate)
    (hlength : 0 < length)
    (hfits : ∀ allocated ∈ items,
      RowIntervalsDisjoint candidate length allocated.1 allocated.2) :
    (∃ space ∈ (scanFreeIntervals endBound items row).1,
      SpaceAllows space candidate length) ∨
      (scanFreeIntervals endBound items row).2 ≤ candidate := by
  induction items generalizing row with
  | nil => exact Or.inr hrow
  | cons head rest inductionHypothesis =>
      have hrestValid := List.pairwise_cons.mp hvalid |>.2
      have hrestFits : ∀ allocated ∈ rest,
          RowIntervalsDisjoint candidate length allocated.1 allocated.2 := by
        intro allocated hallocated
        exact hfits allocated (by simp [hallocated])
      have hheadFits := hfits head (by simp)
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          rcases hheadFits with hcandidateBefore | hheadBefore
          · have hgap : row < head.1 := by omega
            rw [if_pos hgap]
            exact Or.inl ⟨(row, some head.1), by simp,
              ⟨hrow, by intro stop hstop; simp_all⟩⟩
          · have hnext : max row (head.1 + head.2) ≤ candidate := by omega
            have htail := inductionHypothesis
              (max row (head.1 + head.2)) hrestValid hnext hrestFits
            split
            · rcases htail with ⟨space, hspace, hallows⟩ | hend
              · exact Or.inl ⟨space, by simp [hspace], hallows⟩
              · exact Or.inr hend
            · exact htail
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true, Bool.not_true]
            exact inductionHypothesis row hrestValid hrow hrestFits
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            rcases hheadFits with hcandidateBefore | hheadBefore
            · have hgap : row < head.1 := by omega
              rw [if_pos hgap]
              exact Or.inl ⟨(row, some head.1), by simp,
                ⟨hrow, by intro stop hstop; simp_all⟩⟩
            · have hnext : max row (head.1 + head.2) ≤ candidate := by omega
              have htail := inductionHypothesis
                (max row (head.1 + head.2)) hrestValid hnext hrestFits
              split
              · rcases htail with ⟨space, hspace, hallows⟩ | hend
                · exact Or.inl ⟨space, by simp [hspace], hallows⟩
                · exact Or.inr hend
              · exact htail

/-- Every fitting candidate belongs to one of the free intervals enumerated from
an earlier search boundary. This is the completeness counterpart of
`freeIntervals_fits`. -/
theorem Allocations.exists_freeInterval_of_fits
    (allocations : Allocations) (start candidate length : ℕ)
    (endBound : Option ℕ)
    (hvalid : allocations.Valid) (hstart : start ≤ candidate)
    (hlength : 0 < length) (hfits : allocations.Fits candidate length)
    (hbound : ∀ stop, endBound = some stop → candidate + length ≤ stop) :
    ∃ space ∈ allocations.freeIntervals start endBound,
      SpaceAllows space candidate length := by
  have hscan := scanFreeIntervals_contains_fitting_candidate
    allocations.toList start candidate length endBound
    (by simpa [Valid] using hvalid) hstart hlength hfits
  cases endBound with
  | none =>
      rcases hscan with ⟨space, hspace, hallows⟩ | hend
      · exact ⟨space, by simp [freeIntervals, hspace], hallows⟩
      · refine ⟨((scanFreeIntervals none allocations.toList start).2, none),
          by simp [freeIntervals], ⟨hend, by simp⟩⟩
  | some endRow =>
      have hcandidateEnd := hbound endRow rfl
      rcases hscan with ⟨space, hspace, hallows⟩ | hend
      · by_cases hfinal :
            (scanFreeIntervals (some endRow) allocations.toList start).2 <
              endRow
        · exact ⟨space, by simp [freeIntervals, hfinal, hspace], hallows⟩
        · exact ⟨space, by simp [freeIntervals, hfinal, hspace], hallows⟩
      · have hfinal :
            (scanFreeIntervals (some endRow) allocations.toList start).2 <
              endRow := by omega
        refine ⟨((scanFreeIntervals (some endRow)
              allocations.toList start).2, some endRow),
            by simp [freeIntervals, hfinal], ⟨hend, ?_⟩⟩
        intro stop hstop
        simp only [Option.some.injEq] at hstop
        subst stop
        exact hcandidateEnd

/-- Earlier free intervals end before later free intervals begin. -/
def Allocations.SpaceBefore
    (left right : ℕ × Option ℕ) : Prop :=
  ∃ stop, left.2 = some stop ∧ stop ≤ right.1

private theorem Allocations.scanFreeIntervals_space_bounded
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1) :
    ∃ stop, space.2 = some stop := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace
          split at hspace
          next =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · exact ⟨head.1, rfl⟩
            · exact inductionHypothesis _ htail
          next => exact inductionHypothesis _ hspace
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true] at hspace
            exact inductionHypothesis row hspace
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace
            split at hspace
            next =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · exact ⟨head.1, rfl⟩
              · exact inductionHypothesis _ htail
            next => exact inductionHypothesis _ hspace

private theorem Allocations.scanFreeIntervals_space_end_le
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1) :
    ∀ stop, space.2 = some stop →
      stop ≤ (scanFreeIntervals endBound items row).2 := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace ⊢
          split at hspace
          next hgap =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · intro stop hstop
              simp only [Option.some.injEq] at hstop
              subst stop
              exact (Nat.le_add_right head.1 head.2).trans
                ((Nat.le_max_right row (head.1 + head.2)).trans
                  (row_le_scanFreeIntervals rest _ none))
            · exact inductionHypothesis _ htail
          next => exact inductionHypothesis _ hspace
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true] at hspace ⊢
            exact inductionHypothesis row hspace
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace ⊢
            split at hspace
            next hgap =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · intro stop hstop
                simp only [Option.some.injEq] at hstop
                subst stop
                exact (Nat.le_add_right head.1 head.2).trans
                  ((Nat.le_max_right row (head.1 + head.2)).trans
                    (row_le_scanFreeIntervals rest _ (some endRow)))
              · exact inductionHypothesis _ htail
            next => exact inductionHypothesis _ hspace

private theorem Allocations.scanFreeIntervals_pairwise
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ) :
    (scanFreeIntervals endBound items row).1.Pairwise SpaceBefore := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals]
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          split
          next hgap =>
            rw [List.pairwise_cons]
            constructor
            · intro space hspace
              exact ⟨head.1, rfl,
                (Nat.le_add_right head.1 head.2).trans
                  ((Nat.le_max_right row (head.1 + head.2)).trans
                    (scanFreeIntervals_start_le rest _ none hspace))⟩
            · exact inductionHypothesis _
          next => exact inductionHypothesis _
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true, Bool.not_true]
            exact inductionHypothesis row
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            split
            next hgap =>
              rw [List.pairwise_cons]
              constructor
              · intro space hspace
                exact ⟨head.1, rfl,
                  (Nat.le_add_right head.1 head.2).trans
                    ((Nat.le_max_right row (head.1 + head.2)).trans
                      (scanFreeIntervals_start_le rest _ (some endRow) hspace))⟩
              · exact inductionHypothesis _
            next => exact inductionHypothesis _

/-- The free-space iterator enumerates disjoint spaces from low rows to high rows. -/
theorem Allocations.freeIntervals_pairwise
    (allocations : Allocations) (start : ℕ) (endBound : Option ℕ) :
    (allocations.freeIntervals start endBound).Pairwise SpaceBefore := by
  cases endBound with
  | none =>
      simp only [freeIntervals]
      rw [List.pairwise_append]
      exact ⟨scanFreeIntervals_pairwise _ _ _, by simp, by
        intro left hleft right hright
        simp only [List.mem_singleton] at hright
        subst right
        obtain ⟨stop, hstop⟩ := scanFreeIntervals_space_bounded _ _ _ hleft
        exact ⟨stop, hstop,
          scanFreeIntervals_space_end_le _ _ _ hleft stop hstop⟩⟩
  | some endRow =>
      simp only [freeIntervals]
      split
      next hfinal =>
        rw [List.pairwise_append]
        exact ⟨scanFreeIntervals_pairwise _ _ _, by simp, by
          intro left hleft right hright
          simp only [List.mem_singleton] at hright
          subst right
          obtain ⟨stop, hstop⟩ := scanFreeIntervals_space_bounded _ _ _ hleft
          exact ⟨stop, hstop,
            scanFreeIntervals_space_end_le _ _ _ hleft stop hstop⟩⟩
      next => exact scanFreeIntervals_pairwise _ _ _

private theorem Allocations.scanFreeIntervals_bounded
    (items : List (ℕ × ℕ)) (row endRow : ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈
      (scanFreeIntervals (some endRow) items row).1) :
    ∃ stop, space.2 = some stop := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      by_cases hpast : endRow ≤ head.1
      · simp only [scanFreeIntervals, hpast, decide_true,
          Bool.not_true] at hspace
        exact inductionHypothesis row hspace
      · simp only [scanFreeIntervals, hpast, decide_false,
          Bool.not_false, ↓reduceIte] at hspace
        split at hspace
        next =>
          simp only [List.mem_cons] at hspace
          rcases hspace with rfl | htail
          · exact ⟨head.1, rfl⟩
          · exact inductionHypothesis _ htail
        next => exact inductionHypothesis _ hspace

theorem Allocations.freeIntervals_bounded
    (allocations : Allocations) (start endRow : ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ allocations.freeIntervals start (some endRow)) :
    ∃ stop, space.2 = some stop := by
  simp only [Allocations.freeIntervals] at hspace
  split at hspace
  next =>
    simp only [List.mem_append, List.mem_singleton] at hspace
    rcases hspace with hscan | rfl
    · exact scanFreeIntervals_bounded _ _ _ hscan
    · exact ⟨endRow, rfl⟩
  next => exact scanFreeIntervals_bounded _ _ _ hspace

/-- The circuit's per-column allocations. -/
abbrev CircuitAllocations := Std.HashMap RegionColumn Allocations

/-- Every per-column allocation sequence satisfies its ordering invariant. -/
def CircuitAllocations.Valid (allocations : CircuitAllocations) : Prop :=
  ∀ column, (allocations.getD column #[]).Valid

/-- Every allocation recorded before remains recorded after an update. -/
def CircuitAllocations.Extends
    (before after : CircuitAllocations) : Prop :=
  ∀ column interval,
    interval ∈ (before.getD column #[]).toList →
      interval ∈ (after.getD column #[]).toList

/-- An update leaves columns outside the given footprint unchanged. -/
def CircuitAllocations.SameOutside
    (columns : List RegionColumn)
    (before after : CircuitAllocations) : Prop :=
  ∀ column, column ∉ columns →
    after.getD column #[] = before.getD column #[]

/-- An allocation map records one placed interval in every listed column. -/
def CircuitAllocations.Records
    (allocations : CircuitAllocations) (columns : List RegionColumn)
    (start length : ℕ) : Prop :=
  ∀ column ∈ columns,
    (start, length) ∈ (allocations.getD column #[]).toList

/-- Two allocation maps agree on the columns observable by a region. -/
def CircuitAllocations.AgreesOn (left right : CircuitAllocations)
    (columns : List RegionColumn) : Prop :=
  ∀ column, column ∈ columns →
    left.getD column #[] = right.getD column #[]

/-- Allocation maps with the same observable interval sequence in every column. -/
def CircuitAllocations.Equivalent
    (left right : CircuitAllocations) : Prop :=
  ∀ column, left.getD column #[] = right.getD column #[]

theorem CircuitAllocations.Equivalent.refl
    (allocations : CircuitAllocations) : allocations.Equivalent allocations := by
  intro column
  rfl

theorem CircuitAllocations.Equivalent.symm
    {left right : CircuitAllocations} (h : left.Equivalent right) :
    right.Equivalent left := by
  intro column
  exact (h column).symm

theorem CircuitAllocations.Equivalent.trans
    {left middle right : CircuitAllocations}
    (hleft : left.Equivalent middle) (hright : middle.Equivalent right) :
    left.Equivalent right := by
  intro column
  exact (hleft column).trans (hright column)

theorem CircuitAllocations.Equivalent.agreesOn
    {left right : CircuitAllocations} (h : left.Equivalent right)
    (columns : List RegionColumn) : left.AgreesOn right columns := by
  intro column _
  exact h column

theorem CircuitAllocations.AgreesOn.mono
    {left right : CircuitAllocations} {inner outer : List RegionColumn}
    (h : left.AgreesOn right outer) (hsubset : inner ⊆ outer) :
    left.AgreesOn right inner := by
  intro column hcolumn
  exact h column (hsubset hcolumn)

theorem CircuitAllocations.AgreesOn.insert
    {left right : CircuitAllocations} {columns : List RegionColumn}
    (h : left.AgreesOn right columns) (column : RegionColumn)
    {leftValue rightValue : Allocations} (hvalue : leftValue = rightValue) :
    CircuitAllocations.AgreesOn (left.insert column leftValue)
      (right.insert column rightValue) columns := by
  intro candidate hcandidate
  rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert]
  split
  next => rw [hvalue]
  next => exact h candidate hcandidate

theorem CircuitAllocations.Valid.empty :
    (∅ : CircuitAllocations).Valid := by
  intro column
  simp [Allocations.Valid]

theorem CircuitAllocations.Extends.refl
    (allocations : CircuitAllocations) :
    allocations.Extends allocations := by
  intro column interval hinterval
  exact hinterval

theorem CircuitAllocations.Extends.trans
    {first second third : CircuitAllocations}
    (hfirst : first.Extends second) (hsecond : second.Extends third) :
    first.Extends third := by
  intro column interval hinterval
  exact hsecond column interval (hfirst column interval hinterval)

theorem CircuitAllocations.Valid.insertSame
    {allocations : CircuitAllocations} (hvalid : allocations.Valid)
    (column : RegionColumn) :
    CircuitAllocations.Valid
      (allocations.insert column (allocations.getD column #[])) := by
  intro candidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact hvalid column
  · exact hvalid candidate

theorem CircuitAllocations.Extends.insertSame
    (allocations : CircuitAllocations) (column : RegionColumn) :
    allocations.Extends
      (allocations.insert column (allocations.getD column #[])) := by
  intro candidate interval hinterval
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact hinterval
  · exact hinterval

theorem CircuitAllocations.SameOutside.insertSame
    (allocations : CircuitAllocations) (column : RegionColumn) :
    allocations.SameOutside [column]
      (allocations.insert column (allocations.getD column #[])) := by
  intro candidate hcandidate
  simp only [List.mem_singleton] at hcandidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    exact False.elim (hcandidate (beq_iff_eq.mp heq).symm)
  next => rfl

theorem CircuitAllocations.Valid.insertAllocation
    {allocations : CircuitAllocations} (hvalid : allocations.Valid)
    (column : RegionColumn) (start length : ℕ)
    (hfits : (allocations.getD column #[]).Fits start length)
    (hlength : 0 < length) :
    CircuitAllocations.Valid
      (allocations.insert column
        ((allocations.getD column #[]).insert start length)) := by
  intro candidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact Allocations.Valid.insert _ _ _
      (hvalid column) hfits hlength
  next hne => exact hvalid candidate

theorem CircuitAllocations.Extends.insertAllocation
    (allocations : CircuitAllocations) (column : RegionColumn)
    (start length : ℕ) :
    allocations.Extends
      (allocations.insert column
        ((allocations.getD column #[]).insert start length)) := by
  intro candidate interval hinterval
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact Allocations.mem_insert_of_mem _ _ _ hinterval
  next hne => exact hinterval

theorem CircuitAllocations.SameOutside.insertAllocation
    (allocations : CircuitAllocations) (column : RegionColumn)
    (start length : ℕ) :
    allocations.SameOutside [column]
      (allocations.insert column
        ((allocations.getD column #[]).insert start length)) := by
  intro candidate hcandidate
  simp only [List.mem_singleton] at hcandidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    exact False.elim (hcandidate (beq_iff_eq.mp heq).symm)
  next => rfl

mutual

/-- `first_fit_region` (`strategy.rs:107-161`): find the earliest common start row for all of
`cols` (already `RegionColumn::Ord`-sorted), inserting the placed interval into every column.
Returns the start row (`none` if unplaceable) and the updated allocations. `slack` bounds how
far the start may move (`end = start + region_length + slack`); the recursion threads it.

Total via explicit fuel: the Rust recursion consumes exactly one column per level
(`region_columns.split_first()`, `strategy.rs:114`), so `fuel = cols.length` at the top call
(`slotIn`) provably suffices. The `fuel = 0, cols ≠ []` arm is unreachable; it returns
`none` ("no placement"), which the fixture-equality checks would surface loudly. -/
def firstFit (fuel : ℕ) (colAllocs : CircuitAllocations) (cols : List RegionColumn)
    (regionLen : ℕ) (start : ℕ) (slack : Option ℕ) : Option ℕ × CircuitAllocations :=
  match fuel, cols with
  | _, [] => (some start, colAllocs)
  | 0, _ :: _ => (none, colAllocs)
  | fuel + 1, c :: rest =>
    let endBound := slack.map (fun s => start + regionLen + s)
    let cAlloc := colAllocs.getD c #[]
    -- `entry(*c).or_default()` — ensure the key exists (so it shows up in `first_unassigned_row`).
    let colAllocs := colAllocs.insert c cAlloc
    trySpaces fuel colAllocs c rest regionLen (cAlloc.freeIntervals start endBound)
termination_by (fuel, 0, 0)

/-- The `for space in …free_intervals` loop of `first_fit_region` (`strategy.rs:121-157`):
try each free interval of column `c` in order; a space with enough room recurses into the
remaining columns — success inserts the placed interval into `c` and returns
(`strategy.rs:142-154`), failure keeps the (mutated) allocations and moves to the next
space. The spaces are computed ONCE from the state at `firstFit` entry (Rust iterates a
`.clone()`, `strategy.rs:119-124`), so inner mutations do not re-enter the iteration. -/
def trySpaces (fuel : ℕ) (colAllocs : CircuitAllocations) (c : RegionColumn)
    (rest : List RegionColumn) (regionLen : ℕ) (spaces : List (ℕ × Option ℕ)) :
    Option ℕ × CircuitAllocations :=
  match spaces with
  | [] => (none, colAllocs)
  | (sStart, sEnd) :: more =>
    let sSlack : Option ℤ := sEnd.map (fun e => (e : ℤ) - (sStart : ℤ) - (regionLen : ℤ))
    let ok : Bool := match sSlack with | some ss => decide (ss ≥ 0) | none => true
    if ok then
      let recSlack : Option ℕ := sSlack.map Int.toNat
      let (row?, m') := firstFit fuel colAllocs rest regionLen sStart recSlack
      match row? with
      | some row =>
        let cA := (m'.getD c #[]).insert row regionLen
        (some row, m'.insert c cA)
      | none => trySpaces fuel m' c rest regionLen more
    else
      trySpaces fuel colAllocs c rest regionLen more
termination_by (fuel, 1, spaces.length)

end

/-- Once fuel covers every remaining column, its exact value is unobservable. -/
theorem firstFit_eq_of_sufficient_fuel
    (columns : List RegionColumn) :
    ∀ (leftFuel rightFuel : ℕ) (allocations : CircuitAllocations)
      (length start : ℕ) (slack : Option ℕ),
      columns.length ≤ leftFuel → columns.length ≤ rightFuel →
      firstFit leftFuel allocations columns length start slack =
        firstFit rightFuel allocations columns length start slack := by
  induction columns with
  | nil =>
      intro leftFuel rightFuel allocations length start slack _ _
      simp [firstFit]
  | cons column rest inductionHypothesis =>
      intro leftFuel rightFuel allocations length start slack
        hleftFuel hrightFuel
      cases leftFuel with
      | zero => simp at hleftFuel
      | succ leftFuel =>
          cases rightFuel with
          | zero => simp at hrightFuel
          | succ rightFuel =>
              have hleftRest : rest.length ≤ leftFuel := by
                simpa using hleftFuel
              have hrightRest : rest.length ≤ rightFuel := by
                simpa using hrightFuel
              let initialized := allocations.insert column
                (allocations.getD column #[])
              let spaces := (allocations.getD column #[]).freeIntervals start
                (slack.map fun available => start + length + available)
              have compareSpaces : ∀ (remaining : List (ℕ × Option ℕ))
                  (current : CircuitAllocations),
                  trySpaces leftFuel current column rest length remaining =
                    trySpaces rightFuel current column rest length remaining := by
                intro remaining
                induction remaining with
                | nil =>
                    intro current
                    simp [trySpaces]
                | cons space more spacesInduction =>
                    rcases space with ⟨spaceStart, spaceEnd⟩
                    intro current
                    let available : Option ℤ := spaceEnd.map fun stop =>
                      (stop : ℤ) - spaceStart - length
                    let ok : Bool := match available with
                      | some value => decide (value ≥ 0)
                      | none => true
                    by_cases hok : ok = true
                    · have hrecursive := inductionHypothesis leftFuel rightFuel
                        current length spaceStart (available.map Int.toNat)
                        hleftRest hrightRest
                      generalize hleft : firstFit leftFuel current rest length
                        spaceStart (available.map Int.toNat) = leftResult
                          at hrecursive
                      have hright := hrecursive.symm
                      rcases leftResult with ⟨row, updated⟩
                      cases row with
                      | some row =>
                          simp only [trySpaces]
                          change ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations) =
                            ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations)
                          simp only [if_pos hok]
                          have havailable :
                              (spaceEnd.map fun stop =>
                                (stop : ℤ) - spaceStart - length) =
                                available := rfl
                          rw [havailable, hleft, hright]
                      | none =>
                          have hnext := spacesInduction updated
                          simp only [trySpaces]
                          change ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations) =
                            ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations)
                          simp only [if_pos hok]
                          have havailable :
                              (spaceEnd.map fun stop =>
                                (stop : ℤ) - spaceStart - length) =
                                available := rfl
                          rw [havailable, hleft, hright]
                          exact hnext
                    · have hnext := spacesInduction current
                      simp only [trySpaces]
                      change ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations) =
                        ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations)
                      simpa only [if_neg hok] using hnext
              simp only [firstFit]
              exact compareSpaces spaces initialized

/-- A successful recursive placement remains inside its initial search window. -/
def Within (start : ℕ) (slack : Option ℕ)
    (length row : ℕ) : Prop :=
  start ≤ row ∧
    ∀ available, slack = some available →
      row + length ≤ start + length + available

/-- The allocation facts preserved by either a successful or failed first-fit search. -/
structure PlacementLaw
    (before : CircuitAllocations) (columns : List RegionColumn)
    (length : ℕ) (result : Option ℕ × CircuitAllocations) : Prop where
  valid : result.2.Valid
  preserves : before.Extends result.2
  sameOutside : before.SameOutside columns result.2
  records : ∀ row, result.1 = some row →
    result.2.Records columns row length
  fits : ∀ row, result.1 = some row →
    ∀ column ∈ columns,
      (before.getD column #[]).Fits row length

private def FirstFitLaw
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  allocations.Valid → columns.Nodup → 0 < length →
    let result := firstFit fuel allocations columns length start slack
    PlacementLaw allocations columns length result ∧
      ∀ row, result.1 = some row → Within start slack length row

private def TrySpacesLaw
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length : ℕ) (spaces : List (ℕ × Option ℕ)) : Prop :=
  allocations.Valid → rest.Nodup → column ∉ rest → 0 < length →
    (∀ space ∈ spaces, ∀ row,
      Allocations.SpaceAllows space row length →
        (allocations.getD column #[]).Fits row length) →
    let result := trySpaces fuel allocations column rest length spaces
    PlacementLaw allocations (column :: rest) length result ∧
      ∀ row, result.1 = some row →
        ∃ space ∈ spaces,
          Allocations.SpaceAllows space row length

theorem within_space_of_ok
    (spaceStart : ℕ) (spaceEnd : Option ℕ) (length row : ℕ)
    (hok : (match spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length with
      | some available => decide (available ≥ 0)
      | none => true) = true)
    (hwithin : Within spaceStart
      ((spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length).map Int.toNat)
      length row) :
    Allocations.SpaceAllows (spaceStart, spaceEnd) row length := by
  constructor
  · exact hwithin.1
  · intro stop hstop
    change spaceEnd = some stop at hstop
    subst spaceEnd
    change decide
      (((stop : ℤ) - spaceStart - length) ≥ 0) = true at hok
    rw [decide_eq_true_eq] at hok
    have hbound := hwithin.2
      ((stop : ℤ) - spaceStart - length).toNat rfl
    have hcast :
        (↑(((stop : ℤ) - spaceStart - length).toNat) : ℤ) =
          (stop : ℤ) - spaceStart - length :=
      Int.toNat_of_nonneg hok
    omega

/-- First-fit preserves allocation validity and records any successful placement. -/
theorem firstFit_law
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) :
    FirstFitLaw fuel allocations columns length start slack := by
  apply firstFit.induct (regionLen := length)
    (motive1 := fun fuel allocations columns start slack =>
      FirstFitLaw fuel allocations columns length start slack)
    (motive2 := fun fuel allocations column rest spaces =>
      TrySpacesLaw fuel allocations column rest length spaces)
  all_goals simp only [FirstFitLaw, TrySpacesLaw]
  case case1 =>
    intro fuel allocations start slack hvalid hnodup hlength
    simp only [firstFit]
    constructor
    · exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          sameOutside := by intro column hcolumn; rfl
          records := by
            intro row hrow column hcolumn
            simp at hcolumn
          fits := by
            intro row hrow column hcolumn
            simp at hcolumn }
    · intro row hrow
      simp only [Option.some.injEq] at hrow
      subst row
      exact ⟨le_rfl, by intro available havailable; omega⟩
  case case2 =>
    intro allocations start slack head tail hvalid hnodup hlength
    simp only [firstFit]
    constructor
    · exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          sameOutside := by intro column hcolumn; rfl
          records := by simp
          fits := by simp }
    · simp
  case case3 =>
    intro allocations start slack fuel column rest inductionHypothesis
      hvalid hnodup hlength
    have hrestNodup := List.nodup_cons.mp hnodup |>.2
    have hcolumnRest := List.nodup_cons.mp hnodup |>.1
    let initialized :=
      allocations.insert column (allocations.getD column #[])
    have hinitializedValid : CircuitAllocations.Valid initialized :=
      CircuitAllocations.Valid.insertSame hvalid column
    have hspaceSafety :
        ∀ space ∈ (allocations.getD column #[]).freeIntervals start
            (slack.map fun available => start + length + available),
          ∀ row, Allocations.SpaceAllows space row length →
            (initialized.getD column #[]).Fits row length := by
      intro space hspace row hallows
      have hfits := Allocations.freeIntervals_fits
        (allocations.getD column #[]) start
        (slack.map fun available => start + length + available)
        (hvalid column) hspace hallows
      simpa [initialized, Std.HashMap.getD_insert] using hfits
    obtain ⟨hlaw, hwitness⟩ := inductionHypothesis
      hinitializedValid hrestNodup hcolumnRest hlength hspaceSafety
    simp only [firstFit]
    constructor
    · refine
        { valid := hlaw.valid
          preserves := ?_
          sameOutside := ?_
          records := hlaw.records
          fits := ?_ }
      · exact (CircuitAllocations.Extends.insertSame allocations column).trans
          hlaw.preserves
      · intro candidate hcandidate
        have hresult := hlaw.sameOutside candidate hcandidate
        rw [hresult]
        exact CircuitAllocations.SameOutside.insertSame allocations column
          candidate (by
            intro heq
            apply hcandidate
            simp only [List.mem_cons]
            exact Or.inl (by simpa using heq))
      · intro row hrow candidate hcandidate
        have hfits := hlaw.fits row hrow candidate hcandidate
        change (initialized.getD candidate #[]).Fits row length at hfits
        dsimp only [initialized] at hfits
        rw [Std.HashMap.getD_insert] at hfits
        split at hfits
        next heq =>
          have : column = candidate := beq_iff_eq.mp heq
          subst candidate
          exact hfits
        next => exact hfits
    · intro row hrow
      obtain ⟨space, hspace, hallows⟩ := hwitness row hrow
      constructor
      · exact (Allocations.freeIntervals_start_le _ _ _ hspace).trans
          hallows.1
      · intro available havailable
        subst slack
        simp only [Option.map_some] at hspace
        obtain ⟨stop, hstop⟩ :=
          Allocations.freeIntervals_bounded _ _ _ hspace
        rcases space with ⟨spaceStart, spaceEnd⟩
        simp only at hstop
        subst spaceEnd
        exact (hallows.2 stop rfl).trans
          (Allocations.freeIntervals_end_le _ _ _ hspace)
  case case4 =>
    intro fuel allocations column rest hvalid hnodup hcolumn hlength
      hspaceSafety
    simp only [trySpaces]
    constructor
    · exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          sameOutside := by intro candidate hcandidate; rfl
          records := by simp
          fits := by simp }
    · simp
  case case5 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations row hrecursive inductionHypothesis
      hvalid hnodup hcolumn hlength hspaceSafety
    obtain ⟨hrecursiveLaw, hrecursiveWithin⟩ :=
      inductionHypothesis hvalid hnodup hlength
    rw [hrecursive] at hrecursiveLaw hrecursiveWithin
    have hallows := within_space_of_ok spaceStart spaceEnd length row hok
      (hrecursiveWithin row rfl)
    have hfitsOriginal := hspaceSafety (spaceStart, spaceEnd)
      (by simp) row hallows
    have hcolumnSame := hrecursiveLaw.sameOutside column hcolumn
    have hfitsRecursive :
        (recursiveAllocations.getD column #[]).Fits row length := by
      rw [hcolumnSame]
      exact hfitsOriginal
    let resultAllocations := recursiveAllocations.insert column
      ((recursiveAllocations.getD column #[]).insert row length)
    have hresultValid : CircuitAllocations.Valid resultAllocations :=
      CircuitAllocations.Valid.insertAllocation hrecursiveLaw.valid
        column row length hfitsRecursive hlength
    have hinsertExtends := CircuitAllocations.Extends.insertAllocation
      recursiveAllocations column row length
    simp only [trySpaces, hok, if_true, hrecursive]
    constructor
    · refine
        { valid := hresultValid
          preserves := hrecursiveLaw.preserves.trans hinsertExtends
          sameOutside := ?_
          records := ?_
          fits := ?_ }
      · intro candidate hcandidate
        have hinsertSame :=
          CircuitAllocations.SameOutside.insertAllocation
            recursiveAllocations column row length candidate
            (by
              intro heq
              apply hcandidate
              simp only [List.mem_cons]
              exact Or.inl (by simpa using heq))
        rw [hinsertSame]
        exact hrecursiveLaw.sameOutside candidate (by
          intro hrest
          apply hcandidate
          simp [hrest])
      · intro foundRow hfound
        have : foundRow = row := Option.some.inj hfound.symm
        subst foundRow
        intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | hrest
        · rw [Std.HashMap.getD_insert, if_pos]
          · exact Allocations.mem_insert _ _ _
          · simp
        · exact hinsertExtends candidate (row, length)
            (hrecursiveLaw.records row rfl candidate hrest)
      · intro foundRow hfound candidate hcandidate
        have : foundRow = row := Option.some.inj hfound.symm
        subst foundRow
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | hrest
        · exact hfitsOriginal
        · exact hrecursiveLaw.fits row rfl candidate hrest
    · intro foundRow hfound
      have : foundRow = row := Option.some.inj hfound.symm
      subst foundRow
      exact ⟨(spaceStart, spaceEnd), by simp, hallows⟩
  case case6 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations hrecursive firstInduction spacesInduction
      hvalid hnodup hcolumn hlength hspaceSafety
    obtain ⟨hrecursiveLaw, hrecursiveWithin⟩ :=
      firstInduction hvalid hnodup hlength
    rw [hrecursive] at hrecursiveLaw hrecursiveWithin
    have hcolumnSame := hrecursiveLaw.sameOutside column hcolumn
    have hremainingSafety :
        ∀ space ∈ more, ∀ row,
          Allocations.SpaceAllows space row length →
            (recursiveAllocations.getD column #[]).Fits row length := by
      intro space hspace row hallows
      rw [hcolumnSame]
      exact hspaceSafety space (by simp [hspace]) row hallows
    obtain ⟨hremainingLaw, hremainingWitness⟩ :=
      spacesInduction hrecursiveLaw.valid hnodup hcolumn hlength
        hremainingSafety
    simp only [trySpaces, hok, if_true, hrecursive]
    constructor
    · refine
        { valid := hremainingLaw.valid
          preserves := hrecursiveLaw.preserves.trans
            hremainingLaw.preserves
          sameOutside := ?_
          records := hremainingLaw.records
          fits := ?_ }
      · intro candidate hcandidate
        rw [hremainingLaw.sameOutside candidate hcandidate]
        apply hrecursiveLaw.sameOutside candidate
        intro hrest
        apply hcandidate
        simp [hrest]
      · intro row hrow candidate hcandidate
        have hfits := hremainingLaw.fits row hrow candidate hcandidate
        intro interval hinterval
        exact hfits interval
          (hrecursiveLaw.preserves candidate interval hinterval)
    · intro row hrow
      obtain ⟨space, hspace, hallows⟩ :=
        hremainingWitness row hrow
      exact ⟨space, by simp [hspace], hallows⟩
  case case7 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      inductionHypothesis hvalid hnodup hcolumn hlength hspaceSafety
    obtain ⟨hlaw, hwitness⟩ := inductionHypothesis
      hvalid hnodup hcolumn hlength (by
        intro space hspace row hallows
        exact hspaceSafety space (by simp [hspace]) row hallows)
    simp only [trySpaces, hok]
    exact ⟨hlaw, by
      intro row hrow
      obtain ⟨space, hspace, hallows⟩ := hwitness row hrow
      exact ⟨space, by simp [hspace], hallows⟩⟩

/-- A first-fit search changes a participating column by exactly one insertion on
success, and leaves every observable allocation unchanged on failure. -/
def PlacementEffect
    (before : CircuitAllocations) (columns : List RegionColumn)
    (length : ℕ) (result : Option ℕ × CircuitAllocations) : Prop :=
  ∀ column,
    result.2.getD column #[] =
      match result.1 with
      | none => before.getD column #[]
      | some row =>
          if column ∈ columns then
            (before.getD column #[]).insert row length
          else before.getD column #[]

theorem PlacementEffect.equivalent_before_of_none
    {before : CircuitAllocations} {columns : List RegionColumn}
    {length : ℕ} {result : Option ℕ × CircuitAllocations}
    (heffect : PlacementEffect before columns length result)
    (hresult : result.1 = none) : result.2.Equivalent before := by
  intro column
  rw [heffect column, hresult]

private def FirstFitEffect
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  allocations.Valid → columns.Nodup → 0 < length →
    PlacementEffect allocations columns length
      (firstFit fuel allocations columns length start slack)

private def TrySpacesEffect
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length : ℕ) (spaces : List (ℕ × Option ℕ)) : Prop :=
  allocations.Valid → rest.Nodup → column ∉ rest → 0 < length →
    PlacementEffect allocations (column :: rest) length
      (trySpaces fuel allocations column rest length spaces)

/-- Exact first-fit allocation effect. This proposition is intentionally separate
from `PlacementLaw`: consumers that only need safety do not pay to normalize the
algorithm's exact update. -/
theorem firstFit_effect
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) :
    FirstFitEffect fuel allocations columns length start slack := by
  apply firstFit.induct (regionLen := length)
    (motive1 := fun fuel allocations columns start slack =>
      FirstFitEffect fuel allocations columns length start slack)
    (motive2 := fun fuel allocations column rest spaces =>
      TrySpacesEffect fuel allocations column rest length spaces)
  all_goals simp only [FirstFitEffect, TrySpacesEffect]
  case case1 =>
    intro fuel allocations start slack _ _ _ column
    simp [firstFit]
  case case2 =>
    intro allocations start slack head tail _ _ _ column
    simp [firstFit]
  case case3 =>
    intro allocations start slack fuel column rest inductionHypothesis
      hvalid hnodup hlength
    have hrestNodup := List.nodup_cons.mp hnodup |>.2
    have hcolumnRest := List.nodup_cons.mp hnodup |>.1
    let initialized :=
      allocations.insert column (allocations.getD column #[])
    have hinitializedValid : CircuitAllocations.Valid initialized :=
      CircuitAllocations.Valid.insertSame hvalid column
    have heffect := inductionHypothesis hinitializedValid hrestNodup
      hcolumnRest hlength
    simp only [firstFit]
    intro candidate
    have hinitialized :
        initialized.getD candidate #[] = allocations.getD candidate #[] := by
      simp only [initialized, Std.HashMap.getD_insert]
      split <;> rename_i heq
      · exact congrArg (fun found => allocations.getD found #[])
          (beq_iff_eq.mp heq)
      · rfl
    specialize heffect candidate
    rw [heffect, hinitialized]
  case case4 =>
    intro fuel allocations column rest _ _ _ _ candidate
    simp [trySpaces]
  case case5 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations row hrecursive inductionHypothesis
      hvalid hnodup hcolumn hlength
    have hrecursiveEffect := inductionHypothesis hvalid hnodup hlength
    rw [hrecursive] at hrecursiveEffect
    simp only [trySpaces, hok, if_true, hrecursive]
    intro candidate
    simp only [PlacementEffect] at hrecursiveEffect ⊢
    rw [Std.HashMap.getD_insert]
    split <;> rename_i heq
    · have hcandidate : column = candidate := beq_iff_eq.mp heq
      subst candidate
      rw [if_pos (by simp)]
      rw [hrecursiveEffect]
      simp [hcolumn]
    · have hcandidate : column ≠ candidate := by
        intro h
        subst candidate
        simp at heq
      rw [hrecursiveEffect]
      by_cases hrest : candidate ∈ rest
      · simp [hrest]
      · simp [hrest, hcandidate.symm]
  case case6 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations hrecursive firstInduction spacesInduction
      hvalid hnodup hcolumn hlength
    have hrecursiveEffect := firstInduction hvalid hnodup hlength
    rw [hrecursive] at hrecursiveEffect
    have hrecursiveValid :=
      (firstFit_law fuel allocations rest length spaceStart
        ((spaceEnd.map fun endRow =>
          (endRow : ℤ) - spaceStart - length).map Int.toNat)
        hvalid hnodup hlength).1.valid
    rw [hrecursive] at hrecursiveValid
    have hremainingEffect := spacesInduction hrecursiveValid hnodup
      hcolumn hlength
    simp only [trySpaces, hok, if_true, hrecursive]
    intro candidate
    simp only [PlacementEffect] at hrecursiveEffect hremainingEffect ⊢
    specialize hrecursiveEffect candidate
    specialize hremainingEffect candidate
    rw [hremainingEffect, hrecursiveEffect]
  case case7 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      inductionHypothesis hvalid hnodup hcolumn hlength
    simpa only [trySpaces, hok] using
      inductionHypothesis hvalid hnodup hcolumn hlength

/-- If the requested row fits every column, first-fit accepts it immediately. -/
theorem firstFit_row_eq_start_of_fits
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) (hfuel : columns.length ≤ fuel)
    (hfits : ∀ column ∈ columns,
      (allocations.getD column #[]).Fits start length)
    (hbound : ∀ available, slack = some available →
      start + length ≤ start + length + available) :
    (firstFit fuel allocations columns length start slack).1 = some start := by
  induction columns generalizing fuel allocations slack with
  | nil =>
      simp [firstFit]
  | cons column rest inductionHypothesis =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hrestNodup := List.nodup_cons.mp hnodup |>.2
          have hcolumnRest := List.nodup_cons.mp hnodup |>.1
          have hrestFuel : rest.length ≤ fuel := by
            simpa using hfuel
          let initialized :=
            allocations.insert column (allocations.getD column #[])
          have hinitializedValid : CircuitAllocations.Valid initialized :=
            CircuitAllocations.Valid.insertSame hvalid column
          have hinitialized : ∀ candidate,
              initialized.getD candidate #[] =
                allocations.getD candidate #[] := by
            intro candidate
            simp only [initialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => allocations.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hrestFits : ∀ candidate ∈ rest,
              (initialized.getD candidate #[]).Fits start length := by
            intro candidate hcandidate
            rw [hinitialized]
            exact hfits candidate (by simp [hcandidate])
          obtain ⟨stop, more, hspaces, hallows⟩ :=
            Allocations.freeIntervals_starts_with_of_fits
              (allocations.getD column #[]) start length
              (slack.map fun available => start + length + available)
              (hvalid column) (hfits column (by simp)) hlength (by
                intro stop hstop
                obtain ⟨available, havailable, rfl⟩ :=
                  Option.map_eq_some_iff.mp hstop
                exact hbound available havailable)
          cases stop with
          | none =>
              have hrest := inductionHypothesis fuel initialized none
                hinitializedValid hrestNodup hrestFuel hrestFits (by simp)
              dsimp only [initialized] at hrest
              simp [firstFit, hspaces, trySpaces]
              rw [hrest]
          | some stop =>
              have hstop : start + length ≤ stop := hallows.2 stop rfl
              have hrest := inductionHypothesis fuel initialized
                (some ((stop : ℤ) - start - length).toNat)
                hinitializedValid hrestNodup hrestFuel hrestFits (by
                  intro available havailable
                  simp only [Option.some.injEq] at havailable
                  subst available
                  omega)
              dsimp only [initialized] at hrest
              have hslack :
                  ((stop : ℤ) - start - length).toNat =
                    stop - start - length := by
                omega
              rw [hslack] at hrest
              have hwidth : (length : ℤ) ≤ stop - start := by omega
              simp [firstFit, hspaces, trySpaces, hwidth]
              rw [hrest]

/-- First-fit is complete below any fitting candidate: with sufficient fuel it
returns a row no later than that candidate. Together with `firstFit_law`, this
characterizes the selected row as the least common fit. -/
theorem firstFit_row_le_fitting_candidate
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) (candidate : ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) (hfuel : columns.length ≤ fuel)
    (hstart : start ≤ candidate)
    (hbound : ∀ available, slack = some available →
      candidate + length ≤ start + length + available)
    (hfits : ∀ column ∈ columns,
      (allocations.getD column #[]).Fits candidate length) :
    ∃ row updated,
      firstFit fuel allocations columns length start slack =
        (some row, updated) ∧ row ≤ candidate := by
  induction columns generalizing fuel allocations start slack with
  | nil =>
      exact ⟨start, allocations, by simp [firstFit], hstart⟩
  | cons column rest inductionHypothesis =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hrestNodup := List.nodup_cons.mp hnodup |>.2
          have hcolumnRest := List.nodup_cons.mp hnodup |>.1
          have hrestFuel : rest.length ≤ fuel := by
            simpa using hfuel
          let initialized :=
            allocations.insert column (allocations.getD column #[])
          have hinitializedValid : CircuitAllocations.Valid initialized :=
            CircuitAllocations.Valid.insertSame hvalid column
          have hinitializedEquivalent :
              CircuitAllocations.Equivalent initialized allocations := by
            intro current
            simp only [initialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => allocations.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hrestFits : ∀ current ∈ rest,
              (initialized.getD current #[]).Fits candidate length := by
            intro current hcurrent
            rw [hinitializedEquivalent current]
            exact hfits current (by simp [hcurrent])
          let endBound := slack.map fun available =>
            start + length + available
          let spaces := (allocations.getD column #[]).freeIntervals
            start endBound
          have hcandidateBound : ∀ stop, endBound = some stop →
              candidate + length ≤ stop := by
            intro stop hstop
            obtain ⟨available, havailable, rfl⟩ :=
              Option.map_eq_some_iff.mp hstop
            exact hbound available havailable
          obtain ⟨candidateSpace, hcandidateSpace, hcandidateAllows⟩ :=
            Allocations.exists_freeInterval_of_fits
              (allocations.getD column #[]) start candidate length endBound
              (hvalid column) hstart hlength (hfits column (by simp))
              hcandidateBound
          have hspacesPairwise : spaces.Pairwise Allocations.SpaceBefore := by
            exact Allocations.freeIntervals_pairwise _ _ _
          have tryComplete : ∀ (remaining : List (ℕ × Option ℕ))
              (current : CircuitAllocations),
              current.Valid →
              (∀ item ∈ rest,
                (current.getD item #[]).Fits candidate length) →
              remaining.Pairwise Allocations.SpaceBefore →
              candidateSpace ∈ remaining →
              ∃ row updated,
                trySpaces fuel current column rest length remaining =
                  (some row, updated) ∧ row ≤ candidate := by
            intro remaining
            induction remaining with
            | nil => simp
            | cons space more spacesInduction =>
                intro current hcurrentValid hcurrentFits hpairwise hwitness
                rw [List.pairwise_cons] at hpairwise
                simp only [List.mem_cons] at hwitness
                rcases space with ⟨spaceStart, spaceEnd⟩
                let available : Option ℤ := spaceEnd.map fun stop =>
                  (stop : ℤ) - spaceStart - length
                let ok : Bool := match available with
                  | some value => decide (value ≥ 0)
                  | none => true
                by_cases hok : ok = true
                · have hrecursiveLaw := firstFit_law fuel current rest length
                    spaceStart (available.map Int.toNat) hcurrentValid
                    hrestNodup hlength
                  generalize hrecursive : firstFit fuel current rest length
                    spaceStart (available.map Int.toNat) = recursive
                      at hrecursiveLaw
                  rcases recursive with ⟨rowOption, recursiveAllocations⟩
                  cases rowOption with
                  | some row =>
                      have hrow : row ≤ candidate := by
                        rcases hwitness with hwitnessHead | hwitnessTail
                        · have : (spaceStart, spaceEnd) = candidateSpace :=
                            hwitnessHead.symm
                          subst candidateSpace
                          have hrecursiveComplete := inductionHypothesis fuel
                            current spaceStart
                            (available.map Int.toNat) hcurrentValid
                            hrestNodup hrestFuel hcandidateAllows.1
                            (by
                              intro bounded hbounded
                              cases spaceEnd with
                              | none => simp [available] at hbounded
                              | some stop =>
                                  change some
                                    (((stop : ℤ) - spaceStart - length).toNat) =
                                      some bounded at hbounded
                                  simp only [Option.some.injEq] at hbounded
                                  have hok' :
                                      (0 : ℤ) ≤ (stop : ℤ) - spaceStart - length := by
                                    simpa [ok, available] using hok
                                  have hcandidateEnd :=
                                    hcandidateAllows.2 stop rfl
                                  have htoNat :
                                      ((stop : ℤ) - spaceStart - length).toNat =
                                        stop - spaceStart - length := by omega
                                  rw [htoNat] at hbounded
                                  omega)
                            hcurrentFits
                          obtain ⟨found, updated, hfound, hfoundLe⟩ :=
                            hrecursiveComplete
                          rw [hrecursive] at hfound
                          simp only [Prod.mk.injEq, Option.some.injEq] at hfound
                          omega
                        · have hbefore := hpairwise.1 candidateSpace
                            hwitnessTail
                          obtain ⟨stop, hspaceEnd, hstopLe⟩ := hbefore
                          have hwithin := hrecursiveLaw.2 row rfl
                          have hallows := within_space_of_ok spaceStart
                            spaceEnd length row (by simpa [ok, available] using hok)
                            hwithin
                          have hcandidateStart := hcandidateAllows.1
                          have hrowEnd := hallows.2 stop hspaceEnd
                          omega
                      refine ⟨row, recursiveAllocations.insert column
                        ((recursiveAllocations.getD column #[]).insert row length),
                        ?_, hrow⟩
                      have hok' :
                          (match spaceEnd.map fun stop =>
                              (stop : ℤ) - spaceStart - length with
                            | some value => decide (value ≥ 0)
                            | none => true) = true := by
                        simpa only [ok, available] using hok
                      simp only [trySpaces, hok', if_true]
                      change (match (firstFit fuel current rest length
                        spaceStart (available.map Int.toNat)).1 with
                        | some found =>
                          (some found, (firstFit fuel current rest length
                            spaceStart (available.map Int.toNat)).2.insert
                              column (((firstFit fuel current rest length
                                spaceStart (available.map Int.toNat)).2.getD
                                  column #[]).insert found length))
                        | none => trySpaces fuel
                          (firstFit fuel current rest length spaceStart
                            (available.map Int.toNat)).2 column rest length more) = _
                      rw [hrecursive]
                  | none =>
                      have hrecursiveEffect := firstFit_effect fuel current rest
                        length spaceStart (available.map Int.toNat)
                        hcurrentValid hrestNodup hlength
                      rw [hrecursive] at hrecursiveEffect
                      have hequivalent :=
                        hrecursiveEffect.equivalent_before_of_none rfl
                      have hnextFits : ∀ item ∈ rest,
                          (recursiveAllocations.getD item #[]).Fits
                            candidate length := by
                        intro item hitem
                        rw [hequivalent item]
                        exact hcurrentFits item hitem
                      have hwitnessTail : candidateSpace ∈ more := by
                        rcases hwitness with hwitnessHead | hwitnessTail
                        · have : (spaceStart, spaceEnd) = candidateSpace :=
                            hwitnessHead.symm
                          subst candidateSpace
                          have hrecursiveComplete := inductionHypothesis fuel
                            current spaceStart
                            (available.map Int.toNat) hcurrentValid
                            hrestNodup hrestFuel hcandidateAllows.1
                            (by
                              intro bounded hbounded
                              cases spaceEnd with
                              | none => simp [available] at hbounded
                              | some stop =>
                                  change some
                                    (((stop : ℤ) - spaceStart - length).toNat) =
                                      some bounded at hbounded
                                  simp only [Option.some.injEq] at hbounded
                                  have hok' :
                                      (0 : ℤ) ≤ (stop : ℤ) - spaceStart - length := by
                                    simpa [ok, available] using hok
                                  have hcandidateEnd :=
                                    hcandidateAllows.2 stop rfl
                                  have htoNat :
                                      ((stop : ℤ) - spaceStart - length).toNat =
                                        stop - spaceStart - length := by omega
                                  rw [htoNat] at hbounded
                                  omega)
                            hcurrentFits
                          obtain ⟨found, updated, hfound, _⟩ :=
                            hrecursiveComplete
                          rw [hrecursive] at hfound
                          cases hfound
                        · exact hwitnessTail
                      obtain ⟨row, updated, hresult, hrow⟩ :=
                        spacesInduction recursiveAllocations
                          hrecursiveLaw.1.valid hnextFits hpairwise.2 hwitnessTail
                      have hok' :
                          (match spaceEnd.map fun stop =>
                              (stop : ℤ) - spaceStart - length with
                            | some value => decide (value ≥ 0)
                            | none => true) = true := by
                        simpa only [ok, available] using hok
                      exact ⟨row, updated, by
                        simp only [trySpaces, hok', if_true]
                        change (match (firstFit fuel current rest length
                          spaceStart (available.map Int.toNat)).1 with
                          | some found => _
                          | none => trySpaces fuel
                            (firstFit fuel current rest length spaceStart
                              (available.map Int.toNat)).2 column rest length more) = _
                        rw [hrecursive, hresult], hrow⟩
                · have hwitnessTail : candidateSpace ∈ more := by
                    rcases hwitness with hwitnessHead | hwitnessTail
                    · have : (spaceStart, spaceEnd) = candidateSpace :=
                        hwitnessHead.symm
                      subst candidateSpace
                      cases spaceEnd with
                      | none => simp [ok, available] at hok
                      | some stop =>
                          have hwidth := hcandidateAllows.2 stop rfl
                          have hstartCandidate := hcandidateAllows.1
                          apply False.elim
                          apply hok
                          change decide
                            ((0 : ℤ) ≤ (stop : ℤ) - spaceStart - length) = true
                          rw [decide_eq_true_eq]
                          omega
                    · exact hwitnessTail
                  obtain ⟨row, updated, hresult, hrow⟩ :=
                    spacesInduction current hcurrentValid hcurrentFits
                      hpairwise.2 hwitnessTail
                  have hok' :
                      ¬(match spaceEnd.map fun stop =>
                          (stop : ℤ) - spaceStart - length with
                        | some value => decide (value ≥ 0)
                        | none => true) = true := by
                    simpa only [ok, available] using hok
                  exact ⟨row, updated, by
                    simp only [trySpaces, if_neg hok', hresult], hrow⟩
          obtain ⟨row, updated, hresult, hrow⟩ := tryComplete spaces
            initialized hinitializedValid hrestFits hspacesPairwise
            hcandidateSpace
          refine ⟨row, updated, ?_, hrow⟩
          simp only [firstFit]
          simpa only [initialized, spaces, endBound] using hresult
/-- Every column in a footprint admits the candidate interval. -/
def FitsColumns (allocations : CircuitAllocations)
    (columns : List RegionColumn) (start length : ℕ) : Prop :=
  ∀ column ∈ columns,
    (allocations.getD column #[]).Fits start length

/-- A row is the first common fit for a footprint. This is the declarative
counterpart of V1's operational first-fit search. -/
def LeastFit (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length row : ℕ) : Prop :=
  FitsColumns allocations columns row length ∧
    ∀ candidate, FitsColumns allocations columns candidate length →
      row ≤ candidate

/-- The operational allocator chooses a declaratively least fitting row. -/
theorem firstFit_eq_of_leastFit
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start row : ℕ)
    (slack : Option ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) (hfuel : columns.length ≤ fuel)
    (hstart : start ≤ row)
    (hbound : ∀ available, slack = some available →
      row + length ≤ start + length + available)
    (hleast : LeastFit allocations columns length row) :
    ∃ updated,
      firstFit fuel allocations columns length start slack =
        (some row, updated) := by
  obtain ⟨found, updated, hresult, hfoundLe⟩ :=
    firstFit_row_le_fitting_candidate fuel allocations columns length
      start slack row hvalid hnodup hlength hfuel hstart hbound hleast.1
  have hlaw := firstFit_law fuel allocations columns length start slack
    hvalid hnodup hlength
  rw [hresult] at hlaw
  have hrowLe : row ≤ found := hleast.2 found (hlaw.1.fits found rfl)
  have : found = row := Nat.le_antisymm hfoundLe hrowLe
  subst found
  exact ⟨updated, hresult⟩

theorem FitsColumns.congruent
    {left right : CircuitAllocations} {columns : List RegionColumn}
    {start length : ℕ} (hequivalent : left.Equivalent right)
    (hfits : FitsColumns left columns start length) :
    FitsColumns right columns start length := by
  intro column hcolumn
  rw [← hequivalent column]
  exact hfits column hcolumn

theorem FitsColumns.append
    {allocations : CircuitAllocations} {left right : List RegionColumn}
    {start length : ℕ}
    (hleft : FitsColumns allocations left start length)
    (hright : FitsColumns allocations right start length) :
    FitsColumns allocations (left ++ right) start length := by
  intro column hcolumn
  rw [List.mem_append] at hcolumn
  exact hcolumn.elim (hleft column) (hright column)

theorem FitsColumns.mono
    {allocations : CircuitAllocations} {inner outer : List RegionColumn}
    {start length : ℕ} (hfits : FitsColumns allocations outer start length)
    (hsubset : inner ⊆ outer) : FitsColumns allocations inner start length := by
  intro column hcolumn
  exact hfits column (hsubset hcolumn)

/-- The already-processed prefix fits every row still inside a recursive search
window. -/
def SearchPrefixFits (allocations : CircuitAllocations)
    (processed : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  ∀ row, Within start slack length row →
    FitsColumns allocations processed row length

/-- The retained columns dominate a suffix when fitting all retained columns always
implies fitting the suffix. -/
def ColumnsDominate (allocations : CircuitAllocations)
    (retained suffix : List RegionColumn) (length : ℕ) : Prop :=
  ∀ row, FitsColumns allocations retained row length →
    FitsColumns allocations suffix row length

/-- Removing a suffix whose allocation constraints are already implied by retained
columns preserves first-fit's selected row. -/
theorem firstFit_drop_dominated_suffix
    (fuel : ℕ) (left right : CircuitAllocations)
    (processed retained suffix : List RegionColumn)
    (length start : ℕ) (slack : Option ℕ)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hequivalent : left.Equivalent right)
    (hnodup : (retained ++ suffix).Nodup)
    (hlength : 0 < length)
    (hfuel : (retained ++ suffix).length ≤ fuel)
    (hsearch : SearchPrefixFits left processed length start slack)
    (hdominate : ColumnsDominate left (processed ++ retained) suffix length) :
    (firstFit fuel left (retained ++ suffix) length start slack).1 =
      (firstFit fuel right retained length start slack).1 := by
  induction retained generalizing fuel left right processed start slack with
  | nil =>
      have hsuffixNodup : suffix.Nodup := by simpa using hnodup
      have hsuffixFuel : suffix.length ≤ fuel := by simpa using hfuel
      have hwithin : Within start slack length start := by
        exact ⟨le_rfl, by intro available _; omega⟩
      have hprocessed := hsearch start hwithin
      have hsuffixFits : FitsColumns left suffix start length := by
        apply hdominate start
        simpa using hprocessed
      have hfull := firstFit_row_eq_start_of_fits fuel left suffix
        length start slack hvalidLeft hsuffixNodup hlength hsuffixFuel
        hsuffixFits (by intro available _; omega)
      simpa [firstFit] using hfull
  | cons head rest inductionHypothesis =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hfullNodup : (head :: (rest ++ suffix)).Nodup := by
            simpa only [List.cons_append] using hnodup
          have hrestSuffixNodup : (rest ++ suffix).Nodup :=
            List.nodup_cons.mp hfullNodup |>.2
          have hheadRestSuffix : head ∉ rest ++ suffix :=
            List.nodup_cons.mp hfullNodup |>.1
          have hrestFuel : (rest ++ suffix).length ≤ fuel := by
            simpa only [List.length_cons] using
              Nat.le_of_succ_le_succ hfuel
          let leftInitialized :=
            left.insert head (left.getD head #[])
          let rightInitialized :=
            right.insert head (right.getD head #[])
          have hleftInitializedValid :
              CircuitAllocations.Valid leftInitialized :=
            CircuitAllocations.Valid.insertSame hvalidLeft head
          have hrightInitializedValid :
              CircuitAllocations.Valid rightInitialized :=
            CircuitAllocations.Valid.insertSame hvalidRight head
          have hinitializedEquivalent :
              CircuitAllocations.Equivalent leftInitialized
                rightInitialized := by
            intro column
            simp only [leftInitialized, rightInitialized,
              Std.HashMap.getD_insert]
            split <;> rename_i heq
            · have : head = column := beq_iff_eq.mp heq
              subst column
              exact congrArg (fun values => values) (hequivalent head)
            · exact hequivalent column
          have hleftInitialized :
              CircuitAllocations.Equivalent leftInitialized left := by
            intro column
            simp only [leftInitialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => left.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hrightInitialized :
              CircuitAllocations.Equivalent rightInitialized right := by
            intro column
            simp only [rightInitialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => right.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hspaces :
              (left.getD head #[]).freeIntervals start
                  (slack.map fun available => start + length + available) =
                (right.getD head #[]).freeIntervals start
                  (slack.map fun available => start + length + available) := by
            rw [hequivalent head]
          let spaces := (left.getD head #[]).freeIntervals start
            (slack.map fun available => start + length + available)
          have hspaceSafety : ∀ space ∈ spaces, ∀ row,
              Allocations.SpaceAllows space row length →
                (leftInitialized.getD head #[]).Fits row length := by
            intro space hspace row hallows
            have hfits := Allocations.freeIntervals_fits
              (left.getD head #[]) start
              (slack.map fun available => start + length + available)
              (hvalidLeft head) hspace hallows
            rw [hleftInitialized head]
            exact hfits
          have hspaceWithin : ∀ space ∈ spaces, ∀ row,
              Allocations.SpaceAllows space row length →
                Within start slack length row := by
            intro space hspace row hallows
            constructor
            · exact (Allocations.freeIntervals_start_le _ _ _ hspace).trans
                hallows.1
            · intro available havailable
              subst slack
              obtain ⟨stop, hstop⟩ :=
                Allocations.freeIntervals_bounded _ _ _ hspace
              rcases space with ⟨spaceStart, spaceEnd⟩
              simp only at hstop
              subst spaceEnd
              exact (hallows.2 stop rfl).trans
                (Allocations.freeIntervals_end_le _ _ _ hspace)
          have compareSpaces : ∀ (remaining : List (ℕ × Option ℕ))
              (currentLeft currentRight : CircuitAllocations),
              currentLeft.Valid → currentRight.Valid →
              currentLeft.Equivalent currentRight →
              currentLeft.Equivalent leftInitialized →
              currentRight.Equivalent rightInitialized →
              (∀ space ∈ remaining, ∀ row,
                Allocations.SpaceAllows space row length →
                  (currentLeft.getD head #[]).Fits row length) →
              (∀ space ∈ remaining, ∀ row,
                Allocations.SpaceAllows space row length →
                  Within start slack length row) →
              (trySpaces fuel currentLeft head (rest ++ suffix)
                  length remaining).1 =
                (trySpaces fuel currentRight head rest length remaining).1 := by
            intro remaining
            induction remaining with
            | nil =>
                intro currentLeft currentRight _ _ _ _ _ _ _
                simp [trySpaces]
            | cons space more spacesInduction =>
                rcases space with ⟨spaceStart, spaceEnd⟩
                intro currentLeft currentRight hcurrentLeftValid
                  hcurrentRightValid hcurrentEquivalent hcurrentLeft
                  hcurrentRight hremainingSafety hremainingWithin
                let available : Option ℤ := spaceEnd.map fun stop =>
                  (stop : ℤ) - spaceStart - length
                let ok : Bool := match available with
                  | some value => decide (value ≥ 0)
                  | none => true
                have havailable :
                    (spaceEnd.map fun stop =>
                      (stop : ℤ) - spaceStart - length) = available := rfl
                by_cases hok : ok = true
                · have hallowsOfWithin : ∀ row,
                      Within spaceStart (available.map Int.toNat) length row →
                        Allocations.SpaceAllows
                          (spaceStart, spaceEnd) row length := by
                    intro row hwithin
                    apply within_space_of_ok spaceStart spaceEnd length row
                      (by simpa only [ok, available] using hok)
                    exact hwithin
                  have hrecursiveSearch : SearchPrefixFits currentLeft
                      (processed ++ [head]) length spaceStart
                      (available.map Int.toNat) := by
                    intro row hwithin
                    have hallows := hallowsOfWithin row hwithin
                    have houterWithin := hremainingWithin
                      (spaceStart, spaceEnd) (by simp) row hallows
                    have hprocessedFits := hsearch row houterWithin
                    have hprocessedCurrent := hprocessedFits.congruent
                      (hcurrentLeft.trans hleftInitialized).symm
                    have hheadFits := hremainingSafety
                      (spaceStart, spaceEnd) (by simp) row hallows
                    exact hprocessedCurrent.append (by
                      intro column hcolumn
                      simp only [List.mem_singleton] at hcolumn
                      subst column
                      exact hheadFits)
                  have hrecursiveDominate : ColumnsDominate currentLeft
                      ((processed ++ [head]) ++ rest) suffix length := by
                    intro row hfits
                    have hcurrent : FitsColumns currentLeft
                        (processed ++ head :: rest) row length := by
                      simpa only [List.append_assoc,
                        List.singleton_append] using hfits
                    have horiginal := hcurrent.congruent
                      (hcurrentLeft.trans hleftInitialized)
                    have hsuffixFits := hdominate row horiginal
                    exact hsuffixFits.congruent
                      (hcurrentLeft.trans hleftInitialized).symm
                  have hrecursiveRows := inductionHypothesis fuel
                    currentLeft currentRight (processed ++ [head])
                    spaceStart (available.map Int.toNat)
                    hcurrentLeftValid hcurrentRightValid hcurrentEquivalent
                    hrestSuffixNodup hrestFuel hrecursiveSearch
                    hrecursiveDominate
                  generalize hfull : firstFit fuel currentLeft
                    (rest ++ suffix) length spaceStart
                      (available.map Int.toNat) = fullResult at hrecursiveRows
                  rcases fullResult with ⟨fullRow, fullAllocations⟩
                  generalize hcore : firstFit fuel currentRight rest length
                    spaceStart (available.map Int.toNat) = coreResult
                      at hrecursiveRows
                  rcases coreResult with ⟨coreRow, coreAllocations⟩
                  dsimp only at hrecursiveRows
                  cases fullRow with
                  | some row =>
                      have hcoreRow : coreRow = some row := hrecursiveRows.symm
                      subst coreRow
                      simp only [trySpaces]
                      change ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1 =
                        ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1
                      simp only [if_pos hok]
                      rw [havailable, hfull, hcore]
                  | none =>
                      have hcoreRow : coreRow = none := hrecursiveRows.symm
                      subst coreRow
                      have hfullEffect := firstFit_effect fuel currentLeft
                        (rest ++ suffix) length spaceStart
                        (available.map Int.toNat) hcurrentLeftValid
                        hrestSuffixNodup hlength
                      rw [hfull] at hfullEffect
                      have hcoreEffect := firstFit_effect fuel currentRight
                        rest length spaceStart (available.map Int.toNat)
                        hcurrentRightValid
                        hrestSuffixNodup.of_append_left hlength
                      rw [hcore] at hcoreEffect
                      have hfullEquivalent :=
                        hfullEffect.equivalent_before_of_none rfl
                      have hcoreEquivalent :=
                        hcoreEffect.equivalent_before_of_none rfl
                      have hnextEquivalent :
                          fullAllocations.Equivalent coreAllocations :=
                        hfullEquivalent.trans
                          (hcurrentEquivalent.trans hcoreEquivalent.symm)
                      have hnextSafety : ∀ next ∈ more, ∀ candidate,
                          Allocations.SpaceAllows next candidate length →
                            (fullAllocations.getD head #[]).Fits
                              candidate length := by
                        intro next hnext candidate hallows
                        rw [hfullEquivalent head]
                        exact hremainingSafety next (by simp [hnext])
                          candidate hallows
                      have hfullValid :=
                        (firstFit_law fuel currentLeft (rest ++ suffix)
                          length spaceStart (available.map Int.toNat)
                          hcurrentLeftValid hrestSuffixNodup hlength).1.valid
                      rw [hfull] at hfullValid
                      have hcoreValid :=
                        (firstFit_law fuel currentRight rest length spaceStart
                          (available.map Int.toNat) hcurrentRightValid
                          hrestSuffixNodup.of_append_left hlength).1.valid
                      rw [hcore] at hcoreValid
                      have hnext := spacesInduction fullAllocations
                        coreAllocations hfullValid hcoreValid
                        hnextEquivalent
                        (hfullEquivalent.trans hcurrentLeft)
                        (hcoreEquivalent.trans hcurrentRight) hnextSafety
                        (by
                          intro next hnext candidate hallows
                          exact hremainingWithin next (by simp [hnext])
                            candidate hallows)
                      simp only [trySpaces]
                      change ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1 =
                        ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1
                      simp only [if_pos hok]
                      rw [havailable, hfull, hcore]
                      exact hnext
                · have hnextSafety : ∀ next ∈ more, ∀ candidate,
                      Allocations.SpaceAllows next candidate length →
                        (currentLeft.getD head #[]).Fits candidate length := by
                    intro next hnext candidate hallows
                    exact hremainingSafety next (by simp [hnext]) candidate hallows
                  have hnext := spacesInduction currentLeft currentRight
                    hcurrentLeftValid hcurrentRightValid hcurrentEquivalent
                    hcurrentLeft hcurrentRight hnextSafety
                    (by
                      intro next hnext candidate hallows
                      exact hremainingWithin next (by simp [hnext])
                        candidate hallows)
                  simp only [trySpaces]
                  change ((if ok = true then _ else _) :
                      Option ℕ × CircuitAllocations).1 =
                    ((if ok = true then _ else _) :
                      Option ℕ × CircuitAllocations).1
                  simpa only [if_neg hok] using hnext
          have hresult := compareSpaces spaces leftInitialized rightInitialized
            hleftInitializedValid hrightInitializedValid hinitializedEquivalent
            (CircuitAllocations.Equivalent.refl leftInitialized)
            (CircuitAllocations.Equivalent.refl rightInitialized) hspaceSafety
            hspaceWithin
          simp only [List.cons_append, firstFit]
          rw [← hspaces]
          simpa only [leftInitialized, rightInitialized, spaces] using hresult

private def FirstFitCongruent
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  ∀ other, allocations.Valid → other.Valid → columns.Nodup →
    0 < length → allocations.AgreesOn other columns →
    let left := firstFit fuel allocations columns length start slack
    let right := firstFit fuel other columns length start slack
    left.1 = right.1 ∧ left.2.AgreesOn right.2 columns

private def TrySpacesCongruent
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length : ℕ) (spaces : List (ℕ × Option ℕ)) : Prop :=
  ∀ other, allocations.Valid → other.Valid → rest.Nodup →
    column ∉ rest → 0 < length →
    allocations.AgreesOn other (column :: rest) →
    let left := trySpaces fuel allocations column rest length spaces
    let right := trySpaces fuel other column rest length spaces
    left.1 = right.1 ∧ left.2.AgreesOn right.2 (column :: rest)

/-- First-fit's result on a region depends only on that region's columns. -/
theorem firstFit_congruent
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) :
    FirstFitCongruent fuel allocations columns length start slack := by
  apply firstFit.induct (regionLen := length)
    (motive1 := fun fuel allocations columns start slack =>
      FirstFitCongruent fuel allocations columns length start slack)
    (motive2 := fun fuel allocations column rest spaces =>
      TrySpacesCongruent fuel allocations column rest length spaces)
  all_goals simp only [FirstFitCongruent, TrySpacesCongruent]
  case case1 =>
    intro fuel allocations start slack other _ _ _ _ _
    simp only [firstFit]
    exact ⟨True.intro, by intro column hcolumn; simp at hcolumn⟩
  case case2 =>
    intro allocations start slack head tail other _ _ hnodup _ hagree
    simp only [firstFit]
    exact ⟨True.intro, hagree⟩
  case case3 =>
    intro allocations start slack fuel column rest inductionHypothesis
      other hvalidLeft hvalidRight hnodup hlength hagree
    have hrestNodup := List.nodup_cons.mp hnodup |>.2
    have hcolumnRest := List.nodup_cons.mp hnodup |>.1
    have hcolumn := hagree column (by simp)
    let leftInitialized :=
      allocations.insert column (allocations.getD column #[])
    let rightInitialized :=
      other.insert column (other.getD column #[])
    have hinitializedAgree :
        CircuitAllocations.AgreesOn leftInitialized rightInitialized
          (column :: rest) := by
      apply CircuitAllocations.AgreesOn.insert hagree
      exact hcolumn
    have hinitializedValidLeft : CircuitAllocations.Valid leftInitialized :=
      CircuitAllocations.Valid.insertSame hvalidLeft column
    have hinitializedValidRight : CircuitAllocations.Valid rightInitialized :=
      CircuitAllocations.Valid.insertSame hvalidRight column
    have hresult := inductionHypothesis rightInitialized
      hinitializedValidLeft hinitializedValidRight hrestNodup
      hcolumnRest hlength hinitializedAgree
    simpa only [firstFit, leftInitialized, rightInitialized,
      hcolumn] using hresult
  case case4 =>
    intro fuel allocations column rest other _ _ _ _ _ hagree
    simp only [trySpaces]
    exact ⟨True.intro, hagree⟩
  case case5 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      leftRecursive row hleftRecursive firstInduction
      other hvalidLeft hvalidRight hrestNodup hcolumnRest hlength hagree
    have hrestAgree := CircuitAllocations.AgreesOn.mono hagree (by
      intro candidate hcandidate
      exact List.mem_cons_of_mem column hcandidate)
    have hfirst := firstInduction other hvalidLeft hvalidRight
      hrestNodup hlength hrestAgree
    simp only [trySpaces, hok, if_true, hleftRecursive] at hfirst ⊢
    generalize hrightRecursive :
      firstFit fuel other rest length spaceStart
        ((spaceEnd.map fun endRow =>
          (endRow : ℤ) - spaceStart - length).map Int.toNat) = rightResult
    rcases rightResult with ⟨rightRow, rightRecursive⟩
    rw [hrightRecursive] at hfirst
    dsimp only at hfirst
    have hrow : rightRow = some row := hfirst.1.symm
    rw [hrow]
    constructor
    · rfl
    · have hrecursiveAgree :
          leftRecursive.AgreesOn rightRecursive (column :: rest) := by
        intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | hcandidate
        · have hleftLaw := firstFit_law fuel allocations rest length
            spaceStart
            ((spaceEnd.map fun endRow =>
              (endRow : ℤ) - spaceStart - length).map Int.toNat)
            hvalidLeft hrestNodup hlength
          have hrightLaw := firstFit_law fuel other rest length
            spaceStart
            ((spaceEnd.map fun endRow =>
              (endRow : ℤ) - spaceStart - length).map Int.toNat)
            hvalidRight hrestNodup hlength
          rw [hleftRecursive] at hleftLaw
          rw [hrightRecursive, hrow] at hrightLaw
          have hleftColumn :
              leftRecursive.getD candidate #[] =
                allocations.getD candidate #[] :=
            hleftLaw.1.sameOutside candidate hcolumnRest
          have hrightColumn :
              rightRecursive.getD candidate #[] = other.getD candidate #[] :=
            hrightLaw.1.sameOutside candidate hcolumnRest
          rw [hleftColumn, hrightColumn]
          exact hagree candidate (by simp)
        · exact hfirst.2 candidate hcandidate
      apply CircuitAllocations.AgreesOn.insert hrecursiveAgree
      exact congrArg (fun values => values.insert row length)
        (hrecursiveAgree column (by simp))
  case case6 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      leftRecursive hleftRecursive firstInduction spacesInduction
      other hvalidLeft hvalidRight hrestNodup hcolumnRest hlength hagree
    have hrestAgree := CircuitAllocations.AgreesOn.mono hagree (by
      intro candidate hcandidate
      exact List.mem_cons_of_mem column hcandidate)
    have hfirst := firstInduction other hvalidLeft hvalidRight
      hrestNodup hlength hrestAgree
    generalize hrightRecursive :
      firstFit fuel other rest length spaceStart
        ((spaceEnd.map fun endRow =>
          (endRow : ℤ) - spaceStart - length).map Int.toNat) = rightResult
    rcases rightResult with ⟨rightRow, rightRecursive⟩
    rw [hleftRecursive, hrightRecursive] at hfirst
    dsimp only at hfirst
    have hrightRow : rightRow = none := hfirst.1.symm
    have hleftLaw := firstFit_law fuel allocations rest length
      spaceStart
      ((spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length).map Int.toNat)
      hvalidLeft hrestNodup hlength
    have hrightLaw := firstFit_law fuel other rest length
      spaceStart
      ((spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length).map Int.toNat)
      hvalidRight hrestNodup hlength
    rw [hleftRecursive] at hleftLaw
    rw [hrightRecursive, hrightRow] at hrightLaw
    have hrecursiveAgree :
        leftRecursive.AgreesOn rightRecursive (column :: rest) := by
      intro candidate hcandidate
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | hcandidate
      · have hleftColumn :
            leftRecursive.getD candidate #[] =
              allocations.getD candidate #[] :=
          hleftLaw.1.sameOutside candidate hcolumnRest
        have hrightColumn :
            rightRecursive.getD candidate #[] = other.getD candidate #[] :=
          hrightLaw.1.sameOutside candidate hcolumnRest
        rw [hleftColumn, hrightColumn]
        exact hagree candidate (by simp)
      · exact hfirst.2 candidate hcandidate
    have hremaining := spacesInduction rightRecursive
      hleftLaw.1.valid hrightLaw.1.valid hrestNodup hcolumnRest
      hlength hrecursiveAgree
    simpa only [trySpaces, hok, if_true, hleftRecursive,
      hrightRecursive, hrightRow] using hremaining
  case case7 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      inductionHypothesis other hvalidLeft hvalidRight hrestNodup
      hcolumnRest hlength hagree
    have hresult := inductionHypothesis other hvalidLeft hvalidRight
      hrestNodup hcolumnRest hlength hagree
    simpa only [trySpaces, hok] using hresult

/-- Extensionally equal allocation maps remain equal after the same first-fit
placement, and produce the same start row. -/
theorem firstFit_equivalent
    (fuel : ℕ) (left right : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hnodup : columns.Nodup) (hlength : 0 < length)
    (hequivalent : left.Equivalent right) :
    let leftResult := firstFit fuel left columns length start slack
    let rightResult := firstFit fuel right columns length start slack
    leftResult.1 = rightResult.1 ∧
      leftResult.2.Equivalent rightResult.2 := by
  have hlocal := firstFit_congruent fuel left columns length start slack
    right hvalidLeft hvalidRight hnodup hlength
      (hequivalent.agreesOn columns)
  have hleftLaw := firstFit_law fuel left columns length start slack
    hvalidLeft hnodup hlength
  have hrightLaw := firstFit_law fuel right columns length start slack
    hvalidRight hnodup hlength
  constructor
  · exact hlocal.1
  · intro column
    by_cases hcolumn : column ∈ columns
    · exact hlocal.2 column hcolumn
    · rw [hleftLaw.1.sameOutside column hcolumn,
          hrightLaw.1.sameOutside column hcolumn]
      exact hequivalent column

private theorem trySpaces_success_of_final_unbounded
    (initialSpaces : List (ℕ × Option ℕ))
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length finalStart : ℕ)
    (hvalid : allocations.Valid)
    (hnodup : rest.Nodup) (hlength : 0 < length)
    (hrecursiveSuccess :
      ∀ current, current.Valid →
        ∃ row updated,
          firstFit fuel current rest length finalStart none =
            (some row, updated)) :
    ∃ row updated,
      trySpaces fuel allocations column rest length
        (initialSpaces ++ [(finalStart, none)]) = (some row, updated) := by
  induction initialSpaces generalizing allocations with
  | nil =>
      obtain ⟨row, updated, hresult⟩ :=
        hrecursiveSuccess allocations hvalid
      exact ⟨row,
        updated.insert column
          ((updated.getD column #[]).insert row length), by
          simp [trySpaces, hresult]⟩
  | cons space more inductionHypothesis =>
      rcases space with ⟨spaceStart, spaceEnd⟩
      cases spaceEnd with
      | none =>
        cases hresult : firstFit fuel allocations rest length spaceStart
            none with
        | mk rowOption updated =>
          cases rowOption with
          | some row =>
              exact ⟨row,
                updated.insert column
                  ((updated.getD column #[]).insert row length), by
                    simp [trySpaces, hresult]⟩
          | none =>
              have hfirstLaw := firstFit_law fuel allocations rest
                length spaceStart none hvalid hnodup hlength
              rw [hresult] at hfirstLaw
              obtain ⟨row, final, hfinal⟩ :=
                inductionHypothesis updated hfirstLaw.1.valid
              exact ⟨row, final, by simp [trySpaces, hresult, hfinal]⟩
      | some spaceEnd =>
          by_cases hfits :
              (0 : ℤ) ≤ (spaceEnd : ℤ) - spaceStart - length
          · have hcondition :
                (length : ℤ) ≤ (spaceEnd : ℤ) - spaceStart := by
              omega
            cases hresult : firstFit fuel allocations rest length spaceStart
                (some (spaceEnd - spaceStart - length)) with
            | mk rowOption updated =>
              cases rowOption with
              | some row =>
                  exact ⟨row,
                    updated.insert column
                      ((updated.getD column #[]).insert row length), by
                        simp [trySpaces, hcondition, hresult]⟩
              | none =>
                  have hfirstLaw := firstFit_law fuel allocations rest
                    length spaceStart
                    (some (spaceEnd - spaceStart - length))
                    hvalid hnodup hlength
                  rw [hresult] at hfirstLaw
                  obtain ⟨row, final, hfinal⟩ :=
                    inductionHypothesis updated hfirstLaw.1.valid
                  exact ⟨row, final, by
                    simp [trySpaces, hcondition, hresult, hfinal]⟩
          · obtain ⟨row, updated, hresult⟩ :=
              inductionHypothesis allocations hvalid
            exact ⟨row, updated, by
              have hcondition :
                  ¬(length : ℤ) ≤ (spaceEnd : ℤ) - spaceStart := by
                omega
              simp [trySpaces, hcondition, hresult]⟩

/-- With unbounded outer slack, sufficient fuel always yields a placement. -/
theorem firstFit_success_unbounded
    (columns : List RegionColumn) (allocations : CircuitAllocations)
    (length start : ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) :
    ∃ row updated,
      firstFit columns.length allocations columns length start none =
        (some row, updated) := by
  induction columns generalizing allocations start with
  | nil => exact ⟨start, allocations, by simp [firstFit]⟩
  | cons column rest inductionHypothesis =>
      have hrestNodup := List.nodup_cons.mp hnodup |>.2
      let initialized :=
        allocations.insert column (allocations.getD column #[])
      let scanResult := Allocations.scanFreeIntervals none
        (allocations.getD column #[]).toList start
      have hinitializedValid : CircuitAllocations.Valid initialized :=
        CircuitAllocations.Valid.insertSame hvalid column
      have hrecursiveSuccess :
          ∀ current, current.Valid →
            ∃ row updated,
              firstFit rest.length current rest length
                scanResult.2 none =
                (some row, updated) := by
        intro current hcurrent
        exact inductionHypothesis current _ hcurrent hrestNodup
      obtain ⟨row, updated, hresult⟩ :=
        trySpaces_success_of_final_unbounded scanResult.1
          rest.length initialized column rest length scanResult.2
          hinitializedValid hrestNodup hlength hrecursiveSuccess
      exact ⟨row, updated, by
        simpa [firstFit, initialized, Allocations.freeIntervals] using hresult⟩

/-- `slot_in` (`strategy.rs:165-195`): place each shape (in the given order) at the earliest
free common row via `first_fit_region`, threading the allocations. Returns the
`(regionIndex, start)` pairs in the input order plus the final allocations. -/
def slotInFrom (shapes : List RegionShape)
    (colAllocs : CircuitAllocations) :
    List (ℕ × ℕ) × CircuitAllocations :=
  match shapes with
  | [] => ([], colAllocs)
  | shape :: rest =>
    let cols := sortRegionColumns shape.columns
    let (row?, colAllocs') := firstFit cols.length colAllocs cols shape.rowCount 0 none
    let (pairs, finalAllocations) := slotInFrom rest colAllocs'
    ((shape.index, row?.getD 0) :: pairs, finalAllocations)

/-- `slot_in` (`strategy.rs:165-195`) from an initially empty allocation map. -/
def slotIn (shapes : List RegionShape) :
    List (ℕ × ℕ) × CircuitAllocations :=
  slotInFrom shapes ∅

/-- Slotting preserves the input region-index sequence in its result pairs. -/
theorem slotInFrom_indices (shapes : List RegionShape)
    (allocations : CircuitAllocations) :
    (slotInFrom shapes allocations).1.map (·.1) =
      shapes.map RegionShape.index := by
  induction shapes generalizing allocations with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      simp only [slotInFrom, List.map_cons]
      rw [inductionHypothesis]

/-- Slotting from an empty allocation map preserves region indices. -/
theorem slotIn_indices (shapes : List RegionShape) :
    (slotIn shapes).1.map (·.1) = shapes.map RegionShape.index := by
  exact slotInFrom_indices shapes ∅

/-- Slot two shape blocks without flattening their compositional boundary. -/
theorem slotInFrom_append (left right : List RegionShape)
    (allocations : CircuitAllocations) :
    slotInFrom (left ++ right) allocations =
      let leftResult := slotInFrom left allocations
      let rightResult := slotInFrom right leftResult.2
      (leftResult.1 ++ rightResult.1, rightResult.2) := by
  induction left generalizing allocations with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      simp only [List.cons_append, slotInFrom]
      rw [inductionHypothesis]

/-- Repeatedly slot one already-reduced block, retaining the repetition count rather
than requiring callers to expand a `List.replicate`. -/
def slotInRepeated (count : ℕ) (shapes : List RegionShape)
    (allocations : CircuitAllocations) :
    List (ℕ × ℕ) × CircuitAllocations :=
  match count with
  | 0 => ([], allocations)
  | count + 1 =>
      let first := slotInFrom shapes allocations
      let rest := slotInRepeated count shapes first.2
      (first.1 ++ rest.1, rest.2)

/-- Slotting a replicated reduced block is exactly `slotInRepeated`; the proof keeps
`List.replicate` intact and inducts only over its compact repetition count. -/
theorem slotInFrom_flatten_replicate
    (count : ℕ) (shapes : List RegionShape)
    (allocations : CircuitAllocations) :
    slotInFrom (List.replicate count shapes).flatten allocations =
      slotInRepeated count shapes allocations := by
  induction count generalizing allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons, slotInFrom_append]
      simp only [slotInRepeated]
      rw [inductionHypothesis]

/-- Place one index-free reduced region summary. -/
def placeSummary (summary : RegionShapeSummary)
    (allocations : CircuitAllocations) :
    Option ℕ × CircuitAllocations :=
  let columns := sortRegionColumns summary.columns
  firstFit columns.length allocations columns summary.rowCount 0 none

/-- A declaratively least fitting row determines the exact row selected when a
reduced summary is placed. -/
theorem placeSummary_row_eq_of_leastFit
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (row : ℕ) (hvalid : allocations.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hleast : LeastFit allocations (sortRegionColumns summary.columns)
      summary.rowCount row) :
    (placeSummary summary allocations).1 = some row := by
  obtain ⟨updated, hresult⟩ := firstFit_eq_of_leastFit
    (sortRegionColumns summary.columns).length allocations
    (sortRegionColumns summary.columns) summary.rowCount 0 row none
    hvalid ((sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup)
    hlength le_rfl (Nat.zero_le row) (by simp) hleast
  simp only [placeSummary, hresult]

/-- Two reduced summaries are placement-equivalent when the floor planner sees
the same sorted column footprint and height. This deliberately ignores the stored
order of the column set. -/
def RegionShapeSummary.PlacementEquivalent
    (left right : RegionShapeSummary) : Prop :=
  sortRegionColumns left.columns = sortRegionColumns right.columns ∧
    left.rowCount = right.rowCount

/-- Canonical representative of a reduced physical shape, quotienting the
incidental first-seen order of its columns. -/
def RegionShapeSummary.normalized
    (summary : RegionShapeSummary) : RegionShapeSummary :=
  { summary with columns := sortRegionColumns summary.columns }

theorem RegionShapeSummary.placementEquivalent_iff_normalized_eq
    {left right : RegionShapeSummary} :
    left.PlacementEquivalent right ↔ left.normalized = right.normalized := by
  simp only [PlacementEquivalent, normalized]
  constructor
  · rintro ⟨hcolumns, hrows⟩
    cases left
    cases right
    simp_all
  · intro heq
    injection heq with hcolumns hrows
    exact ⟨hcolumns, hrows⟩

/-- Equality of canonical physical summaries yields pointwise placement
equivalence without requiring a decidability instance for `List.Forall₂`. -/
theorem RegionShapeSummary.forall₂_placementEquivalent_of_map_normalized_eq
    {left right : List RegionShapeSummary}
    (hequal : left.map RegionShapeSummary.normalized =
      right.map RegionShapeSummary.normalized) :
    List.Forall₂ RegionShapeSummary.PlacementEquivalent left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Forall₂.nil
      | cons head tail => simp at hequal
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp at hequal
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at hequal
          exact List.Forall₂.cons
            (RegionShapeSummary.placementEquivalent_iff_normalized_eq.mpr
              hequal.1)
            (inductionHypothesis hequal.2)

theorem RegionShapeSummary.normalized_key_eq
    (summary : RegionShapeSummary) :
    summary.normalized.key = summary.key := by
  unfold normalized RegionShapeSummary.key RegionShapeSummary.adviceCols
  have hlength := ((sortRegionColumns_perm summary.columns).filter
    RegionColumn.isAdvice).length_eq
  exact congrArg (fun count => count * summary.rowCount) hlength

theorem RegionShapeSummary.PlacementEquivalent.symm
    {left right : RegionShapeSummary}
    (hequivalent : left.PlacementEquivalent right) :
    right.PlacementEquivalent left :=
  ⟨hequivalent.1.symm, hequivalent.2.symm⟩

theorem placeSummary_eq_of_placementEquivalent
    {left right : RegionShapeSummary}
    (hequivalent : left.PlacementEquivalent right)
    (allocations : CircuitAllocations) :
    placeSummary left allocations = placeSummary right allocations := by
  simp only [placeSummary]
  rw [hequivalent.1, hequivalent.2]

/-- The generic first-fit law, specialized to one reduced region summary. -/
theorem placeSummary_law
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hnodup : summary.columns.Nodup)
    (hlength : 0 < summary.rowCount) :
    PlacementLaw allocations (sortRegionColumns summary.columns)
      summary.rowCount (placeSummary summary allocations) ∧
      ∀ row, (placeSummary summary allocations).1 = some row →
        Within 0 none summary.rowCount row := by
  exact firstFit_law (sortRegionColumns summary.columns).length allocations
    (sortRegionColumns summary.columns) summary.rowCount 0 none hvalid
    ((sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup)
    hlength

/-- Placing a well-formed reduced summary preserves allocation validity, including
the empty-column case where first-fit is a no-op. -/
theorem placeSummary_valid
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hwellFormed : summary.WellFormed) :
    (placeSummary summary allocations).2.Valid := by
  by_cases hcolumns : summary.columns = []
  · simp [placeSummary, hcolumns, sortRegionColumns, firstFit]
    exact hvalid
  · exact (placeSummary_law summary allocations hvalid hwellFormed.1
      (hwellFormed.2 hcolumns)).1.valid

/-- Index-free slotting of the reduced region summaries. This is the exact V1
allocator with only the bookkeeping region index removed. -/
def slotShapeSummariesFrom (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    List ℕ × CircuitAllocations :=
  match summaries with
  | [] => ([], allocations)
  | summary :: rest =>
      let (row?, updated) := placeSummary summary allocations
      let (starts, finalAllocations) :=
        slotShapeSummariesFrom rest updated
      (row?.getD 0 :: starts, finalAllocations)

/-- Forgetting all region indices before slotting preserves starts and allocation
state. -/
theorem slotInFrom_forgetIndices
    (shapes : List RegionShape) (allocations : CircuitAllocations) :
    ((slotInFrom shapes allocations).1.map (·.2),
      (slotInFrom shapes allocations).2) =
      slotShapeSummariesFrom (shapes.map RegionShape.toSummary) allocations := by
  induction shapes generalizing allocations with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      let columns := sortRegionColumns shape.columns
      generalize hfirst : firstFit columns.length allocations columns
        shape.rowCount 0 none = first
      rcases first with ⟨row?, updated⟩
      simp only [slotInFrom, slotShapeSummariesFrom, List.map_cons,
        RegionShape.toSummary, placeSummary, columns, hfirst]
      have ih := inductionHypothesis updated
      have ihStarts :
          (slotInFrom rest updated).1.map (·.2) =
            (slotShapeSummariesFrom
              (rest.map RegionShape.toSummary) updated).1 := by
        simpa using congrArg Prod.fst ih
      have ihAllocations :
          (slotInFrom rest updated).2 =
            (slotShapeSummariesFrom
              (rest.map RegionShape.toSummary) updated).2 := by
        simpa using congrArg Prod.snd ih
      rw [ihStarts, ihAllocations]

/-- Removing region indices before slotting changes only the index component of
the returned pairs, never starts or allocation state. -/
theorem slotInFrom_indexRegionSummaries
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    ((slotInFrom (indexRegionSummaries initial summaries) allocations).1.map
        (·.2),
      (slotInFrom (indexRegionSummaries initial summaries) allocations).2) =
      slotShapeSummariesFrom summaries allocations := by
  induction summaries generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      let columns := sortRegionColumns summary.columns
      generalize hfirst : firstFit columns.length allocations columns
        summary.rowCount 0 none = first
      rcases first with ⟨row?, updated⟩
      simp only [indexRegionSummaries, slotInFrom, measureRegionSummary,
        List.map_cons, columns, hfirst, slotShapeSummariesFrom,
        placeSummary]
      have ih := inductionHypothesis (initial + 1) updated
      have ihStarts :
          (slotInFrom (indexRegionSummaries (initial + 1) rest)
            updated).1.map (·.2) =
            (slotShapeSummariesFrom rest updated).1 := by
        simpa using congrArg Prod.fst ih
      have ihAllocations :
          (slotInFrom (indexRegionSummaries (initial + 1) rest)
            updated).2 =
            (slotShapeSummariesFrom rest updated).2 := by
        simpa using congrArg Prod.snd ih
      rw [ihStarts, ihAllocations]

/-- Index-free slotting composes over summary concatenation. -/
theorem slotShapeSummariesFrom_append
    (left right : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom (left ++ right) allocations =
      let leftResult := slotShapeSummariesFrom left allocations
      let rightResult := slotShapeSummariesFrom right leftResult.2
      (leftResult.1 ++ rightResult.1, rightResult.2) := by
  induction left generalizing allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hfirst : placeSummary summary allocations = first
      rcases first with ⟨row?, updated⟩
      simp only [List.cons_append, slotShapeSummariesFrom, hfirst]
      rw [inductionHypothesis]

/-- Empty zero-row summaries contribute zero starts and leave allocations
unchanged. -/
theorem slotShapeSummariesFrom_replicate_empty
    (count : Nat) (allocations : CircuitAllocations) :
    slotShapeSummariesFrom
      (List.replicate count { columns := [], rowCount := 0 }) allocations =
        (List.replicate count 0, allocations) := by
  induction count generalizing allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ]
      simp [slotShapeSummariesFrom, placeSummary, sortRegionColumns,
        firstFit, inductionHypothesis]
      rw [List.replicate_succ]

/-- Replacing every reduced region shape by a placement-equivalent shape preserves
the complete index-free planner result. This is the compositional boundary used by
concrete circuits to publish canonical physical summaries without preserving the
incidental first-seen order of their column sets. -/
theorem slotShapeSummariesFrom_eq_of_forall₂_placementEquivalent
    {left right : List RegionShapeSummary}
    (hequivalent : List.Forall₂ RegionShapeSummary.PlacementEquivalent
      left right)
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom left allocations =
      slotShapeSummariesFrom right allocations := by
  induction hequivalent generalizing allocations with
  | nil => rfl
  | cons hhead _ inductionHypothesis =>
      simp only [slotShapeSummariesFrom]
      rw [placeSummary_eq_of_placementEquivalent hhead,
        inductionHypothesis]

/-- Repeated index-free slotting of one already-reduced summary block. -/
def slotShapeSummariesRepeated (count : ℕ)
    (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    List ℕ × CircuitAllocations :=
  match count with
  | 0 => ([], allocations)
  | count + 1 =>
      let first := slotShapeSummariesFrom summaries allocations
      let rest := slotShapeSummariesRepeated count summaries first.2
      (first.1 ++ rest.1, rest.2)

/-- Evaluate a compact `List.replicate` summary by induction over its count. -/
theorem slotShapeSummariesFrom_flatten_replicate
    (count : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom
        (List.replicate count summaries).flatten allocations =
      slotShapeSummariesRepeated count summaries allocations := by
  induction count generalizing allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons,
        slotShapeSummariesFrom_append]
      simp only [slotShapeSummariesRepeated]
      rw [inductionHypothesis]

/-- Evaluate repeated singleton-summary blocks while retaining every chosen start. -/
def slotShapeSummaryBlocks (blocks : List (ℕ × RegionShapeSummary))
    (allocations : CircuitAllocations) : List ℕ × CircuitAllocations :=
  match blocks with
  | [] => ([], allocations)
  | (count, summary) :: rest =>
      let first := slotShapeSummariesRepeated count [summary] allocations
      let tail := slotShapeSummaryBlocks rest first.2
      (first.1 ++ tail.1, tail.2)

/-- A flat list of repeated summaries and its compact block evaluator agree exactly. -/
theorem slotShapeSummariesFrom_flatMap_replicate
    (blocks : List (ℕ × RegionShapeSummary))
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom
        (blocks.flatMap fun block => List.replicate block.1 block.2)
        allocations =
      slotShapeSummaryBlocks blocks allocations := by
  induction blocks generalizing allocations with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      rcases block with ⟨count, summary⟩
      rw [List.flatMap_cons, ← List.flatten_replicate_singleton,
        slotShapeSummariesFrom_append,
        slotShapeSummariesFrom_flatten_replicate]
      simp only [slotShapeSummaryBlocks]
      rw [inductionHypothesis]

/-- Extensionally equal allocation states produce the same starts and remain
extensionally equal after slotting any well-formed summary sequence. -/
theorem slotShapeSummariesFrom_equivalent
    (summaries : List RegionShapeSummary)
    (left right : CircuitAllocations)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hequivalent : left.Equivalent right) :
    let leftResult := slotShapeSummariesFrom summaries left
    let rightResult := slotShapeSummariesFrom summaries right
    leftResult.1 = rightResult.1 ∧
      leftResult.2.Equivalent rightResult.2 := by
  induction summaries generalizing left right with
  | nil => exact ⟨rfl, hequivalent⟩
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      have hhead := hwellFormed.1
      have htail := hwellFormed.2
      let columns := sortRegionColumns summary.columns
      have hcolumnsNodup : columns.Nodup :=
        (sortRegionColumns_perm summary.columns).nodup_iff.mpr hhead.1
      by_cases hcolumns : summary.columns = []
      · have hsorted : columns = [] := by
          simp [columns, hcolumns, sortRegionColumns]
        simp only [slotShapeSummariesFrom, placeSummary, columns,
          hsorted, firstFit]
        have hrest := inductionHypothesis left right htail hvalidLeft
          hvalidRight hequivalent
        exact ⟨congrArg (List.cons 0) hrest.1, hrest.2⟩
      · have hlength : 0 < summary.rowCount := hhead.2 hcolumns
        have hfirst := firstFit_equivalent columns.length left right
          columns summary.rowCount 0 none hvalidLeft hvalidRight
          hcolumnsNodup hlength hequivalent
        have hleftLaw := firstFit_law columns.length left columns
          summary.rowCount 0 none hvalidLeft hcolumnsNodup hlength
        have hrightLaw := firstFit_law columns.length right columns
          summary.rowCount 0 none hvalidRight hcolumnsNodup hlength
        generalize hleft :
          firstFit columns.length left columns summary.rowCount 0 none =
            leftFirst at hfirst hleftLaw ⊢
        generalize hright :
          firstFit columns.length right columns summary.rowCount 0 none =
            rightFirst at hfirst hrightLaw ⊢
        rcases leftFirst with ⟨leftRow, leftUpdated⟩
        rcases rightFirst with ⟨rightRow, rightUpdated⟩
        dsimp only at hfirst
        have hrest := inductionHypothesis leftUpdated rightUpdated htail
          hleftLaw.1.valid hrightLaw.1.valid hfirst.2
        simp only [slotShapeSummariesFrom, placeSummary, columns,
          hleft, hright]
        rw [hfirst.1]
        exact
          ⟨congrArg (List.cons (rightRow.getD 0)) hrest.1, hrest.2⟩

/-- Placing regions with disjoint column footprints commutes: each receives the
same row, and both orders leave the same observable allocation state. -/
theorem placeSummary_commute
    (left right : RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleftNodup : left.columns.Nodup)
    (hrightNodup : right.columns.Nodup)
    (hleftLength : 0 < left.rowCount)
    (hrightLength : 0 < right.rowCount)
    (hdisjoint : List.Disjoint left.columns right.columns) :
    let leftFirst := placeSummary left allocations
    let leftThenRight := placeSummary right leftFirst.2
    let rightFirst := placeSummary right allocations
    let rightThenLeft := placeSummary left rightFirst.2
    leftFirst.1 = rightThenLeft.1 ∧
      rightFirst.1 = leftThenRight.1 ∧
      leftThenRight.2.Equivalent rightThenLeft.2 := by
  let leftColumns := sortRegionColumns left.columns
  let rightColumns := sortRegionColumns right.columns
  have hleftColumnsNodup : leftColumns.Nodup :=
    (sortRegionColumns_perm left.columns).nodup_iff.mpr hleftNodup
  have hrightColumnsNodup : rightColumns.Nodup :=
    (sortRegionColumns_perm right.columns).nodup_iff.mpr hrightNodup
  have hsortedDisjoint : List.Disjoint leftColumns rightColumns := by
    intro column hleftColumn hrightColumn
    exact hdisjoint
      ((sortRegionColumns_perm left.columns).mem_iff.mp hleftColumn)
      ((sortRegionColumns_perm right.columns).mem_iff.mp hrightColumn)
  simp only [placeSummary]
  generalize hleftFirst :
    firstFit leftColumns.length allocations leftColumns
      left.rowCount 0 none = leftFirst
  rcases leftFirst with ⟨leftRow, leftAllocations⟩
  generalize hrightFirst :
    firstFit rightColumns.length allocations rightColumns
      right.rowCount 0 none = rightFirst
  rcases rightFirst with ⟨rightRow, rightAllocations⟩
  generalize hleftThenRight :
    firstFit rightColumns.length leftAllocations rightColumns
      right.rowCount 0 none = leftThenRight
  rcases leftThenRight with
    ⟨rightRowAfterLeft, leftThenRightAllocations⟩
  generalize hrightThenLeft :
    firstFit leftColumns.length rightAllocations leftColumns
      left.rowCount 0 none = rightThenLeft
  rcases rightThenLeft with
    ⟨leftRowAfterRight, rightThenLeftAllocations⟩
  have hleftLaw := firstFit_law leftColumns.length allocations
    leftColumns left.rowCount 0 none hvalid hleftColumnsNodup hleftLength
  have hrightLaw := firstFit_law rightColumns.length allocations
    rightColumns right.rowCount 0 none hvalid hrightColumnsNodup
      hrightLength
  rw [hleftFirst] at hleftLaw
  rw [hrightFirst] at hrightLaw
  have hrightAgreement :
      allocations.AgreesOn leftAllocations rightColumns := by
    intro column hcolumn
    symm
    exact hleftLaw.1.sameOutside column (by
      intro hleftColumn
      exact hsortedDisjoint hleftColumn hcolumn)
  have hleftAgreement :
      allocations.AgreesOn rightAllocations leftColumns := by
    intro column hcolumn
    symm
    exact hrightLaw.1.sameOutside column (by
      intro hrightColumn
      exact hsortedDisjoint hcolumn hrightColumn)
  have hrightCongruent := firstFit_congruent rightColumns.length
    allocations rightColumns right.rowCount 0 none leftAllocations
    hvalid hleftLaw.1.valid hrightColumnsNodup hrightLength
    hrightAgreement
  have hleftCongruent := firstFit_congruent leftColumns.length
    allocations leftColumns left.rowCount 0 none rightAllocations
    hvalid hrightLaw.1.valid hleftColumnsNodup hleftLength hleftAgreement
  rw [hrightFirst, hleftThenRight] at hrightCongruent
  rw [hleftFirst, hrightThenLeft] at hleftCongruent
  have hleftThenRightLaw := firstFit_law rightColumns.length
    leftAllocations rightColumns right.rowCount 0 none
    hleftLaw.1.valid hrightColumnsNodup hrightLength
  have hrightThenLeftLaw := firstFit_law leftColumns.length
    rightAllocations leftColumns left.rowCount 0 none
    hrightLaw.1.valid hleftColumnsNodup hleftLength
  rw [hleftThenRight] at hleftThenRightLaw
  rw [hrightThenLeft] at hrightThenLeftLaw
  dsimp only at hrightCongruent hleftCongruent ⊢
  constructor
  · exact hleftCongruent.1
  constructor
  · exact hrightCongruent.1
  · intro column
    by_cases hleftColumn : column ∈ leftColumns
    · rw [hleftThenRightLaw.1.sameOutside column (by
            intro hrightColumn
            exact hsortedDisjoint hleftColumn hrightColumn)]
      exact hleftCongruent.2 column hleftColumn
    · by_cases hrightColumn : column ∈ rightColumns
      · rw [← hrightCongruent.2 column hrightColumn,
            hrightThenLeftLaw.1.sameOutside column hleftColumn]
      · rw [hleftThenRightLaw.1.sameOutside column hrightColumn,
            hleftLaw.1.sameOutside column hleftColumn,
            hrightThenLeftLaw.1.sameOutside column hleftColumn,
            hrightLaw.1.sameOutside column hrightColumn]

/-- Pair shapes with the starts returned in the same slotting order. -/
def placedShapes (shapes : List RegionShape)
    (pairs : List (ℕ × ℕ)) : List (RegionShape × ℕ) :=
  shapes.zip (pairs.map (·.2))

private def PlacedRecords (allocations : CircuitAllocations)
    (placed : List (RegionShape × ℕ)) : Prop :=
  ∀ item ∈ placed, ∀ column ∈ item.1.columns,
    (item.2, item.1.rowCount) ∈
      (allocations.getD column #[]).toList

private def PlacedFits (allocations : CircuitAllocations)
    (placed : List (RegionShape × ℕ)) : Prop :=
  ∀ item ∈ placed, ∀ column ∈ item.1.columns,
    (allocations.getD column #[]).Fits item.2 item.1.rowCount

/-- Pairwise row disjointness for shapes that share a planner column. -/
def PlacedDisjoint (placed : List (RegionShape × ℕ)) : Prop :=
  placed.Pairwise fun left right =>
    ∀ column, column ∈ left.1.columns → column ∈ right.1.columns →
      RowIntervalsDisjoint
        left.2 left.1.rowCount right.2 right.1.rowCount

/-- The compositional correctness interface of `slotInFrom`. -/
structure SlotInLaw
    (before : CircuitAllocations) (shapes : List RegionShape)
    (result : List (ℕ × ℕ) × CircuitAllocations) : Prop where
  valid : result.2.Valid
  preserves : before.Extends result.2
  indices : result.1.map (·.1) = shapes.map RegionShape.index
  records : PlacedRecords result.2 (placedShapes shapes result.1)
  fitsBefore : PlacedFits before (placedShapes shapes result.1)
  disjoint : PlacedDisjoint (placedShapes shapes result.1)

/-- Recursive slotting preserves allocation validity and separates shared columns. -/
theorem slotInFrom_law
    (shapes : List RegionShape) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hshapes : shapes.Forall RegionShape.WellFormed) :
    SlotInLaw allocations shapes (slotInFrom shapes allocations) := by
  induction shapes generalizing allocations with
  | nil =>
      exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          indices := rfl
          records := by simp [PlacedRecords, placedShapes]
          fitsBefore := by simp [PlacedFits, placedShapes]
          disjoint := by simp [PlacedDisjoint, placedShapes] }
  | cons shape rest inductionHypothesis =>
      rw [List.forall_cons] at hshapes
      have hcolumnsNodup : (sortRegionColumns shape.columns).Nodup :=
        (sortRegionColumns_perm shape.columns).nodup_iff.mpr
          hshapes.1.1
      by_cases hcolumns : shape.columns = []
      · have hsorted : sortRegionColumns shape.columns = [] := by
          exact List.eq_nil_iff_forall_not_mem.mpr fun column hcolumn =>
            (by simpa [hcolumns] using
              (sortRegionColumns_perm shape.columns).mem_iff.mp hcolumn)
        have hrecursive := inductionHypothesis allocations hvalid hshapes.2
        simp only [slotInFrom, hsorted, firstFit]
        refine
          { valid := hrecursive.valid
            preserves := hrecursive.preserves
            indices := by simp [hrecursive.indices]
            records := ?_
            fitsBefore := ?_
            disjoint := ?_ }
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · simp [hcolumns] at hcolumn
          · exact hrecursive.records item (by
              simpa [placedShapes] using hrest) column hcolumn
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · simp [hcolumns] at hcolumn
          · exact hrecursive.fitsBefore item (by
              simpa [placedShapes] using hrest) column hcolumn
        · unfold placedShapes PlacedDisjoint
          rw [List.map_cons, List.zip_cons_cons, List.pairwise_cons]
          exact ⟨by
            intro item hitem column hcolumn
            simp [hcolumns] at hcolumn,
            hrecursive.disjoint⟩
      · have hrowCount : 0 < shape.rowCount := hshapes.1.2 hcolumns
        obtain ⟨row, nextAllocations, hplacement⟩ :=
          firstFit_success_unbounded (sortRegionColumns shape.columns)
            allocations shape.rowCount 0 hvalid hcolumnsNodup hrowCount
        have hplacementLaw := firstFit_law
          (sortRegionColumns shape.columns).length allocations
          (sortRegionColumns shape.columns) shape.rowCount 0 none
          hvalid hcolumnsNodup hrowCount
        rw [hplacement] at hplacementLaw
        have hrecursive := inductionHypothesis nextAllocations
          hplacementLaw.1.valid hshapes.2
        simp only [slotInFrom, hplacement]
        refine
          { valid := hrecursive.valid
            preserves := hplacementLaw.1.preserves.trans
              hrecursive.preserves
            indices := by simp [hrecursive.indices]
            records := ?_
            fitsBefore := ?_
            disjoint := ?_ }
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · exact hrecursive.preserves column (row, shape.rowCount)
              (hplacementLaw.1.records row rfl column
                ((sortRegionColumns_perm shape.columns).mem_iff.mpr hcolumn))
          · exact hrecursive.records item (by
              simpa [placedShapes] using hrest) column hcolumn
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · exact hplacementLaw.1.fits row rfl column
              ((sortRegionColumns_perm shape.columns).mem_iff.mpr hcolumn)
          · intro interval hinterval
            exact hrecursive.fitsBefore item (by
                simpa [placedShapes] using hrest) column hcolumn
              interval
              (hplacementLaw.1.preserves column interval hinterval)
        · unfold placedShapes PlacedDisjoint
          rw [List.map_cons, List.zip_cons_cons, List.pairwise_cons]
          constructor
          · intro item hitem column hshapeColumn hitemColumn
            have hitemFit := hrecursive.fitsBefore item (by
              simpa [placedShapes] using hitem) column hitemColumn
            have hshapeRecord := hplacementLaw.1.records row rfl column
              ((sortRegionColumns_perm shape.columns).mem_iff.mpr
                hshapeColumn)
            exact (hitemFit (row, shape.rowCount) hshapeRecord).elim
              Or.inr Or.inl
          · exact hrecursive.disjoint

theorem placedShapes_exists_of_mem
    (shapes : List RegionShape) (pairs : List (ℕ × ℕ))
    (hindices : pairs.map (·.1) = shapes.map RegionShape.index)
    {shape : RegionShape} (hshape : shape ∈ shapes) :
    ∃ start, (shape, start) ∈ placedShapes shapes pairs := by
  induction shapes generalizing pairs with
  | nil => simp at hshape
  | cons head rest inductionHypothesis =>
      cases pairs with
      | nil => simp at hindices
      | cons pair remaining =>
          simp only [List.map_cons, List.cons.injEq] at hindices
          simp only [List.mem_cons] at hshape
          rcases hshape with rfl | hrest
          · exact ⟨pair.2, by simp [placedShapes]⟩
          · obtain ⟨start, hplaced⟩ :=
              inductionHypothesis remaining hindices.2 hrest
            exact ⟨start, by
              simp only [placedShapes, List.map_cons, List.zip_cons_cons,
                List.mem_cons]
              exact Or.inr hplaced⟩

theorem pair_mem_of_mem_placedShapes
    (shapes : List RegionShape) (pairs : List (ℕ × ℕ))
    (hindices : pairs.map (·.1) = shapes.map RegionShape.index)
    {shape : RegionShape} {start : ℕ}
    (hplaced : (shape, start) ∈ placedShapes shapes pairs) :
    (shape.index, start) ∈ pairs := by
  induction shapes generalizing pairs with
  | nil => simp [placedShapes] at hplaced
  | cons head rest inductionHypothesis =>
      cases pairs with
      | nil => simp [placedShapes] at hplaced
      | cons pair remaining =>
          simp only [List.map_cons, List.cons.injEq] at hindices
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hplaced
          rcases hplaced with hhead | htail
          · have hshape : shape = head := congrArg Prod.fst hhead
            have hstart : start = pair.2 := congrArg Prod.snd hhead
            subst shape
            subst start
            rw [List.mem_cons]
            apply Or.inl
            exact Prod.ext hindices.1.symm rfl
          · exact List.mem_cons_of_mem _
              (inductionHypothesis remaining hindices.2 htail)

/-- Distinct regions sharing any measured column occupy disjoint row intervals. -/
def SharedColumnIntervalsDisjoint
    (shapes : List RegionShape) (starts : List ℕ) : Prop :=
  ∀ ⦃left right : RegionShape⦄,
    left ∈ shapes →
    right ∈ shapes →
    left.index ≠ right.index →
    ∀ ⦃column : RegionColumn⦄,
      column ∈ left.columns →
      column ∈ right.columns →
      RowIntervalsDisjoint
        (starts.getD left.index 0) left.rowCount
        (starts.getD right.index 0) right.rowCount

/--
The semantic selector-placement invariant: distinct regions that share a virtual
selector column occupy disjoint row intervals.
-/
def SharedSelectorIntervalsDisjoint
    (shapes : List RegionShape) (starts : List ℕ) : Prop :=
  ∀ ⦃left right : RegionShape⦄,
    left ∈ shapes →
    right ∈ shapes →
    left.index ≠ right.index →
    ∀ ⦃selector : ℕ⦄,
      RegionColumn.selector selector ∈ left.columns →
      RegionColumn.selector selector ∈ right.columns →
      RowIntervalsDisjoint
        (starts.getD left.index 0) left.rowCount
        (starts.getD right.index 0) right.rowCount

theorem rel_or_reverse_of_pairwise_of_mem
    {α : Type} {relation : α → α → Prop}
    {items : List α} (hpairs : items.Pairwise relation)
    {left right : α} (hleft : left ∈ items)
    (hright : right ∈ items) (hne : left ≠ right) :
    relation left right ∨ relation right left := by
  induction items with
  | nil =>
      simp at hleft
  | cons head tail ih =>
      rw [List.pairwise_cons] at hpairs
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · contradiction
        · exact Or.inl (hpairs.1 right hright)
      · rcases hright with rfl | hright
        · exact Or.inr (hpairs.1 left hleft)
        · exact ih hpairs.2 hleft hright

/-- An operation activates selector `selector` at region-local `row`. -/
def activatesSelectorAt (selector row : ℕ) : RegionOperation F → Prop
  | operation => operation.ActivatesSelectorAt selector row

private theorem mem_addCol_self
    (columns : List RegionColumn) (column : RegionColumn) :
    column ∈ addCol columns column := by
  by_cases hcolumn : column ∈ columns <;>
    simp [addCol, addColumn, hcolumn]

private theorem mem_addCol_of_mem
    (columns : List RegionColumn) (added column : RegionColumn)
    (hcolumn : column ∈ columns) :
    column ∈ addCol columns added := by
  by_cases hadded : added ∈ columns <;>
    simp [addCol, addColumn, hadded, hcolumn]

private theorem mem_foldl_addCol_of_initial_mem
    (added : List RegionColumn) (columns : List RegionColumn)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈ added.foldl addCol columns := by
  induction added generalizing columns with
  | nil =>
      exact hcolumn
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (mem_addCol_of_mem columns head column hcolumn)

private theorem mem_foldl_addCol_of_mem
    (added : List RegionColumn) (columns : List RegionColumn)
    {column : RegionColumn} (hcolumn : column ∈ added) :
    column ∈ added.foldl addCol columns := by
  induction added generalizing columns with
  | nil =>
      simp at hcolumn
  | cons head tail ih =>
      simp only [List.mem_cons] at hcolumn
      simp only [List.foldl_cons]
      rcases hcolumn with rfl | htail
      · exact mem_foldl_addCol_of_initial_mem tail _
          (mem_addCol_self columns column)
      · exact ih (addCol columns head) htail

private theorem mem_addOperationColumns_of_mem
    (columns : List RegionColumn) (operation : RegionOperation F)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈ addOperationColumns columns operation := by
  exact mem_foldl_addCol_of_initial_mem
    (regionOperationShapeColumns operation) columns hcolumn

private theorem mem_foldl_addOperationColumns_of_initial_mem
    (body : RegionOperations F) (columns : List RegionColumn)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈ body.foldl addOperationColumns columns := by
  induction body generalizing columns with
  | nil =>
      exact hcolumn
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (mem_addOperationColumns_of_mem columns head hcolumn)

private theorem selector_mem_foldl_addOperationColumns_of_activation
    (body : RegionOperations F) (columns : List RegionColumn)
    {operation : RegionOperation F} (hoperation : operation ∈ body)
    {selector row : ℕ}
    (hactivation : activatesSelectorAt selector row operation) :
    RegionColumn.selector selector ∈
      body.foldl addOperationColumns columns := by
  induction body generalizing columns operation with
  | nil =>
      simp at hoperation
  | cons head tail ih =>
      simp only [List.mem_cons] at hoperation
      simp only [List.foldl_cons]
      rcases hoperation with rfl | htail
      · apply mem_foldl_addOperationColumns_of_initial_mem
        apply mem_foldl_addCol_of_mem
        cases operation with
        | enableGate gate operationRow =>
            rcases hactivation with ⟨rfl, rfl⟩
            simp [regionOperationShapeColumns]
        | enableLookup argument enabled operationRow =>
            rcases hactivation with ⟨⟨selected, hselected, rfl⟩, rfl⟩
            exact List.mem_map.mpr ⟨selected, hselected, rfl⟩
        | assignAdvice | assignFixed | constrainEqual | constrainConstant |
            constrainInstance =>
            contradiction
      · exact ih (addOperationColumns columns head) htail hactivation

/-- Every activated selector is a virtual column measured for its region. -/
theorem selector_mem_measureRegion_of_activatesSelectorAt
    (idx : ℕ) (body : RegionOperations F)
    {operation : RegionOperation F} (hoperation : operation ∈ body)
    {selector row : ℕ}
    (hactivation : activatesSelectorAt selector row operation) :
    RegionColumn.selector selector ∈ (measureRegion idx body).columns := by
  have hcolumn : RegionColumn.selector selector ∈
      (regionSynthesisSummary body).columns := by
    apply mem_regionSynthesisSummary_columns_of_mem body operation hoperation
    cases operation with
    | enableGate gate operationRow =>
        rcases hactivation with ⟨rfl, rfl⟩
        simp [regionOperationShapeColumns]
    | enableLookup argument enabled operationRow =>
        rcases hactivation with ⟨⟨selected, hselected, rfl⟩, rfl⟩
        exact List.mem_map.mpr ⟨selected, hselected, rfl⟩
    | assignAdvice | assignFixed | constrainEqual | constrainConstant |
        constrainInstance => contradiction
  exact hcolumn

/-- Every selector activation row lies in its measured region interval. -/
theorem row_lt_measureRegion_of_activatesSelectorAt
    (idx : ℕ) (body : RegionOperations F)
    {operation : RegionOperation F} (hoperation : operation ∈ body)
    {selector row : ℕ}
    (hactivation : activatesSelectorAt selector row operation) :
    row < (measureRegion idx body).rowCount := by
  cases operation with
  | enableGate gate operationRow =>
      rcases hactivation with ⟨_, rfl⟩
      rw [Nat.lt_iff_add_one_le]
      exact regionOperationRowExtent_le_synthesisSummary_of_mem body
        (.enableGate gate operationRow) hoperation
  | enableLookup argument enabled operationRow =>
      rcases hactivation with ⟨_, rfl⟩
      exact row_lt_measureRegion_of_enableLookup_mem
        idx body argument enabled operationRow hoperation
  | assignAdvice | assignFixed | constrainEqual | constrainConstant |
      constrainInstance =>
      contradiction

/-- Distinct regions sharing a measured column cannot contain local rows at the
same absolute position when their column intervals are disjoint. -/
theorem region_rows_ne_of_sharedColumnIntervalsDisjoint
    {shapes : List RegionShape} {starts : List ℕ}
    (hplanner : SharedColumnIntervalsDisjoint shapes starts)
    {leftIndex rightIndex : ℕ}
    {leftBody rightBody : RegionOperations F}
    (hleftShape : measureRegion leftIndex leftBody ∈ shapes)
    (hrightShape : measureRegion rightIndex rightBody ∈ shapes)
    (hindices : leftIndex ≠ rightIndex)
    {column : RegionColumn} {leftRow rightRow : ℕ}
    (hleftColumn : column ∈
      (measureRegion leftIndex leftBody).columns)
    (hrightColumn : column ∈
      (measureRegion rightIndex rightBody).columns)
    (hleftRow : leftRow < (measureRegion leftIndex leftBody).rowCount)
    (hrightRow : rightRow < (measureRegion rightIndex rightBody).rowCount) :
    starts.getD leftIndex 0 + leftRow ≠
      starts.getD rightIndex 0 + rightRow := by
  have hdisjoint :=
    hplanner hleftShape hrightShape hindices
      hleftColumn hrightColumn
  change
    RowIntervalsDisjoint
      (starts.getD leftIndex 0)
      (measureRegion leftIndex leftBody).rowCount
      (starts.getD rightIndex 0)
      (measureRegion rightIndex rightBody).rowCount at hdisjoint
  intro hequal
  rcases hdisjoint with hleftBefore | hrightBefore
  · have habsLt :
        starts.getD leftIndex 0 + leftRow <
          starts.getD leftIndex 0 +
            (measureRegion leftIndex leftBody).rowCount :=
      Nat.add_lt_add_left hleftRow _
    rw [hequal] at habsLt
    exact (Nat.not_lt_of_ge
      (hleftBefore.trans
        (Nat.le_add_right (starts.getD rightIndex 0) rightRow))) habsLt
  · have habsLt :
        starts.getD rightIndex 0 + rightRow <
          starts.getD rightIndex 0 +
            (measureRegion rightIndex rightBody).rowCount :=
      Nat.add_lt_add_left hrightRow _
    rw [← hequal] at habsLt
    exact (Nat.not_lt_of_ge
      (hrightBefore.trans
      (Nat.le_add_right (starts.getD leftIndex 0) leftRow))) habsLt

/-- Distinct regions sharing a selector column cannot contain local rows at the same
absolute position when their selector intervals are disjoint. -/
theorem region_rows_ne_of_sharedSelectorIntervalsDisjoint
    {shapes : List RegionShape} {starts : List ℕ}
    (hplanner : SharedSelectorIntervalsDisjoint shapes starts)
    {leftIndex rightIndex : ℕ}
    {leftBody rightBody : RegionOperations F}
    (hleftShape : measureRegion leftIndex leftBody ∈ shapes)
    (hrightShape : measureRegion rightIndex rightBody ∈ shapes)
    (hindices : leftIndex ≠ rightIndex)
    {selector leftRow rightRow : ℕ}
    (hleftColumn : RegionColumn.selector selector ∈
      (measureRegion leftIndex leftBody).columns)
    (hrightColumn : RegionColumn.selector selector ∈
      (measureRegion rightIndex rightBody).columns)
    (hleftRow : leftRow < (measureRegion leftIndex leftBody).rowCount)
    (hrightRow : rightRow < (measureRegion rightIndex rightBody).rowCount) :
    starts.getD leftIndex 0 + leftRow ≠
      starts.getD rightIndex 0 + rightRow := by
  have hdisjoint :=
    hplanner hleftShape hrightShape hindices hleftColumn hrightColumn
  change
    RowIntervalsDisjoint
      (starts.getD leftIndex 0)
      (measureRegion leftIndex leftBody).rowCount
      (starts.getD rightIndex 0)
      (measureRegion rightIndex rightBody).rowCount at hdisjoint
  intro hequal
  rcases hdisjoint with hleftBefore | hrightBefore
  · have habsLt :
        starts.getD leftIndex 0 + leftRow <
          starts.getD leftIndex 0 +
            (measureRegion leftIndex leftBody).rowCount :=
      Nat.add_lt_add_left hleftRow _
    rw [hequal] at habsLt
    exact (Nat.not_lt_of_ge
      (hleftBefore.trans
        (Nat.le_add_right (starts.getD rightIndex 0) rightRow))) habsLt
  · have habsLt :
        starts.getD rightIndex 0 + rightRow <
          starts.getD rightIndex 0 +
            (measureRegion rightIndex rightBody).rowCount :=
      Nat.add_lt_add_left hrightRow _
    rw [← hequal] at habsLt
    exact (Nat.not_lt_of_ge
      (hrightBefore.trans
      (Nat.le_add_right (starts.getD leftIndex 0) leftRow))) habsLt

/--
Distinct regions whose selector intervals are disjoint cannot activate the same
selector at the same absolute row.
-/
theorem activation_rows_ne_of_sharedSelectorIntervalsDisjoint
    {shapes : List RegionShape} {starts : List ℕ}
    (hplanner : SharedSelectorIntervalsDisjoint shapes starts)
    {leftIndex rightIndex : ℕ}
    {leftBody rightBody : RegionOperations F}
    (hleftShape : measureRegion leftIndex leftBody ∈ shapes)
    (hrightShape : measureRegion rightIndex rightBody ∈ shapes)
    (hindices : leftIndex ≠ rightIndex)
    {leftOperation rightOperation : RegionOperation F}
    (hleftOperation : leftOperation ∈ leftBody)
    (hrightOperation : rightOperation ∈ rightBody)
    {selector leftRow rightRow : ℕ}
    (hleftActivation :
      activatesSelectorAt selector leftRow leftOperation)
    (hrightActivation :
      activatesSelectorAt selector rightRow rightOperation) :
    starts.getD leftIndex 0 + leftRow ≠
      starts.getD rightIndex 0 + rightRow := by
  apply region_rows_ne_of_sharedSelectorIntervalsDisjoint
    hplanner hleftShape hrightShape hindices
  · exact selector_mem_measureRegion_of_activatesSelectorAt
      leftIndex leftBody hleftOperation hleftActivation
  · exact selector_mem_measureRegion_of_activatesSelectorAt
      rightIndex rightBody hrightOperation hrightActivation
  · exact row_lt_measureRegion_of_activatesSelectorAt
      leftIndex leftBody hleftOperation hleftActivation
  · exact row_lt_measureRegion_of_activatesSelectorAt
      rightIndex rightBody hrightOperation hrightActivation

/--
Under selector-interval disjointness, an absolute selector activation has a unique
source region index. Multiple source operations within that region remain harmless.
-/
theorem activation_origin_regionIndex_unique
    {regions : List (ℕ × RegionOperations F)} {starts : List ℕ}
    (hplanner :
      SharedSelectorIntervalsDisjoint
        (regions.map fun region =>
          measureRegion region.1 region.2)
        starts)
    {selector absoluteRow : ℕ}
    {leftIndex rightIndex : ℕ}
    {leftBody rightBody : RegionOperations F}
    {leftOperation rightOperation : RegionOperation F}
    {leftRow rightRow : ℕ}
    (hleftRegion : (leftIndex, leftBody) ∈ regions)
    (hrightRegion : (rightIndex, rightBody) ∈ regions)
    (hleftOperation : leftOperation ∈ leftBody)
    (hrightOperation : rightOperation ∈ rightBody)
    (hleftActivation :
      activatesSelectorAt selector leftRow leftOperation)
    (hrightActivation :
      activatesSelectorAt selector rightRow rightOperation)
    (hleftAbsolute :
      absoluteRow = starts.getD leftIndex 0 + leftRow)
    (hrightAbsolute :
      absoluteRow = starts.getD rightIndex 0 + rightRow) :
    leftIndex = rightIndex := by
  by_contra hindices
  apply activation_rows_ne_of_sharedSelectorIntervalsDisjoint
    hplanner
    (List.mem_map.mpr
      ⟨(leftIndex, leftBody), hleftRegion, rfl⟩)
    (List.mem_map.mpr
      ⟨(rightIndex, rightBody), hrightRegion, rfl⟩)
    hindices hleftOperation hrightOperation
    hleftActivation hrightActivation
  rw [← hleftAbsolute, ← hrightAbsolute]

end Halo2.FloorPlanner
