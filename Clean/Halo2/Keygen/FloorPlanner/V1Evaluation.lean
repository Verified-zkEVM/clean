import Clean.Halo2.Keygen.FloorPlanner.V1Correctness

namespace Halo2.FloorPlanner.V1.CompactPlanner

open Halo2 FloorPlanner V1

/-!
# Executable evaluation of reduced V1 planner inputs

This module checks exact placements using only reduced region footprints. Its state is
an association list of occupied intervals, deliberately independent of circuit
synthesis and V1's region-sorting implementation. The final theorem connects a
successful closed evaluation to the existing declarative correctness theorem for the
actual V1 allocator.
-/

/-- Reduced per-column occupancy used by the executable evaluator. -/
abbrev Allocations := List (RegionColumn × List (Nat × Nat))

def Allocations.get : Allocations → RegionColumn → List (Nat × Nat)
  | [], _ => []
  | item :: rest, column =>
      if item.1 == column then item.2 else Allocations.get rest column

def Allocations.insertColumn :
    Allocations → RegionColumn → Nat → Nat → Allocations
  | [], column, start, length => [(column, [(start, length)])]
  | item :: rest, column, start, length =>
      if item.1 == column then
        (column, (start, length) :: item.2) :: rest
      else
        item :: Allocations.insertColumn rest column start length

def Allocations.insert :
    Allocations → List RegionColumn → Nat → Nat → Allocations
  | allocations, [], _, _ => allocations
  | allocations, column :: rest, start, length =>
      Allocations.insert
        (allocations.insertColumn column start length) rest start length

theorem Allocations.mem_get_insertColumn_iff
    (allocations : Allocations) (column query : RegionColumn)
    (start length : Nat) (interval : Nat × Nat) :
    interval ∈ (allocations.insertColumn column start length).get query ↔
      (query = column ∧ interval = (start, length)) ∨
        interval ∈ allocations.get query := by
  induction allocations with
  | nil =>
      by_cases hquery : query = column
      · subst query
        simp [insertColumn, get]
      · simp [insertColumn, get, hquery, Ne.symm hquery]
  | cons item rest inductionHypothesis =>
      rcases item with ⟨key, values⟩
      by_cases hitem : key = column
      · by_cases hquery : query = column
        · subst key
          subst query
          simp [insertColumn, get]
        · simp [insertColumn, get, hitem, hquery, Ne.symm hquery]
      · by_cases hquery : key = query
        · subst key
          simp [insertColumn, get, hitem]
        · simp [insertColumn, get, hitem, hquery, inductionHypothesis]

theorem Allocations.mem_get_insert_iff
    (allocations : Allocations) (columns : List RegionColumn)
    (query : RegionColumn) (start length : Nat) (interval : Nat × Nat) :
    interval ∈ (allocations.insert columns start length).get query ↔
      (query ∈ columns ∧ interval = (start, length)) ∨
        interval ∈ allocations.get query := by
  induction columns generalizing allocations with
  | nil => simp [insert]
  | cons column rest inductionHypothesis =>
      rw [insert, inductionHypothesis,
        mem_get_insertColumn_iff]
      aesop

def Allocations.entries (allocations : Allocations)
    (columns : List RegionColumn) : List (Nat × Nat) :=
  columns.flatMap allocations.get

def Fits (allocations : Allocations) (columns : List RegionColumn)
    (start length : Nat) : Prop :=
  (allocations.entries columns).Forall fun interval =>
    RowIntervalsDisjoint start length interval.1 interval.2

def fitsCheck (allocations : Allocations) (columns : List RegionColumn)
    (start length : Nat) : Bool :=
  (allocations.entries columns).all fun interval =>
    start + length <= interval.1 || interval.1 + interval.2 <= start

theorem fitsCheck_eq_true_iff (allocations : Allocations)
    (columns : List RegionColumn) (start length : Nat) :
    fitsCheck allocations columns start length = true ↔
      Fits allocations columns start length := by
  simp [fitsCheck, Fits, List.all_eq_true, List.forall_iff_forall_mem,
    RowIntervalsDisjoint]

def nextCandidate (allocations : Allocations)
    (columns : List RegionColumn) (start length : Nat) : Nat :=
  (allocations.entries columns).foldl (fun next interval =>
    if start + length <= interval.1 ||
        interval.1 + interval.2 <= start then next
    else max next (interval.1 + interval.2)) start

private theorem foldEnds_initial_le (items : List (Nat × Nat))
    (start length initial : Nat) :
    initial ≤ items.foldl (fun next interval =>
      if start + length <= interval.1 ||
          interval.1 + interval.2 <= start then next
      else max next (interval.1 + interval.2)) initial := by
  induction items generalizing initial with
  | nil => exact Nat.le_refl _
  | cons interval rest inductionHypothesis =>
      simp only [List.foldl_cons]
      split
      · exact inductionHypothesis initial
      · exact (Nat.le_max_left _ _).trans (inductionHypothesis _)

theorem start_le_nextCandidate (allocations : Allocations)
    (columns : List RegionColumn) (start length : Nat) :
    start ≤ nextCandidate allocations columns start length :=
  foldEnds_initial_le _ _ _ _

private theorem intervalEnd_le_foldEnds
    {interval : Nat × Nat} {items : List (Nat × Nat)}
    (start length initial : Nat) (hmember : interval ∈ items)
    (hconflict : ¬RowIntervalsDisjoint start length interval.1 interval.2) :
    interval.1 + interval.2 ≤ items.foldl (fun next item =>
      if start + length <= item.1 || item.1 + item.2 <= start then next
      else max next (item.1 + item.2)) initial := by
  induction items generalizing initial with
  | nil => simp at hmember
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmember
      simp only [List.foldl_cons]
      split
      next hdisjoint =>
        rcases hmember with rfl | htail
        · exact (hconflict (by simpa [RowIntervalsDisjoint] using hdisjoint)).elim
        · exact inductionHypothesis initial htail
      next =>
        rcases hmember with rfl | htail
        · exact (Nat.le_max_right _ _).trans
            (foldEnds_initial_le tail start length _)
        · exact inductionHypothesis _ htail

theorem nextCandidate_strict_of_not_fits
    {allocations : Allocations} {columns : List RegionColumn}
    {start length : Nat} (hnotFits : ¬Fits allocations columns start length) :
    start < nextCandidate allocations columns start length := by
  unfold Fits at hnotFits
  rw [List.forall_iff_forall_mem] at hnotFits
  push Not at hnotFits
  obtain ⟨interval, hinterval, hconflict⟩ := hnotFits
  have hend := intervalEnd_le_foldEnds start length start hinterval hconflict
  apply lt_of_lt_of_le _ hend
  unfold RowIntervalsDisjoint at hconflict
  omega

private theorem foldEnds_le (items : List (Nat × Nat))
    (start length initial bound : Nat) (hinitial : initial ≤ bound)
    (hbound : ∀ interval ∈ items,
      ¬RowIntervalsDisjoint start length interval.1 interval.2 →
        interval.1 + interval.2 ≤ bound) :
    items.foldl (fun next interval =>
      if start + length <= interval.1 ||
          interval.1 + interval.2 <= start then next
      else max next (interval.1 + interval.2)) initial ≤ bound := by
  induction items generalizing initial with
  | nil => exact hinitial
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons]
      split
      · apply inductionHypothesis initial hinitial
        intro interval hinterval
        exact hbound interval (by simp [hinterval])
      next hconflict =>
        apply inductionHypothesis
        · rw [max_le_iff]
          exact ⟨hinitial, hbound head (by simp) (by
            simpa [RowIntervalsDisjoint] using hconflict)⟩
        · intro interval hinterval
          exact hbound interval (by simp [hinterval])

theorem nextCandidate_le_of_fits
    {allocations : Allocations} {columns : List RegionColumn}
    {start length candidate : Nat} (hstart : start ≤ candidate)
    (hfits : Fits allocations columns candidate length) :
    nextCandidate allocations columns start length ≤ candidate := by
  apply foldEnds_le _ _ _ _ candidate hstart
  intro interval hinterval hconflict
  unfold Fits at hfits
  have hcandidateDisjoint := List.forall_iff_forall_mem.mp hfits
    interval hinterval
  unfold RowIntervalsDisjoint at hcandidateDisjoint hconflict
  rcases hcandidateDisjoint with hbefore | hafter
  · exfalso
    apply hconflict
    left
    omega
  · exact hafter

/-- Find the least fitting row by jumping directly past conflicting intervals. -/
def firstFit (allocations : Allocations) (columns : List RegionColumn)
    (length : Nat) : Nat → Nat → Nat
  | 0, candidate => candidate
  | fuel + 1, candidate =>
      if fitsCheck allocations columns candidate length then candidate
      else firstFit allocations columns length fuel
        (nextCandidate allocations columns candidate length)

theorem firstFit_fits_and_le
    (allocations : Allocations) (columns : List RegionColumn)
    (length target : Nat) (hTargetFits : Fits allocations columns target length) :
    ∀ fuel candidate, candidate ≤ target → target - candidate < fuel →
      Fits allocations columns
        (firstFit allocations columns length fuel candidate) length ∧
      firstFit allocations columns length fuel candidate ≤ target := by
  intro fuel
  induction fuel with
  | zero =>
      intro candidate _ hFuel
      simp at hFuel
  | succ fuel inductionHypothesis =>
      intro candidate hCandidate hFuel
      simp only [firstFit]
      split
      next hFitsCheck =>
        exact ⟨(fitsCheck_eq_true_iff _ _ _ _).mp hFitsCheck, hCandidate⟩
      next hFitsCheck =>
        have hNotFits : ¬Fits allocations columns candidate length := by
          exact fun hFits => hFitsCheck
            ((fitsCheck_eq_true_iff _ _ _ _).mpr hFits)
        have hStrict := nextCandidate_strict_of_not_fits hNotFits
        have hNext := nextCandidate_le_of_fits hCandidate hTargetFits
        apply inductionHypothesis _ hNext
        omega

def Bounded (allocations : Allocations) (endpoint : Nat) : Prop :=
  ∀ column interval, interval ∈ allocations.get column →
    interval.1 + interval.2 ≤ endpoint

theorem fits_endpoint (allocations : Allocations)
    (columns : List RegionColumn) (length endpoint : Nat)
    (hbounded : Bounded allocations endpoint) :
    Fits allocations columns endpoint length := by
  unfold Fits Allocations.entries
  rw [List.forall_iff_forall_mem]
  intro interval hinterval
  rw [List.mem_flatMap] at hinterval
  obtain ⟨column, hcolumn, hinterval⟩ := hinterval
  right
  exact hbounded column interval hinterval

def computedStart (allocations : Allocations) (endpoint : Nat)
    (columns : List RegionColumn) (length : Nat) : Nat :=
  firstFit allocations columns length (endpoint + 1) 0

theorem computedStart_fits
    (allocations : Allocations) (endpoint : Nat)
    (columns : List RegionColumn) (length : Nat)
    (hbounded : Bounded allocations endpoint) :
    Fits allocations columns
      (computedStart allocations endpoint columns length) length :=
  (firstFit_fits_and_le allocations columns length endpoint
    (fits_endpoint allocations columns length endpoint hbounded)
    (endpoint + 1) 0 (Nat.zero_le _) (by omega)).1

theorem computedStart_le_of_fits
    {allocations : Allocations} {endpoint : Nat}
    {columns : List RegionColumn} {length candidate : Nat}
    (hbounded : Bounded allocations endpoint)
    (hfits : Fits allocations columns candidate length) :
    computedStart allocations endpoint columns length ≤ candidate := by
  by_cases hcandidate : candidate ≤ endpoint
  · exact (firstFit_fits_and_le allocations columns length candidate hfits
      (endpoint + 1) 0 (Nat.zero_le _) (by omega)).2
  · have hresult := (firstFit_fits_and_le allocations columns length endpoint
      (fits_endpoint allocations columns length endpoint hbounded)
      (endpoint + 1) 0 (Nat.zero_le _) (by omega)).2
    exact hresult.trans (Nat.le_of_lt (Nat.lt_of_not_ge hcandidate))

/-- The reduced occupancy contains exactly the intervals represented by a planned prefix. -/
def Represents (allocations : Allocations)
    (placed : List PlannedSummaryBlock) : Prop :=
  ∀ column interval,
    interval ∈ allocations.get column ↔
      ∃ block ∈ placed,
        column ∈ block.summary.columns ∧
          interval = (block.start, block.count * block.summary.rowCount)

theorem empty_represents : Represents [] [] := by
  intro column interval
  simp [Allocations.get]

theorem Represents.insert
    {allocations : Allocations} {placed : List PlannedSummaryBlock}
    (hrepresents : Represents allocations placed)
    (block : PlannedSummaryBlock) :
    Represents
      (allocations.insert block.summary.columns block.start
        (block.count * block.summary.rowCount))
      (placed ++ [block]) := by
  intro column interval
  rw [Allocations.mem_get_insert_iff, hrepresents]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro (⟨hcolumn, hinterval⟩ | ⟨earlier, hearlier, hcolumn, hinterval⟩)
    · exact ⟨block, Or.inr rfl, hcolumn, hinterval⟩
    · exact ⟨earlier, Or.inl hearlier, hcolumn, hinterval⟩
  · rintro ⟨earlier, hearlier | rfl, hcolumn, hinterval⟩
    · exact Or.inr ⟨earlier, hearlier, hcolumn, hinterval⟩
    · exact Or.inl ⟨hcolumn, hinterval⟩

theorem fits_iff_fitsAfterAt
    {allocations : Allocations} {placed : List PlannedSummaryBlock}
    (hrepresents : Represents allocations placed)
    (block : PlannedSummaryBlock) (start length : Nat) :
    Fits allocations block.summary.columns start length ↔
      PlannedSummaryBlock.FitsAfterAt placed block start length := by
  unfold Fits Allocations.entries PlannedSummaryBlock.FitsAfterAt
  constructor
  · intro hfits
    rw [List.forall_iff_forall_mem] at hfits ⊢
    intro earlier hearlier
    rw [List.forall_iff_forall_mem]
    intro column hcolumn hearlierColumn
    apply hfits (earlier.start, earlier.count * earlier.summary.rowCount)
    rw [List.mem_flatMap]
    exact ⟨column, hcolumn, (hrepresents column _).mpr
      ⟨earlier, hearlier, hearlierColumn, rfl⟩⟩
  · intro hfits
    rw [List.forall_iff_forall_mem] at hfits ⊢
    intro interval hinterval
    rw [List.mem_flatMap] at hinterval
    obtain ⟨column, hcolumn, hinterval⟩ := hinterval
    obtain ⟨earlier, hearlier, hearlierColumn, rfl⟩ :=
      (hrepresents column interval).mp hinterval
    exact (List.forall_iff_forall_mem.mp
      (hfits earlier hearlier)) column hcolumn hearlierColumn

theorem Bounded.insert
    {allocations : Allocations} {endpoint : Nat}
    (hbounded : Bounded allocations endpoint)
    (block : PlannedSummaryBlock) :
    Bounded
      (allocations.insert block.summary.columns block.start
        (block.count * block.summary.rowCount))
      (max endpoint
        (block.start + block.count * block.summary.rowCount)) := by
  intro column interval hinterval
  rw [Allocations.mem_get_insert_iff] at hinterval
  rcases hinterval with ⟨_, rfl⟩ | hinterval
  · exact Nat.le_max_right _ _
  · exact (hbounded column interval hinterval).trans (Nat.le_max_left _ _)

theorem empty_bounded : Bounded [] 0 := by
  intro column interval
  simp [Allocations.get]

def columnsNodupCheck : List RegionColumn → Bool
  | [] => true
  | column :: rest =>
      !rest.contains column && columnsNodupCheck rest

theorem columnsNodupCheck_eq_true_iff (columns : List RegionColumn) :
    columnsNodupCheck columns = true ↔ columns.Nodup := by
  induction columns with
  | nil => simp [columnsNodupCheck]
  | cons column rest inductionHypothesis =>
      simp [columnsNodupCheck, List.nodup_cons, inductionHypothesis]

/-- Evaluate every proposed start in a compact trace while threading reduced occupancy. -/
def traceCheck :
    List PlannedSummaryBlock → Allocations → Nat → Bool
  | [], _, _ => true
  | block :: rest, allocations, endpoint =>
      block.count != 0 &&
      columnsNodupCheck block.summary.columns &&
      block.summary.columns != [] &&
      block.summary.rowCount != 0 &&
      computedStart allocations endpoint block.summary.columns
        block.summary.rowCount == block.start &&
      fitsCheck allocations block.summary.columns block.start
        (block.count * block.summary.rowCount) &&
      traceCheck rest
        (allocations.insert block.summary.columns block.start
          (block.count * block.summary.rowCount))
        (max endpoint
          (block.start + block.count * block.summary.rowCount))

theorem traceLawfulAfter_of_traceCheck_eq_true
    (placed trace : List PlannedSummaryBlock)
    (allocations : Allocations) (endpoint : Nat)
    (hrepresents : Represents allocations placed)
    (hbounded : Bounded allocations endpoint)
    (hcheck : traceCheck trace allocations endpoint = true) :
    PlannedSummaryBlock.TraceLawfulAfter placed trace := by
  induction trace generalizing placed allocations endpoint with
  | nil => trivial
  | cons block rest inductionHypothesis =>
      simp only [traceCheck, Bool.and_eq_true, bne_iff_ne,
        columnsNodupCheck_eq_true_iff, beq_iff_eq,
        fitsCheck_eq_true_iff] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨⟨hcount, hnodup⟩, hcolumns⟩, hrows⟩,
          hstart⟩, hfits⟩, hrest⟩
      have hcountPos : 0 < block.count := Nat.pos_of_ne_zero hcount
      have hrowsPos : 0 < block.summary.rowCount := Nat.pos_of_ne_zero hrows
      have hwellFormed : block.summary.WellFormed :=
        ⟨hnodup, fun _ => hrowsPos⟩
      have hleast : ∀ candidate,
          PlannedSummaryBlock.FitsAfterAt placed block candidate
            block.summary.rowCount → block.start ≤ candidate := by
        intro candidate hcandidate
        rw [← hstart]
        apply computedStart_le_of_fits hbounded
        exact (fits_iff_fitsAfterAt hrepresents block _ _).mpr hcandidate
      exact ⟨hcountPos, hwellFormed, hcolumns,
        (fits_iff_fitsAfterAt hrepresents block _ _).mp hfits,
        hleast,
        inductionHypothesis (placed ++ [block]) _ _
          (hrepresents.insert block) (hbounded.insert block) hrest⟩

/-- A successful reduced evaluation reproduces the actual V1 placement. -/
theorem lawful_of_traceCheck_eq_true
    (trace : List PlannedSummaryBlock)
    (hcheck : traceCheck trace [] 0 = true) :
    PlannedSummaryBlock.Lawful AllocationView.empty trace :=
  PlannedSummaryBlock.lawful_of_traceLawfulAfter [] trace (by simp)
    (traceLawfulAfter_of_traceCheck_eq_true [] trace [] 0
      empty_represents empty_bounded hcheck)

end Halo2.FloorPlanner.V1.CompactPlanner
