import Clean.Halo2.Operations.Copy

/-! Region-indexed, execution-order-sensitive copy provenance. The supplied
assignment table is checked against each actual region before its entries become
available. Within the current region only earlier writes are usable. -/
namespace Midnight.Math.Operations.RegionalCopy
open Halo2
variable {F : Type}
abbrev Key := AnyColumn × Nat
abbrev Table := Array (List Key)
def cellKey (cell : Cell) : Key := (cell.column, cell.rowOffset)
def atRegion (region : Nat) (key : Key) : Cell := ⟨region, key.2, key.1⟩

def writes : RegionOperations F → List Key
  | [] => []
  | .assignAdvice column row _ :: rest => (column.toAny,row) :: writes rest
  | .assignFixed column row _ :: rest => (column.toAny,row) :: writes rest
  | _ :: rest => writes rest

/-- Candidate data only: `check` also verifies each table entry from the source. -/
def table (ops : Operations F) : Table :=
  (ops.filterMap fun op => match op with | .region _ body => some (writes body) | _ => none).toArray

def has (table : Table) (region : Nat) (seen : List Key) (cell : Cell) : Bool :=
  if cell.regionIndex == region then decide (cellKey cell ∈ seen)
  else decide (cell.regionIndex < region) && decide (cellKey cell ∈ table[cell.regionIndex]!)

def regionCheck (table : Table) (index : Nat) (seen : List Key) : RegionOperations F → Bool
  | [] => true
  | .assignAdvice column row _ :: rest => regionCheck table index ((column.toAny,row)::seen) rest
  | .assignFixed column row _ :: rest => regionCheck table index ((column.toAny,row)::seen) rest
  | .constrainEqual left right :: rest =>
      has table index seen left && has table index seen right && regionCheck table index seen rest
  | .constrainConstant cell _ :: rest | .constrainInstance cell _ _ :: rest =>
      has table index seen cell && regionCheck table index seen rest
  | _ :: rest => regionCheck table index seen rest

def check (table : Table) (index : Nat) : Operations F → Bool
  | [] => true
  | .region _ body :: rest =>
      decide (table[index]! = writes body) && regionCheck table index [] body && check table (index+1) rest
  | .constrainInstance cell _ _ :: rest => has table index [] cell && check table index rest
  | .loadTable _ _ :: rest => check table index rest

theorem check_append (table : Table) (index : Nat) (left right : Operations F) :
    check table index (left ++ right) =
      (check table index left && check table (index + left.regionCount) right) := by
  induction left generalizing index with
  | nil => simp only [List.nil_append, check, Operations.regionCount, Nat.add_zero, Bool.true_and]
  | cons op rest ih =>
    cases op <;> simp only [List.cons_append, check, Operations.regionCount, ih,
      Bool.and_assoc, Nat.add_assoc]

private def Covers (table : Table) (region : Nat) (available : List Cell) : Prop :=
  ∀ cell, cell.regionIndex < region → cellKey cell ∈ table[cell.regionIndex]! → cell ∈ available
private def LocalCovers (region : Nat) (seen : List Key) (available : List Cell) : Prop :=
  ∀ key ∈ seen, atRegion region key ∈ available

private theorem has_sound (table : Table) (region : Nat) (seen : List Key)
    (available : List Cell) (covered : Covers table region available)
    (localCovered : LocalCovers region seen available) (cell : Cell)
    (accepted : has table region seen cell = true) : cell ∈ available := by
  unfold has at accepted
  split at accepted
  · rename_i same
    have member := localCovered (cellKey cell) (of_decide_eq_true accepted)
    have same := beq_iff_eq.mp same
    have cell_eq : atRegion region (cellKey cell) = cell := by
      cases cell
      simp_all [atRegion, cellKey]
    exact cell_eq ▸ member
  · exact covered cell (of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).1)
      (of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).2)

private theorem covers_cons {table : Table} {region : Nat} {available : List Cell}
    (covered : Covers table region available) (new : Cell) : Covers table region (new::available) := by
  intro cell bound member
  exact List.mem_cons_of_mem _ (covered cell bound member)

private theorem local_cons {region : Nat} {seen : List Key} {available : List Cell}
    (covered : LocalCovers region seen available) (new : Key) :
    LocalCovers region (new::seen) (atRegion region new::available) := by
  intro key member
  rcases List.mem_cons.mp member with rfl | member
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (covered key member)

private theorem region_refines (table : Table) (index : Nat) (seen : List Key)
    (available : List Cell) (ops : RegionOperations F)
    (covered : Covers table index available) (localCovered : LocalCovers index seen available)
    (accepted : regionCheck table index seen ops = true) :
    ops.CopyCellsAssignedFrom index available := by
  induction ops generalizing seen available with
  | nil => exact .nil available
  | cons op rest ih =>
    cases op with
    | assignAdvice column row value =>
      exact .assignAdvice _ _ _ _ _ (ih _ _ (covers_cons covered _) (local_cons localCovered _) accepted)
    | assignFixed column row value =>
      exact .assignFixed _ _ _ _ _ (ih _ _ (covers_cons covered _) (local_cons localCovered _) accepted)
    | enableGate gate row => exact .enableGate _ _ _ _ (ih _ _ covered localCovered accepted)
    | enableLookup lookup selectors row => exact .enableLookup _ _ _ _ _ (ih _ _ covered localCovered accepted)
    | constrainEqual left right =>
      obtain ⟨⟨leftOK,rightOK⟩,tail⟩ := Bool.and_eq_true_iff.mp accepted |>.imp_left Bool.and_eq_true_iff.mp
      exact .constrainEqual _ _ _ _ (has_sound _ _ _ _ covered localCovered _ leftOK)
        (has_sound _ _ _ _ covered localCovered _ rightOK) (ih _ _ covered localCovered tail)
    | constrainConstant cell value =>
      obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp accepted
      exact .constrainConstant _ _ _ _ (has_sound _ _ _ _ covered localCovered _ head)
        (ih _ _ covered localCovered tail)
    | constrainInstance cell column row =>
      obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp accepted
      exact .constrainInstance _ _ _ _ _ (has_sound _ _ _ _ covered localCovered _ head)
        (ih _ _ covered localCovered tail)

theorem assigned_eq (ops : RegionOperations F) (index : Nat) :
    ops.assignedCells index = (writes ops).map (atRegion index) := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp only [RegionOperations.assignedCells, List.flatMap_cons,
      RegionOperation.assignedCells, writes, List.map_cons, List.singleton_append,
      List.nil_append] at *
    all_goals first | exact ih | exact congrArg (List.cons _) ih

private theorem covers_next (table : Table) (index : Nat) (available : List Cell)
    (body : RegionOperations F) (covered : Covers table index available)
    (entry : table[index]! = writes body) :
    Covers table (index+1) (body.assignedCellsAfter index available) := by
  intro cell bound member
  change cell.regionIndex < index + 1 at bound
  rw [RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  by_cases old : cell.regionIndex < index
  · exact Or.inl (covered cell old member)
  · have same : cell.regionIndex = index :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp bound) (Nat.le_of_not_gt old)
    right
    rw [same, entry] at member
    rw [assigned_eq, List.mem_map]
    refine ⟨cellKey cell, member, ?_⟩
    cases cell
    simp_all [cellKey, atRegion]

private theorem check_refines (table : Table) (index : Nat) (available : List Cell)
    (ops : Operations F) (covered : Covers table index available)
    (accepted : check table index ops = true) : ops.CopyCellsAssignedFrom index available := by
  induction ops generalizing index available with
  | nil => exact .nil _ _
  | cons op rest ih =>
    cases op with
    | region name body =>
      obtain ⟨⟨entry,head⟩,tail⟩ := Bool.and_eq_true_iff.mp accepted |>.imp_left Bool.and_eq_true_iff.mp
      exact .region _ _ _ _ _ (region_refines _ _ [] _ _ covered (by intro key member; cases member) head)
        (ih _ _ (covers_next _ _ _ _ covered (of_decide_eq_true entry)) tail)
    | constrainInstance cell column row =>
      obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp accepted
      exact .constrainInstance _ _ _ _ _ _
        (has_sound _ _ [] _ covered (by intro key member; cases member) _ head)
        (ih _ _ covered tail)
    | loadTable column values => exact .loadTable _ _ _ _ _ (ih _ _ covered accepted)

/-- Accepted metadata establishes Clean's original ordered copy predicate. -/
theorem sound (table : Table) (ops : Operations F) (accepted : check table 0 ops = true) :
    ops.CopyCellsAssignedFrom 0 [] :=
  check_refines table 0 [] ops (by intro cell bound; omega) accepted

end Midnight.Math.Operations.RegionalCopy
