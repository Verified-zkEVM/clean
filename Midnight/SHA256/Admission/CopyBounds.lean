import Midnight.Chips.CopyLawful
import Midnight.Chips.OperationsLawful
import Midnight.SHA256.Admission.OperationBounds

/-! Physical copy bounds from actual assignment provenance. The proof follows
copied cells back to real writes, and checks public rows separately. -/
namespace Midnight.SHA256.Admission.CopyBounds
open Halo2 Midnight.Chips

def CellRows (starts : List Nat) (usable : Nat) (cell : Cell) : Prop :=
  cell.regionIndex < starts.length ∧ starts.getD cell.regionIndex 0 + cell.rowOffset < usable

def RegionPublicRows (usable : Nat) (body : RegionOperations F) : Prop :=
  ∀ cell column row, .constrainInstance cell column row ∈ body → row < usable

def PublicRows (usable : Nat) : Operation F → Prop
  | .region _ body => RegionPublicRows usable body
  | .constrainInstance _ _ row => row < usable
  | .loadTable _ _ => True

private theorem regionEndpoints (body : RegionOperations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) (fixed : List (Column .fixed))
    (permutation : List Halo2.Layout.ColRef) (starts : List Nat) (usable : Nat)
    (registered : body.Forall (RegionOperation.KeygenRegistered gates lookups fixed
      (permutation.map Halo2.Layout.ColRef.toAny)))
    (rows : ∀ cell ∈ body.copiedCells, CellRows starts usable cell)
    (publicRows : RegionPublicRows usable body) :
    ∀ copy ∈ Halo2.regionDeclaredCopies body,
      CopyLawful.CopyValid permutation starts usable copy := by
  induction body with
  | nil => simp [Halo2.regionDeclaredCopies]
  | cons op rest ih =>
    obtain ⟨registered, tail⟩ := (List.forall_cons _ _ _).mp registered
    have restRows : ∀ cell ∈ RegionOperations.copiedCells rest, CellRows starts usable cell := by
      intro cell member
      exact rows cell (List.mem_append_right _ member)
    have restPublic : RegionPublicRows usable rest := by
      intro cell col row member
      exact publicRows cell col row (List.mem_cons_of_mem _ member)
    have later := ih tail restRows restPublic
    cases op with
    | constrainEqual left right =>
      intro copy member
      rcases List.mem_cons.mp member with rfl | member
      · have leftRows := rows left (by simp [RegionOperations.copiedCells, RegionOperation.copiedCells])
        have rightRows := rows right (by simp [RegionOperations.copiedCells, RegionOperation.copiedCells])
        exact ⟨⟨registered.1,leftRows⟩,⟨registered.2,rightRows⟩⟩
      · exact later copy member
    | constrainInstance cell column row =>
      intro copy member
      rcases List.mem_cons.mp member with rfl | member
      · have cellRows := rows cell (by simp [RegionOperations.copiedCells, RegionOperation.copiedCells])
        exact ⟨⟨registered.1,cellRows⟩,⟨registered.2,publicRows cell column row (by simp)⟩⟩
      · exact later copy member
    | constrainConstant cell value =>
      intro copy member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨registered, rows cell (by simp [RegionOperations.copiedCells, RegionOperation.copiedCells])⟩
      · exact later copy member
    | assignAdvice | assignFixed | enableGate | enableLookup => exact later

private theorem endpoints (ops : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) (fixed : List (Column .fixed))
    (permutation : List Halo2.Layout.ColRef) (starts : List Nat) (usable : Nat)
    (registered : ops.KeygenRegistered gates lookups fixed (permutation.map Halo2.Layout.ColRef.toAny))
    (rows : ∀ cell ∈ ops.copiedCells, CellRows starts usable cell)
    (publicRows : ops.Forall (PublicRows usable)) :
    CopyLawful.EndpointsValid ops permutation starts usable := by
  rw [CopyLawful.EndpointsValid, List.forall_iff_forall_mem]
  induction ops with
  | nil => simp [Halo2.operationDeclaredCopies]
  | cons op rest ih =>
    obtain ⟨registered,tail⟩ := (List.forall_cons _ _ _).mp registered
    obtain ⟨publicRows,restPublic⟩ := (List.forall_cons _ _ _).mp publicRows
    have restRows : ∀ cell ∈ Operations.copiedCells rest, CellRows starts usable cell := by
      intro cell member
      exact rows cell (List.mem_append_right _ member)
    have later := ih tail restRows restPublic
    cases op with
    | region name body =>
      intro copy member
      rcases List.mem_append.mp member with here | there
      · exact regionEndpoints body gates lookups fixed permutation starts usable registered
          (fun cell member => rows cell (List.mem_append_left _ member)) publicRows copy here
      · exact later copy there
    | constrainInstance cell column row =>
      intro copy member
      rcases List.mem_cons.mp member with rfl | member
      · have cellRows := rows cell (by simp [Operations.copiedCells, Operation.copiedCells])
        exact ⟨⟨registered.1,cellRows⟩,⟨registered.2,publicRows⟩⟩
      · exact later copy member
    | loadTable => exact later

private theorem assignedCellsFrom (ops : Operations F) (self : Nat) :
    ops.assignedCellsFrom self =
      (indexedRegions ops self).1.flatMap (fun pair => pair.2.assignedCells pair.1) := by
  induction ops generalizing self with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp only [Operations.assignedCellsFrom, indexedRegions, List.flatMap_cons, ih]

theorem assignedRows (ops : Operations F) (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (counts : ConfigureCounts) (starts : List Nat) (usable : Nat)
    (lawful : OperationsLawful.Lawful ops gates lookups counts starts usable)
    (assignedRows : (indexedRegions ops 0).1.Forall fun (region, body) =>
      body.Forall (OperationBounds.AssignedRow (starts.getD region 0) usable))
    (cell : Cell) (member : cell ∈ ops.assignedCellsFrom 0) : CellRows starts usable cell := by
  rw [assignedCellsFrom, List.mem_flatMap] at member
  obtain ⟨⟨index,body⟩,region,member⟩ := member
  obtain ⟨operation,source,assigned⟩ := List.mem_flatMap.mp member
  have regionBound := lawful.region_exists region
  have row := List.forall_iff_forall_mem.mp
    ((List.forall_iff_forall_mem.mp assignedRows) (index, body) region) operation source
  cases operation <;> simp only [RegionOperation.assignedCells, List.not_mem_nil] at assigned
  all_goals
    obtain rfl := List.mem_singleton.mp assigned
    exact ⟨regionBound, row⟩

/-- Provenance supplies the bound on every regional endpoint, even when it refers
back to an earlier region. Public instance rows are checked in the actual stream. -/
theorem from_provenance (ops : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) (fixed : List (Column .fixed))
    (permutation : List Halo2.Layout.ColRef) (counts : ConfigureCounts)
    (starts : List Nat) (usable : Nat)
    (registered : ops.KeygenRegistered gates lookups fixed (permutation.map Halo2.Layout.ColRef.toAny))
    (assigned : ops.CopyCellsAssigned 0 [])
    (lawful : OperationsLawful.Lawful ops gates lookups counts starts usable)
    (rows : (indexedRegions ops 0).1.Forall fun (region, body) =>
      body.Forall (OperationBounds.AssignedRow (starts.getD region 0) usable))
    (publicRows : ops.Forall (PublicRows usable)) :
    CopyLawful.EndpointsValid ops permutation starts usable := by
  apply endpoints ops gates lookups fixed permutation starts usable registered ?_ publicRows
  intro cell member
  have source := ops.copyCellsCovered_of_assigned 0 [] assigned cell member
  exact assignedRows ops gates lookups counts starts usable lawful rows cell source

end Midnight.SHA256.Admission.CopyBounds
