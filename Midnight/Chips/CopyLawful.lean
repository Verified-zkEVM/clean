import Midnight.Field
import Clean.Halo2.Operations.Keygen
import Clean.Halo2.Keygen.Layout
import Clean.Halo2.Keygen.FloorPlanner.Simple
import Clean.Halo2.Compiler.CompiledCopies
import Midnight.Chips.Planner

/-! Copy obligations for the explicit-assignment Midnight fragment: configure registration,
endpoint bounds and the placement of deferred constants. -/

namespace Midnight.Chips.CopyLawful
open Halo2

abbrev ResolvedCopy := Nat × Nat × Nat × Nat

/-- Rust pushes region `region`'s start before running its body and indexes `regions` at each copy
and constant endpoint (single_pass.rs:231, 469), so they may name regions up to `region`. -/
def regionLaidOut (region : Nat) : RegionOperation F → Bool
  | .constrainEqual left right => decide (left.regionIndex ≤ region) && decide (right.regionIndex ≤ region)
  | .constrainConstant cell _ => decide (cell.regionIndex ≤ region)
  | .constrainInstance cell _ _ => decide (cell.regionIndex ≤ region)
  | _ => true

/-- Every endpoint names a region Rust has laid out when it resolves it: a layouter instance
copy only regions before it (single_pass.rs:299). `region` counts regions; tables are not. -/
def laidOut (region : Nat) : Operations F → Bool
  | [] => true
  | .region _ body :: rest => body.all (regionLaidOut region) && laidOut (region + 1) rest
  | .constrainInstance cell _ _ :: rest => decide (cell.regionIndex < region) && laidOut region rest
  | .loadTable _ _ :: rest => laidOut region rest

private theorem mem_assignedCellsAfter {region : Nat} {cell : Cell} :
    ∀ {available : List Cell} {body : RegionOperations F},
      cell ∈ body.assignedCellsAfter region available → cell ∈ available ∨ cell.regionIndex = region
  | _, [], member => .inl member
  | available, op :: rest, member => by
    rcases mem_assignedCellsAfter (available := op.assignedCells region ++ available) member with
      old | here
    · rcases List.mem_append.mp old with new | old
      · right
        cases op <;> simp only [RegionOperation.assignedCells, List.mem_cons, List.not_mem_nil,
          or_false] at new <;> subst new <;> rfl
      · exact .inl old
    · exact .inr here

private theorem regionLaidOut_of_assigned {region : Nat} {available : List Cell}
    {body : RegionOperations F} (assigned : body.CopyCellsAssignedFrom region available) :
    (∀ cell ∈ available, cell.regionIndex ≤ region) → body.all (regionLaidOut region) = true := by
  induction assigned with
  | nil => intro _; rfl
  | assignAdvice available column row compute rest _ ih | assignFixed available column row compute rest _ ih =>
    intro bounded
    simp only [List.all_cons, regionLaidOut, Bool.true_and]
    refine ih fun cell member => ?_
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_refl _
    · exact bounded cell member
  | enableGate _ _ _ _ _ ih | enableLookup _ _ _ _ _ _ ih =>
    intro bounded
    simpa only [List.all_cons, regionLaidOut, Bool.true_and] using ih bounded
  | constrainEqual _ _ _ _ left right _ ih =>
    intro bounded
    simp only [List.all_cons, regionLaidOut, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨bounded _ left, bounded _ right⟩, ih bounded⟩
  | constrainConstant _ _ _ _ member _ ih | constrainInstance _ _ _ _ _ member _ ih =>
    intro bounded
    simp only [List.all_cons, regionLaidOut, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨bounded _ member, ih bounded⟩

/-- Copy provenance (every endpoint assigned before its copy) implies `laidOut`. -/
theorem laidOut_of_assigned {ops : Operations F} (assigned : ops.CopyCellsAssigned 0 []) :
    laidOut 0 ops = true := by
  suffices ∀ {region available} {ops : Operations F}, ops.CopyCellsAssignedFrom region available →
      (∀ cell ∈ available, cell.regionIndex < region) → laidOut region ops = true from
    this assigned (by simp)
  intro region available ops assigned
  induction assigned with
  | nil => intro _; rfl
  | region region available _ body rest hbody _ ih =>
    intro bounded
    simp only [laidOut, Bool.and_eq_true]
    refine ⟨regionLaidOut_of_assigned hbody fun cell member => Nat.le_of_lt (bounded cell member),
      ih fun cell member => ?_⟩
    rcases mem_assignedCellsAfter member with old | here
    · exact Nat.lt_succ_of_lt (bounded cell old)
    · rw [here]; exact Nat.lt_succ_self _
  | constrainInstance _ _ _ _ _ _ member _ ih =>
    intro bounded
    simp only [laidOut, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨bounded _ member, ih bounded⟩
  | loadTable _ _ _ _ _ _ ih =>
    intro bounded
    exact ih bounded

def RegionNoDeferredConstants (ops : RegionOperations F) : Prop :=
  ∀ cell value, .constrainConstant cell value ∉ ops

def NoDeferredConstants (ops : Operations F) : Prop :=
  ∀ name body, .region name body ∈ ops → RegionNoDeferredConstants body

/-- Rust's constants pass succeeds: a queued constant needs a constants column (else
`NotEnoughColumnsForConstants`), and `assign_fixed` and `copy` need its row to be usable. V1
needs a free position for every queued constant (v1.rs:118-120). -/
def ConstantsPlaced (ops : Operations F) (constant : Option Nat) (usable : Nat)
    (planner : Layout.Planner := .simple) : Prop :=
  match planner, constant with
  | .simple, none => NoDeferredConstants ops
  | .simple, some column => (FloorPlanner.SimpleFloorPlanner.plan column ops).constants.Forall
      fun placed => placed.2.2 < usable
  | .v1 columns, _ => (operationConstSites ops).length ≤ (Layout.v1Positions columns ops).length ∧
      ((Layout.Planner.v1 columns).constants constant ops).Forall fun placed => placed.2.2 < usable

/-- Simple resolves an endpoint when it is reached (`laidOut`); V1 has placed every region before
it synthesizes (v1.rs:79-81), so only `EndpointValid`'s region count applies. -/
def plannerLaidOut (planner : Layout.Planner) (ops : Operations F) : Bool :=
  match planner with
  | .simple => laidOut 0 ops
  | .v1 _ => true

/-- Source bounds for an upstream semantic endpoint. A deferred literal's own row is
`ConstantsPlaced`'s. -/
def EndpointValid (permutation : List Halo2.Layout.ColRef) (starts : List Nat)
    (usable : Nat) : CopyEndpoint F → Prop
  | .cell c => c.column ∈ permutation.map Halo2.Layout.ColRef.toAny ∧
      c.regionIndex < starts.length ∧ Halo2.Layout.place starts c.regionIndex + c.rowOffset < usable
  | .instance column row => column.toAny ∈ permutation.map Halo2.Layout.ColRef.toAny ∧ row < usable
  | .constant _ => True

/-- Ordinary endpoints retain column, region and usable-row bounds. A constant request
bounds its cell, which Rust copies to the constants column. -/
def CopyValid (permutation : List Halo2.Layout.ColRef) (starts : List Nat)
    (usable : Nat) : DeclaredCopy F → Prop
  | (.cell cell, .constant _) => EndpointValid permutation starts usable (.cell cell)
  | (left, right) => EndpointValid permutation starts usable left ∧
      EndpointValid permutation starts usable right

/-- Source bounds are checked on upstream's declaration stream. -/
def EndpointsValid (ops : Operations F) (permutation : List Halo2.Layout.ColRef)
    (starts : List Nat) (usable : Nat) : Prop :=
  (operationDeclaredCopies ops).Forall (CopyValid permutation starts usable)

/-- Decide Clean's registration predicate directly; it is the single source
of truth for the executable registration check and its correctness contract. -/
private def registrationDecision (ops : Operations F) (gates : List (Gate F))
    (lookups : List (LookupArgument F)) (fixed : List (Column .fixed))
    (permutation : List AnyColumn) :
    Decidable (ops.KeygenRegistered gates lookups fixed permutation) := by
  letI : DecidablePred (RegionOperation.KeygenRegistered gates lookups fixed permutation) :=
    fun instruction => by
      cases instruction <;> dsimp [RegionOperation.KeygenRegistered] <;> infer_instance
  letI : DecidablePred (Operation.KeygenRegistered gates lookups fixed permutation) :=
    fun operation => by
      cases operation <;> dsimp [Operation.KeygenRegistered] <;> infer_instance
  unfold Operations.KeygenRegistered
  infer_instance

def registered (ops : Operations F) (gates : List (Gate F))
    (lookups : List (LookupArgument F)) (fixed : List (Column .fixed))
    (permutation : List AnyColumn) : Bool :=
  @decide _ (registrationDecision ops gates lookups fixed permutation)

/-- Bounded copy extraction. Endpoints need not be assigned: Rust's keygen and MockProver record
any copy between usable cells (keygen.rs:142-154), the prover reading 0 at an unassigned cell. -/
structure Lawful (ops : Operations F) (gates : List (Gate F))
    (lookups : List (LookupArgument F)) (fixed : List (Column .fixed))
    (permutation : List Halo2.Layout.ColRef) (starts : List Nat) (usable : Nat)
    (constant : Option Nat) (planner : Layout.Planner := .simple) : Type where
  registered : ops.KeygenRegistered gates lookups fixed (permutation.map Halo2.Layout.ColRef.toAny)
  laidOut : plannerLaidOut planner ops = true
  constants : ConstantsPlaced ops constant usable planner
  endpoints : EndpointsValid ops permutation starts usable

end Midnight.Chips.CopyLawful
