import Midnight.Keygen.ConfigureLawful
import Clean.Halo2.Keygen.FloorPlanner.Simple

/-! Source-operation bounds and selector activation closure for Midnight's
explicit-assignment fragment. These are declarative properties of the actual
operation stream. Clean lookups are the `owned` ones, with selector-free inputs, so a lookup
enables exactly its master.
Every active selector must expose all its configured equations and memberships.
Empty named gate entries (including native additive placeholders) are vacuous.
-/

namespace Midnight.Chips.OperationsLawful
open Halo2

def GateEnabled (body : RegionOperations F) (gate : Gate F) (row : Nat) : Prop :=
  .enableGate gate row ∈ body

def LookupEnabled (body : RegionOperations F) (lookup : LookupArgument F) (row : Nat) : Prop :=
  ∃ enabled, .enableLookup lookup enabled row ∈ body

/-- The same selector extraction used by layout, with start zero to retain local rows. -/
def localActivations (body : RegionOperations F) : List (Nat × Nat) :=
  Halo2.activations [0] [(0, body)]

/-- Bounds on physical assignments and selector enables. Copy provenance and
configured-object membership are the separate `CopyLawful` obligations. Advice rows are not
bounded: keygen's `assign_advice` checks nothing (keygen.rs) and the Simple planner places regions
unbounded, so Rust keys advice past the usable rows; copies of such cells are bounded by `CopyValid`. -/
def InstructionValid (counts : ConfigureCounts) (start usable : Nat) : RegionOperation F → Prop
  | .assignAdvice column _ _ => column.index < counts.numAdviceColumns
  | .assignFixed column row _ => column.index < counts.numFixedColumns ∧ start + row < usable
  | .enableGate gate row => gate.selector.index < counts.numSelectors ∧ start + row < usable
  | .enableLookup lookup enabled row =>
      enabled = [lookup.masterSelector.toSelector] ∧
      lookup.masterSelector.index < counts.numSelectors ∧ start + row < usable
  | _ => True

/-- Every active selector carries all nonvacuous configured gates and all
configured lookup tuples at that row. Registration alone proves only the reverse
inclusion. Empty gate entries impose no equations and need no enable operation. -/
def ActivationClosed (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (body : RegionOperations F) : Prop :=
  (localActivations body).Forall fun activation =>
    gates.Forall (fun gate => gate.constraints ≠ [] →
      gate.selector.index = activation.1 → GateEnabled body gate activation.2) ∧
    lookups.Forall (fun lookup => lookup.masterSelector.index = activation.1 →
      LookupEnabled body lookup activation.2)

def RegionValid (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (counts : ConfigureCounts) (starts : List Nat) (usable : Nat)
    (region : Nat) (body : RegionOperations F) : Prop :=
  region < starts.length ∧
  body.Forall (InstructionValid counts (starts.getD region 0) usable) ∧
  ActivationClosed gates lookups body

/-- Native table loading starts a default-fill pass at `values.length`; that start must be a
usable row, even for an otherwise full table. An empty load assigns nothing and fills nothing
(table_layouter.rs:121-153), as Clean's `loadTable []` states nothing. -/
def TableValid (counts : ConfigureCounts) (usable : Nat) : Operation F → Prop
  | .loadTable table values => table.inner.index < counts.numFixedColumns ∧ values.length < usable
  | _ => True

/-- The fixed columns `loadTable` fills, in stream order. An empty load marks no column used. -/
def tableColumns (ops : Operations F) : List Nat :=
  ops.filterMap fun
    | .loadTable table values => if values.isEmpty then none else some table.inner.index
    | _ => none

/-- Whether an operation is an `assignAdvice` of `cell`. -/
def assignsAdvice (cell : Cell) : RegionOperation F → Bool
  | .assignAdvice column row _ => cell.column == column.toAny && cell.rowOffset == row
  | _ => false

def instanceCopyLocal (region : Nat) (assigned : Cell → Bool) : RegionOperation F → Bool
  | .constrainInstance cell _ _ =>
      cell.regionIndex == region && cell.column.kind == .advice && assigned cell
  | _ => true

/-- Rust's only in-region instance copy is `assign_advice_from_instance`, which copies an advice
cell of its own region and assigns it. Lean's region shape counts only `assignAdvice`, so the
region must also assign that cell, before or after the copy (a cell only the copy touches would
change Rust's region height). -/
def instanceCopiesLocal (region : Nat) (body : RegionOperations F) : Bool :=
  body.all (instanceCopyLocal region fun cell => body.any (assignsAdvice cell))

structure Lawful (ops : Operations F) (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (counts : ConfigureCounts) (starts : List Nat) (usable : Nat) : Type where
  regions : (indexedRegions ops 0).1.Forall fun (region, body) =>
    RegionValid gates lookups counts starts usable region body
  tables : ops.Forall (TableValid counts usable)
  /-- Rust's layouter fails with `UsedColumn` when a table column is loaded twice. -/
  tablesDistinct : (tableColumns ops).Nodup
  instanceCopies : (indexedRegions ops 0).1.Forall fun (region, body) =>
    instanceCopiesLocal region body = true

theorem Lawful.region_exists {ops : Operations F} {gates : List (Gate F)}
    {lookups : List (LookupArgument F)} {counts : ConfigureCounts} {starts : List Nat} {usable : Nat}
    (lawful : Lawful ops gates lookups counts starts usable)
    {region : Nat} {body : RegionOperations F} (hregion : (region, body) ∈ (indexedRegions ops 0).1) :
    region < starts.length :=
  ((List.forall_iff_forall_mem.mp lawful.regions) (region, body) hregion).1

theorem Lawful.instruction_valid {ops : Operations F} {gates : List (Gate F)}
    {lookups : List (LookupArgument F)} {counts : ConfigureCounts} {starts : List Nat} {usable : Nat}
    (lawful : Lawful ops gates lookups counts starts usable)
    {region : Nat} {body : RegionOperations F} (hregion : (region, body) ∈ (indexedRegions ops 0).1)
    {instruction : RegionOperation F} (hinstruction : instruction ∈ body) :
    InstructionValid counts (starts.getD region 0) usable instruction :=
  (List.forall_iff_forall_mem.mp
    (((List.forall_iff_forall_mem.mp lawful.regions) (region, body) hregion).2.1)) instruction hinstruction

end Midnight.Chips.OperationsLawful
