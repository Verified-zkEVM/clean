import Midnight.Field
import Midnight.Chips.V1
import Clean.Halo2.Keygen.FloorPlanner.Simple
import Clean.Halo2.Compiler.CompiledCopies

/-! The floor planners Rust ships: where each places regions and deferred constants. -/

namespace Midnight.Chips.Layout
open Halo2

def simpleStarts (ops : Operations F) : List Nat := FloorPlanner.SimpleFloorPlanner.starts ops

/-- Rust's floor planners, a closed choice, not a caller-supplied starts vector. `v1` carries
the constants columns (`cs.constants`), which V1 fills in order; Simple uses only the first. -/
inductive Planner where
  | simple
  | v1 (constants : List Nat)
  deriving DecidableEq, Repr

/-- V1's constant positions (v1.rs:89-108): each constants column's rows below
`first_unassigned_row` that no region allocated, columns in order. -/
def v1Positions (columns : List Nat) (ops : Operations F) : List (Nat × Nat) :=
  let allocations := (Midnight.Chips.V1.plan ops).2
  let endRow := Halo2.FloorPlanner.V1.firstUnassignedRow allocations
  columns.flatMap fun column =>
    (Halo2.FloorPlanner.V1.freeRows allocations column endRow).map (column, ·)

/-- Region starts given `constants[0]`. Without a constants column Rust's constants pass
places nothing, and a queued constant is an error that admission rejects. V1 measures every
region first and places them biggest advice area first (v1.rs:79-81). -/
def Planner.starts (planner : Planner) (constant : Option Nat) (ops : Operations F) : List Nat :=
  match planner, constant with
  | .simple, none => simpleStarts ops
  | .simple, some column => (FloorPlanner.SimpleFloorPlanner.plan column ops).starts
  | .v1 _, _ => Midnight.Chips.V1.starts ops

/-- The constants pass's `(value, column, row)` per `constrainConstant`, in region then body
order, the allocation map `copyList` consumes. V1 zips its positions with every queued constant
after synthesis (v1.rs:118-138); a shortfall is `NotEnoughColumnsForConstants`, which
admission rejects. -/
def Planner.constants (planner : Planner) (constant : Option Nat) (ops : Operations F) :
    List (Nat × Nat × Nat) :=
  match planner, constant with
  | .simple, none => []
  | .simple, some column => (FloorPlanner.SimpleFloorPlanner.plan column ops).constants.map
      fun (value, column, row) => (scalarNat value, column, row)
  | .v1 columns, _ => ((v1Positions columns ops).zip (operationConstSites ops)).map
      fun ((column, row), (_, value)) => (scalarNat value, column, row)

end Midnight.Chips.Layout
