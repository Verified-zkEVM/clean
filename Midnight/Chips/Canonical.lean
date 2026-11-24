import Midnight.Chips.OperationsLawful

/-! Rust's reading of an operation stream. Rust enables selectors, not gates: `q.enable` switches
on every gate and lookup on `q`, and `assign_advice_from_instance` assigns the cell it copies. So
Rust keys streams that enable only some of a selector's gates or lookups, enable an unconfigured
gate on a configured selector, or copy an instance into a cell nothing else assigns. `ops` restates
such a stream with the same selector rows, region shapes and copies, hence Rust's key, in the form
the certificate admits (`ActivationClosed`, `KeygenRegistered`, `instanceCopiesLocal`); Lean's
lowering derives the key of `ops`. Its Clean meaning is Rust's: every gate and lookup on an enabled
selector is stated. -/

namespace Midnight.Chips.Canonical
open Halo2 Midnight.Keygen

/-- What `q.enable` at `row` switches on: every configured gate with constraints and every lookup
on `q`, or a configured constraint-free gate on `q` (a handle) if there are none. `none` when
nothing configured is on `q`, so the caller keeps its operation (and the certificate rejects it). -/
def selectorEnables (gates : List (Gate F)) (lookups : List (LookupArgument F)) (q row : Nat) :
    Option (List (RegionOperation F)) :=
  let on := (gates.filter fun g => g.selector.index == q && !g.constraints.isEmpty).map
      (.enableGate · row) ++
    (lookups.filter (·.masterSelector.index == q)).map fun l =>
      .enableLookup l [l.masterSelector.toSelector] row
  if on.isEmpty then ((gates.find? (·.selector.index == q)).map fun g => [.enableGate g row])
  else some on

/-- One region: each selector activation's enables at its first enable, and an `assignAdvice` (of
the instance value, as Rust's) before an instance copy of an own advice cell nothing assigns. -/
def regionBody (gates : List (Gate F)) (lookups : List (LookupArgument F)) (region : Nat)
    (body : RegionOperations F) : RegionOperations F :=
  let activate := fun (acc : List (Nat × Nat) × Array (RegionOperation F)) op (q row : Nat) =>
    if acc.1.contains (q, row) then acc
    else match selectorEnables gates lookups q row with
      | some ops => ((q, row) :: acc.1, acc.2 ++ ops.toArray)
      | none => (acc.1, acc.2.push op)
  (body.foldl (init := ([], #[])) fun acc op => match op with
    | .enableGate g row => activate acc op g.selector.index row
    | .enableLookup _ enabled row => enabled.foldl (fun acc s => activate acc op s.index row) acc
    | .constrainInstance cell column row =>
        if cell.regionIndex == region && cell.column.kind == .advice &&
            !body.any (OperationsLawful.assignsAdvice cell) &&
            !acc.2.any (OperationsLawful.assignsAdvice cell) then
          (acc.1, (acc.2.push (.assignAdvice ⟨cell.column.index⟩ cell.rowOffset
            (instanceGet column row))).push op)
        else (acc.1, acc.2.push op)
    | op => (acc.1, acc.2.push op)).2.toList

/-- The stream Lean lowers, from region index `i`. -/
def ops (gates : List (Gate F)) (lookups : List (LookupArgument F)) (i : Nat := 0) :
    Operations F → Operations F
  | [] => []
  | .region name body :: rest => .region name (regionBody gates lookups i body) :: ops gates lookups (i + 1) rest
  | op :: rest => op :: ops gates lookups i rest

local instance (e : E) (queries : List Halo2.Query) : Decidable (e.QueriesDeclared (queries.map (.var ·))) :=
  decidable_of_iff _ (Halo2.Expression.declared_iff e queries)

local instance (s : CS) (g : GateSpec) : Decidable (g.Lawful s) := by
  unfold GateSpec.Lawful; infer_instance

local instance (s : CS) (l : BatchedLookup) : Decidable (l.Lawful s) := by
  unfold BatchedLookup.Lawful Halo2.Expression.Registered; infer_instance

local instance (s : CS) : Decidable s.WellFormed := decidable_of_iff _ (CS.wellFormed_iff s).symm

/-- `CS.WellFormed`, decided: the certificate's `configuration`. -/
def checked? (s : CS) : Option CS.Checked :=
  if h : s.WellFormed then some ⟨s, h⟩ else none

/-- The stream Lean keys for `stream`: Rust's reading of it when the source is well formed. The
certificate is for this stream, and `Export.layout` lowers it. -/
def rustOps (source : CS) (stream : Operations F) : Operations F :=
  match checked? source with
  | some c => ops c.toCleanDelta.gates c.toCleanDelta.lookups 0 stream
  | none => stream

end Midnight.Chips.Canonical
