import Clean.Halo2.Pinned

/-!
# Halo2-like synthesis/layout layer

This module models the second half of Halo2 circuit construction: after
`configure` has produced a constraint system and a config object, `synthesize`
uses a layouter to assign regions, enable selectors, assign fixed/advice cells,
and add copy constraints.

The model is intentionally metadata-oriented. It records exactly the facts that
feed pinned-CS/keygen post-processing, especially selector activation vectors for
selector compression. It does not attempt to compute witness values.
-/

namespace Halo2.Synthesis

open Halo2.Pinned

structure Cell where
  column : Pinned.Column
  row : Nat
deriving Repr, DecidableEq, BEq

instance : Inhabited Cell where
  default := ⟨Pinned.Column.advice 0, 0⟩

structure AssignedCell where
  cell : Cell
deriving Repr, DecidableEq, BEq

instance : Inhabited AssignedCell where
  default := ⟨default⟩

structure RegionState where
  name : String := "anonymous"
  startRow : Nat := 0
  nextLocalRow : Nat := 0
  selectorActivations : List (Nat × Nat) := []
  fixedAssignments : List (Cell × String) := []
  copyConstraints : List (Cell × Cell) := []
deriving Repr, DecidableEq, BEq

structure Layout where
  nextRow : Nat := 0
  selectorActivations : List (Nat × Nat) := []
  fixedAssignments : List (Cell × String) := []
  copyConstraints : List (Cell × Cell) := []
deriving Repr, DecidableEq, BEq

namespace RegionState

def absoluteRow (r : RegionState) (localRow : Nat) : Nat :=
  r.startRow + localRow

def enableSelector (selector : Nat) (localRow : Nat) (r : RegionState) : RegionState :=
  { r with selectorActivations := r.selectorActivations ++ [(selector, r.absoluteRow localRow)] }

def assignAdvice (column : Pinned.Column) (localRow : Nat) (r : RegionState) : AssignedCell × RegionState :=
  let abs := r.absoluteRow localRow
  let r := { r with nextLocalRow := max r.nextLocalRow (localRow + 1) }
  (⟨⟨column, abs⟩⟩, r)

def assignFixed (column : Pinned.Column) (localRow : Nat) (value : String) (r : RegionState) : RegionState :=
  let abs := r.absoluteRow localRow
  { r with
    nextLocalRow := max r.nextLocalRow (localRow + 1)
    fixedAssignments := r.fixedAssignments ++ [(⟨column, abs⟩, value)] }

def constrainEqual (a b : AssignedCell) (r : RegionState) : RegionState :=
  { r with copyConstraints := r.copyConstraints ++ [(a.cell, b.cell)] }

end RegionState

namespace Layout

/-- Assign one Halo2 region. The region receives an absolute start row and returns
its local metadata. -/
def assignRegion {α : Type} (name : String) (body : RegionState → α × RegionState) (l : Layout) : α × Layout :=
  let region0 : RegionState := { name := name, startRow := l.nextRow }
  let (a, region) := body region0
  let l := { l with
    nextRow := l.nextRow + region.nextLocalRow
    selectorActivations := l.selectorActivations ++ region.selectorActivations
    fixedAssignments := l.fixedAssignments ++ region.fixedAssignments
    copyConstraints := l.copyConstraints ++ region.copyConstraints }
  (a, l)

/-- Assign a table region. Halo2 tables are fixed assignments and do not consume
ordinary advice-region rows in the V1 floor planner, so this records assignments
without advancing `nextRow`. -/
def assignTable (assignments : List (Pinned.Column × Nat × String)) (l : Layout) : Layout :=
  { l with fixedAssignments := l.fixedAssignments ++ assignments.map (fun (c, row, v) => (⟨c, row⟩, v)) }

/-- Enable a selector in a fresh one-row region. -/
def enableSelectorAtCurrentRow (selector : Nat) (l : Layout) : Layout :=
  let (_, l) := l.assignRegion s!"selector {selector}" fun r =>
    ((), r.enableSelector selector 0)
  l

end Layout

/-- A configured Halo2 circuit bundles a config value, a pinned-CS builder result,
and a synthesize function that records layout metadata. -/
structure ConfiguredCircuit (Config : Type) where
  config : Config
  cs : ConstraintSystem
  synthesize : Config → Layout

/-- Convert a list of selector activations into boolean rows for a circuit with
`numSelectors` selectors and at least `numRows` rows. -/
def selectorActivationTable (numSelectors numRows : Nat) (activations : List (Nat × Nat)) : List (List Bool) :=
  (List.range numSelectors).map fun selector =>
    (List.range numRows).map fun row => (selector, row) ∈ activations

/-- Number of rows needed to contain all selector activations. -/
def activationRows (activations : List (Nat × Nat)) : Nat :=
  activations.foldl (fun acc (_, row) => max acc (row + 1)) 0

end Halo2.Synthesis
