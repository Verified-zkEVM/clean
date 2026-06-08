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
  selectorKinds : List Halo2.Pinned.SelectorKind := []
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

namespace Halo2.Synthesis

abbrev ConfigureM := StateM Halo2.Pinned.Builder
abbrev SynthesizeM := StateM Layout
abbrev RegionM := StateM RegionState

namespace ConfigureM

def adviceColumn : ConfigureM Halo2.Pinned.Column := do
  let b ← get
  let (c, b) := b.adviceColumn
  set b
  pure c

def fixedColumn : ConfigureM Halo2.Pinned.Column := do
  let b ← get
  let (c, b) := b.fixedColumn
  set b
  pure c

def instanceColumn : ConfigureM Halo2.Pinned.Column := do
  let b ← get
  let (c, b) := b.instanceColumn
  set b
  pure c

def selector : ConfigureM Nat := do
  let b ← get
  let (s, b) := b.selector
  set b
  pure s

def complexSelector : ConfigureM Nat := do
  let b ← get
  let (s, b) := b.complexSelector
  set b
  pure s

def modifyBuilder (f : Halo2.Pinned.Builder → Halo2.Pinned.Builder) : ConfigureM Unit := do
  modify f

def createGate (polys : List Halo2.Pinned.Expression) : ConfigureM Unit :=
  modifyBuilder (·.createGate polys)

def lookup (arg : Halo2.Pinned.LookupArgument) : ConfigureM Unit :=
  modifyBuilder (·.lookup arg)

end ConfigureM

namespace RegionM

def enableSelector (selector row : Nat) : RegionM Unit :=
  modify (RegionState.enableSelector selector row)

def assignAdvice (column : Halo2.Pinned.Column) (row : Nat) : RegionM AssignedCell := do
  let r ← get
  let (cell, r) := r.assignAdvice column row
  set r
  pure cell

def assignFixed (column : Halo2.Pinned.Column) (row : Nat) (value : String) : RegionM Unit :=
  modify (RegionState.assignFixed column row value)

def constrainEqual (a b : AssignedCell) : RegionM Unit :=
  modify (RegionState.constrainEqual a b)

end RegionM

namespace SynthesizeM

def assignRegion {α : Type} (name : String) (body : RegionM α) : SynthesizeM α := do
  let l ← get
  let (a, l) := l.assignRegion name body.run
  set l
  pure a

def assignTable (assignments : List (Halo2.Pinned.Column × Nat × String)) : SynthesizeM Unit :=
  modify (Layout.assignTable assignments)

end SynthesizeM

/-- Halo2-like circuit interface: `configure` produces a config and pinned-CS
builder state; `synthesize` lays out a configured circuit. -/
class PlonkCircuit (C : Type) where
  Config : Type
  configure : C → ConfigureM Config
  synthesize : C → Config → SynthesizeM Unit

def PlonkCircuit.configured {C : Type} [PlonkCircuit C] (c : C) : ConfiguredCircuit (PlonkCircuit.Config C) :=
  let (config, builder) := (PlonkCircuit.configure c).run {}
  let synthesize := fun config =>
    let (_, layout) := (PlonkCircuit.synthesize c config).run {}
    layout
  { config, cs := builder.cs, selectorKinds := builder.selectorKinds, synthesize }

end Halo2.Synthesis

namespace Halo2.Synthesis

structure SelectorCompressionInput where
  kinds : List Halo2.Pinned.SelectorKind
  activations : List (List Bool)
  numRows : Nat
deriving Repr, DecidableEq, BEq

/-- Compute the selector-compression input generated by synthesis for a configured circuit. -/
def ConfiguredCircuit.selectorCompressionInput {Config : Type} (c : ConfiguredCircuit Config) : SelectorCompressionInput :=
  let layout := c.synthesize c.config
  let rows := max 1 (activationRows layout.selectorActivations)
  { kinds := c.selectorKinds
    activations := selectorActivationTable c.cs.numSelectors rows layout.selectorActivations
    numRows := rows }

/-- For now this exposes the key invariant selector compression needs: one
activation vector per configured selector. -/
def SelectorCompressionInput.WellFormed (input : SelectorCompressionInput) : Prop :=
  input.kinds.length = input.activations.length

end Halo2.Synthesis

namespace Halo2.Synthesis

/-- A simple, layout-driven selector compression strategy: allocate one fixed
selector column per selector that appears in synthesis. This is not Halo2's
optimized compression, but it is useful for validating the synthesize/configure
interface before replacing it by the exact greedy compressor. -/
def ConfiguredCircuit.compressSelectorsOnePerColumn {Config : Type}
    (c : ConfiguredCircuit Config) (firstColumn firstQuery : Nat) : Halo2.Pinned.ConstraintSystem :=
  let input := c.selectorCompressionInput
  let replacement : Nat → Halo2.Pinned.Expression := fun selector =>
    if selector < input.activations.length then
      .fixed (firstQuery + selector) (firstColumn + selector) (.rot 0)
    else
      .selector selector
  let cs := c.cs.replaceSelectors replacement
  let selectorQueries := (List.range c.cs.numSelectors).map fun i =>
    (Halo2.Pinned.Column.fixed (firstColumn + i), Halo2.Pinned.Rotation.rot 0)
  { cs with
    numFixedColumns := max cs.numFixedColumns (firstColumn + c.cs.numSelectors)
    fixedQueries := cs.fixedQueries ++ selectorQueries }

end Halo2.Synthesis
