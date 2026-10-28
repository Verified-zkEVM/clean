module

public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Multiplicity cells

A multiplicity cell of a component is an input cell that generation counts: the multiplicity of the
component's interaction on its channel, see `Clean.Air.WitnessGeneration.Generation`. The generation
marks the cell; this file finds the interaction it is the multiplicity of.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

/-- A multiplicity cell, resolved. -/
structure MultiplicityColumn where
  /-- The input column of the cell. -/
  column : ℕ
  /-- The position of the counted interaction among the component's row interactions. -/
  interaction : ℕ

/-- Why the multiplicity cell of a component is invalid. -/
inductive MultiplicityError where
  /-- A preallocated component has no multiplicity cell, a standalone component has one, or a
  component has several. -/
  | cells (count : ℕ)
  /-- Not exactly one interaction has the cell as its multiplicity. -/
  | interactions (column count : ℕ)
  /-- The counted interaction is on another channel than the one the component answers demand on. -/
  | channel (column : ℕ) (counted expected : String)
  /-- The message of the counted interaction reads a cell other than a non-multiplicity input cell,
  so counting could change which message the row answers. -/
  | message (column : ℕ)
deriving Repr, DecidableEq

instance : ToString MultiplicityError where
  toString
    | .cells count => s!"has {count} multiplicity cells"
    | .interactions column count =>
        s!"has {count} interactions whose multiplicity is the multiplicity cell in column \
          {column}, expected one"
    | .channel column counted expected =>
        s!"counts with column {column} on channel '{counted}', but answers demand on channel \
          '{expected}'"
    | .message column =>
        s!"counts with column {column} on an interaction whose message reads a cell other than \
          a non-multiplicity input cell"

/-- The cells an expression reads. -/
def expressionCells : Expression F → List ℕ
  | .var cell => [cell.index]
  | .const _ => []
  | .add left right | .mul left right => expressionCells left ++ expressionCells right

/-- Resolve the cell in `column` to the unique interaction whose multiplicity is exactly that cell,
and check that the interaction is on the generation's channel and that its message reads only
other input cells. -/
def MultiplicityColumn.resolve (component : Component F) (column : ℕ) :
    Except MultiplicityError MultiplicityColumn := do
  let interactions := component.rowOperations.interactions
  let counted := interactions.zipIdx.filter fun (interaction, _) =>
    match interaction.mult with
    | .var multiplicity => multiplicity.index == column
    | _ => false
  let [(interaction, index)] := counted | throw (.interactions column counted.length)
  let some channel := component.generation.channelName? | throw (.cells 1)
  unless interaction.channel.name == channel do
    throw (.channel column interaction.channel.name channel)
  let cells := interaction.msg.toList.flatMap expressionCells
  unless cells.all fun cell => cell < component.rowOffset && cell ≠ column do
    throw (.message column)
  return { column, interaction := index }

/-- The multiplicity cell of a component, resolved: exactly one in a preallocated component, at most
one in a demand component, and none in a standalone or segment-generated component. -/
def resolveMultiplicity (component : Component F) :
    Except MultiplicityError (Option MultiplicityColumn) := do
  let columns := (component.generation.cells.1.toList.zipIdx.filter (·.1.isMultiplicity)).map (·.2)
  match columns, component.generation with
  | [column], _ => some <$> MultiplicityColumn.resolve component column
  | [], .demand _ | [], .standalone _ | [], .segments _ => return none
  | columns, _ => throw (.cells columns.length)

end Air.Flat.WitnessGeneration
