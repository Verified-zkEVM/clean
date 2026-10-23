module

public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Counters

A counter is an input variable of a component that is the multiplicity of one of its interactions,
see `Clean.Air.WitnessGeneration.Generation`. The generation names the variable; this file finds
the interaction it counts.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

/-- A counter, resolved from the input variable that holds it. -/
structure Counter where
  /-- The input column holding the counter. -/
  column : ℕ
  /-- The position of the counted interaction among the component's row interactions. -/
  interaction : ℕ
  /-- The channel of the counted interaction, on which the counter answers demand. -/
  channel : String

/-- Why a named counter is invalid. -/
inductive CounterError where
  /-- The counter isn't a single input variable after the fixed columns. -/
  | notVariable
  /-- Not exactly one interaction has the counter as its multiplicity. -/
  | interactions (column count : ℕ)
  /-- The message of the counted interaction reads a cell other than a non-counter input cell, so
  counting could change which message the row answers. -/
  | message (column : ℕ)
deriving Repr, DecidableEq

instance : ToString CounterError where
  toString
    | .notVariable => "names a counter that is not a single input variable after the fixed columns"
    | .interactions column count =>
        s!"has {count} interactions whose multiplicity is the counter in column {column}, \
          expected one"
    | .message column =>
        s!"counts with column {column} on an interaction whose message reads a cell other than \
          a non-counter input cell"

/-- The cells an expression reads. -/
def expressionCells : Expression F → List ℕ
  | .var cell => [cell.index]
  | .const _ => []
  | .add left right | .mul left right => expressionCells left ++ expressionCells right

/-- Resolve a counter of `component`, named by its input variable, to the unique interaction whose
multiplicity is exactly that variable. -/
def Counter.resolve (component : Component F) (counter : Var component.Input F → Expression F) :
    Except CounterError Counter :=
  match counter (varFromOffset component.Input 0) with
  | .var cell =>
      if component.fixedWidth ≤ cell.index && cell.index < component.ownInputWidth then
        let counted := component.rowOperations.interactions.zipIdx.filter fun (interaction, _) =>
          match interaction.mult with
          | .var multiplicity => multiplicity.index == cell.index
          | _ => false
        match counted with
        | [(interaction, index)] =>
            .ok { column := cell.index, interaction := index, channel := interaction.channel.name }
        | found => .error (.interactions cell.index found.length)
      else .error .notVariable
  | _ => .error .notVariable

/-- Check that counting never changes which message a row answers: the messages of counted
interactions only read input cells that aren't counters. -/
def checkCounterMessages (component : Component F) (counters : List Counter) :
    Except CounterError Unit := do
  let interactions := component.rowOperations.interactions
  for counter in counters do
    let some interaction := interactions[counter.interaction]? | continue
    let cells := interaction.msg.toList.flatMap expressionCells
    unless cells.all fun cell => cell < component.ownInputWidth && counters.all (·.column ≠ cell) do
      throw (.message counter.column)

/-- The counters of a component: the one of a `byMessage` demand component, or those of a
preallocated component. -/
def resolveCounters (component : Component F) : Except CounterError (List Counter) := do
  let counters ← match component.generation with
    | .demand mode => match mode.aggregation with
      | .perOccurrence => pure []
      | .byMessage counter => ([·]) <$> Counter.resolve component counter
    | .preallocated mode => mode.counters.mapM (Counter.resolve component)
  checkCounterMessages component counters
  return counters

end Air.Flat.WitnessGeneration
