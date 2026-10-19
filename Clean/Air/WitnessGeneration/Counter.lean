module

public import Clean.Air.WitnessGeneration.Config

@[expose] public section

/-!
# Counters

A counter is the multiplicity of a component's interaction on a channel where it answers demand by
message, see `Clean.Air.WitnessGeneration.Config`. This file finds the counters in the circuit.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

/-- A counter, resolved from the channel it counts on. -/
structure Counter where
  /-- The position of the counted interaction among the component's row interactions. -/
  interaction : ℕ
  /-- The input column holding the interaction's multiplicity. -/
  column : ℕ

/-- Why a component has no valid counter on a channel. -/
inductive CounterError where
  /-- The component doesn't have exactly one interaction on the channel. -/
  | interactions (channel : String) (count : ℕ)
  /-- The multiplicity of the interaction isn't a single non-fixed input variable. -/
  | multiplicity (channel : String)
  /-- The message of the interaction reads a cell other than a non-counter input cell, so counting
  could change which message the row answers. -/
  | message (channel : String)
deriving Repr, DecidableEq

instance : ToString CounterError where
  toString
    | .interactions channel count =>
        s!"has {count} interactions on channel '{channel}', expected one to count"
    | .multiplicity channel =>
        s!"counts on channel '{channel}' with a multiplicity that is not a non-fixed input \
          variable"
    | .message channel =>
        s!"counts on channel '{channel}' with a message that reads a cell other than a \
          non-counter input cell"

/-- The cells an expression reads. -/
def expressionCells : Expression F → List ℕ
  | .var cell => [cell.index]
  | .const _ => []
  | .add left right | .mul left right => expressionCells left ++ expressionCells right

/-- The counter of a component on `channel`: its unique interaction on that channel, whose
multiplicity must be an input variable after the fixed columns. -/
def Counter.resolve (component : Component F) (channel : RawChannel F) :
    Except CounterError Counter :=
  match component.rowOperations.interactions.zipIdx.filter (·.1.channel.name == channel.name) with
  | [(interaction, index)] =>
      match interaction.mult with
      | .var cell =>
          if component.fixedWidth ≤ cell.index && cell.index < component.rowOffset then
            .ok { interaction := index, column := cell.index }
          else .error (.multiplicity channel.name)
      | _ => .error (.multiplicity channel.name)
  | found => .error (.interactions channel.name found.length)

/-- Check that counting never changes which message a row answers: the messages of counted
interactions only read input cells that aren't counters. -/
def checkCounterMessages (component : Component F) (counters : List Counter) :
    Except CounterError Unit := do
  let interactions := component.rowOperations.interactions
  for counter in counters do
    let some interaction := interactions[counter.interaction]? | continue
    let cells := interaction.msg.toList.flatMap expressionCells
    unless cells.all fun cell => cell < component.rowOffset && counters.all (·.column ≠ cell) do
      throw (.message interaction.channel.name)

/-- The counters of a component's generation: one per channel of a preallocated component, and one
on the channel of a `byMessage` demand component. -/
def Generation.counters (component : Component F) (generation : Generation F) :
    Except CounterError (List Counter) := do
  let counters ← match generation with
    | .demand mode => match mode.aggregation with
      | .perOccurrence => pure []
      | .byMessage => ([·]) <$> Counter.resolve component mode.channel
    | .preallocated mode => mode.channels.mapM (Counter.resolve component)
  checkCounterMessages component counters
  return counters

end Air.Flat.WitnessGeneration
