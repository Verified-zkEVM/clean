import Clean.Air.FlatEnsemble
import Clean.Circuit.WitnessGeneration

/-!
# Channel-driven ensemble witness generation

This file contains the executable reference builder for flat AIR ensemble witnesses.
It is intentionally not completeness-proved: malformed generation metadata or a public
input for which generation does not terminate produces an explicit error. Soundness does
not depend on this builder; generated rows still have to satisfy the component constraints
and global channel-balance relation.

The reference evaluator recomputes channel imbalance after every row mutation. This is
not the eventual optimized implementation, but it gives row updates the correct delta
semantics by construction: unchanged interactions are never counted twice.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Operational direction of a typed channel interaction. -/
inductive Direction where
  | pull
  | push
deriving Repr, DecidableEq, BEq

/-- How dynamically generated rows are allocated for repeated demand. -/
inductive Aggregation where
  | perOccurrence
  | byMessage
deriving Repr, DecidableEq, BEq

/-- A structured component-input cell derived from a triggering interaction. -/
inductive InputCell (F : Type) where
  | message (index : ℕ)
  | multiplicity
  | const (value : F)

namespace InputCell

def eval (message : Array F) (multiplicity : ℕ) : InputCell F → Except String F
  | .message index =>
      match message[index]? with
      | some value => .ok value
      | none => .error s!"channel message has no element at index {index}"
  | .multiplicity => .ok (FiniteField.fromNat multiplicity)
  | .const value => .ok value

end InputCell

/-- Build one component input row from a channel message and an integer multiplicity. -/
structure InputTemplate (F : Type) where
  cells : List (InputCell F)

namespace InputTemplate

def eval (template : InputTemplate F) (message : Array F) (multiplicity : ℕ) :
    Except String (Array F) := do
  return (← template.cells.mapM (InputCell.eval message multiplicity)).toArray

end InputTemplate

/-- Demand-driven row generation. -/
structure DemandMode (F : Type) where
  channel : String
  direction : Direction
  aggregation : Aggregation
  input : InputTemplate F

/-- One mutable multiplicity cell in a fixed collection of primary input rows. -/
structure FixedSlot (F : Type) where
  channel : String
  direction : Direction
  message : Array F
  row : ℕ
  column : ℕ

/-- The initial generation modes needed by flat AIR ensembles. -/
inductive Mode (F : Type) where
  | demand (mode : DemandMode F)
  | fixed (inputRows : List (Array F)) (slots : List (FixedSlot F))

/-- Generation metadata is aligned with `Ensemble.tables`. -/
structure Config (F : Type) where
  modes : List (Mode F)
  fuel : ℕ := 100000

/-- A normalized, nonzero channel imbalance. -/
structure Demand (F : Type) where
  channel : String
  direction : Direction
  message : Array F
  count : ℕ

namespace Demand

def sameMessage (left right : Demand F) : Bool :=
  left.channel == right.channel && left.message == right.message

def ofInteraction (interaction : Interaction F) : Option (Demand F) :=
  let direction := if interaction.assumeGuarantees then Direction.pull else Direction.push
  let count := if interaction.assumeGuarantees then
    FiniteField.val (-interaction.mult)
  else
    FiniteField.val interaction.mult
  if count = 0 then none else some {
    channel := interaction.channel.name
    direction
    message := interaction.msg
    count
  }

/-- Add one demand to a normalized list, eagerly cancelling opposite directions. -/
def add : List (Demand F) → Demand F → List (Demand F)
  | demands, demand =>
    if demand.count = 0 then demands else
    match demands with
    | [] => [demand]
    | current :: rest =>
      if sameMessage current demand then
        if current.direction = demand.direction then
          { current with count := current.count + demand.count } :: rest
        else if current.count = demand.count then
          rest
        else if current.count < demand.count then
          { demand with count := demand.count - current.count } :: rest
        else
          { current with count := current.count - demand.count } :: rest
      else
        current :: add rest demand

def normalize (interactions : List (Interaction F)) : List (Demand F) :=
  interactions.foldl (fun demands interaction =>
    match ofInteraction interaction with
    | none => demands
    | some demand => add demands demand) []

end Demand

/-- How a dynamic row was triggered, retained for message-coalesced updates. -/
structure Origin (F : Type) where
  channel : String
  direction : Direction
  message : Array F
  multiplicity : ℕ

structure GeneratedRow (F : Type) where
  input : Array F
  values : Array F
  origin : Option (Origin F) := none

structure GeneratedTable (F : Type) where
  rows : List (GeneratedRow F) := []

private def emptyData (F : Type) : ProverData F := fun _ _ => #[]

private def completeRow (component : Component F) (input : Array F)
    (origin : Option (Origin F) := none) : Except String (GeneratedRow F) := do
  unless input.size = component.rowOffset do
    throw s!"component input has width {input.size}, expected {component.rowOffset}"
  let circuit := component.circuit.main component.rowInputVar
  let values := circuit.witgen (ProverHint.empty F) input
  unless values.size = component.width do
    throw s!"generated row has width {values.size}, expected {component.width}"
  return { input, values, origin }

private def initializeTables :
    List (Component F) → List (Mode F) → Except String (List (GeneratedTable F))
  | [], [] => .ok []
  | component :: components, mode :: modes => do
      let rows ← match mode with
        | .demand _ => pure []
        | .fixed inputRows _ => inputRows.mapM fun input => completeRow component input
      let rest ← initializeTables components modes
      return { rows } :: rest
  | _, _ => .error "generation-mode count does not match ensemble component count"

private def rowInteractions (component : Component F) (row : GeneratedRow F) :
    List (Interaction F) :=
  component.operations.interactionValues (.fromArray row.values (emptyData F))

private def tableInteractions :
    List (Component F) → List (GeneratedTable F) → Except String (List (Interaction F))
  | [], [] => .ok []
  | component :: components, table :: tables => do
      let rest ← tableInteractions components tables
      return table.rows.flatMap (rowInteractions component) ++ rest
  | _, _ => .error "generated-table count does not match ensemble component count"

private def allInteractions (ensemble : Ensemble F PublicIO) (publicInput : PublicIO F)
    (tables : List (GeneratedTable F)) : Except String (List (Interaction F)) := do
  let verifier := ensemble.verifierOperations.interactionValues
    (.fromInput publicInput (emptyData F))
  return verifier ++ (← tableInteractions ensemble.tables tables)

private def Mode.handles (mode : Mode F) (demand : Demand F) : Bool :=
  match mode with
  | .demand mode => mode.channel == demand.channel && mode.direction == demand.direction
  | .fixed _ slots => slots.any fun slot =>
      slot.channel == demand.channel && slot.direction == demand.direction &&
        slot.message == demand.message

private def handlerIndices (modes : List (Mode F)) (demand : Demand F) : List ℕ :=
  modes.zipIdx.filterMap fun (mode, index) =>
    if mode.handles demand then some index else none

private def findAction (modes : List (Mode F)) :
    List (Demand F) → Except String (Option (Demand F × ℕ))
  | [] => .ok none
  | demand :: demands =>
      match handlerIndices modes demand with
      | [] => findAction modes demands
      | [index] => .ok (some (demand, index))
      | _ => .error s!"multiple generation handlers match channel '{demand.channel}'"

private def sameOrigin (origin : Origin F) (mode : DemandMode F) (demand : Demand F) : Bool :=
  origin.channel == mode.channel && origin.direction == mode.direction &&
    origin.message == demand.message

private def findOriginIndex (rows : List (GeneratedRow F)) (mode : DemandMode F)
    (demand : Demand F) : Option ℕ :=
  rows.zipIdx.findSome? fun (row, index) =>
    match row.origin with
    | some origin => if sameOrigin origin mode demand then some index else none
    | none => none

private def createDemandRow (component : Component F) (mode : DemandMode F)
    (demand : Demand F) (multiplicity : ℕ) : Except String (GeneratedRow F) := do
  let origin : Origin F := {
    channel := mode.channel
    direction := mode.direction
    message := demand.message
    multiplicity
  }
  completeRow component (← mode.input.eval demand.message multiplicity) (some origin)

private def handleDemand (component : Component F) (mode : DemandMode F)
    (demand : Demand F) (table : GeneratedTable F) : Except String (GeneratedTable F) := do
  match mode.aggregation with
  | .perOccurrence =>
      let rows ← (List.replicate demand.count ()).mapM fun _ =>
        createDemandRow component mode demand 1
      return { table with rows := table.rows ++ rows }
  | .byMessage =>
      match findOriginIndex table.rows mode demand with
      | none =>
          return { table with rows := table.rows ++ [← createDemandRow component mode demand demand.count] }
      | some index =>
          let some row := table.rows[index]?
            | throw "coalesced row index is out of bounds"
          let some origin := row.origin
            | throw "coalesced row has no origin"
          let updated ← createDemandRow component mode demand (origin.multiplicity + demand.count)
          return { table with rows := table.rows.set index updated }

private def findFixedSlot (slots : List (FixedSlot F)) (demand : Demand F) :
    Except String (FixedSlot F) :=
  match slots.filter fun slot =>
    slot.channel == demand.channel && slot.direction == demand.direction &&
      slot.message == demand.message with
  | [slot] => .ok slot
  | [] => .error s!"fixed handler has no slot for channel '{demand.channel}' message"
  | _ => .error s!"fixed handler has duplicate slots for channel '{demand.channel}' message"

private def handleFixed (component : Component F) (slots : List (FixedSlot F))
    (demand : Demand F) (table : GeneratedTable F) : Except String (GeneratedTable F) := do
  let slot ← findFixedSlot slots demand
  let some row := table.rows[slot.row]?
    | throw s!"fixed slot row {slot.row} is out of bounds"
  let some current := row.input[slot.column]?
    | throw s!"fixed slot column {slot.column} is out of bounds"
  let count := FiniteField.val current + demand.count
  let value := FiniteField.fromNat (F := F) count
  unless FiniteField.val value = count do
    throw s!"fixed multiplicity {count} overflows the field characteristic"
  let input := (row.input.toList.set slot.column value).toArray
  let updated ← completeRow component input
  return { table with rows := table.rows.set slot.row updated }

private def handle (ensemble : Ensemble F PublicIO) (config : Config F)
    (tables : List (GeneratedTable F)) (demand : Demand F) (index : ℕ) :
    Except String (List (GeneratedTable F)) := do
  let some component := ensemble.tables[index]?
    | throw s!"component index {index} is out of bounds"
  let some mode := config.modes[index]?
    | throw s!"generation mode index {index} is out of bounds"
  let some table := tables[index]?
    | throw s!"generated table index {index} is out of bounds"
  let updated ← match mode with
    | .demand mode => handleDemand component mode demand table
    | .fixed _ slots => handleFixed component slots demand table
  return tables.set index updated

private def generateLoop (ensemble : Ensemble F PublicIO) (config : Config F)
    (publicInput : PublicIO F) : ℕ → List (GeneratedTable F) →
    Except String (List (GeneratedTable F))
  | 0, _ => .error "ensemble witness generation exhausted its fuel"
  | fuel + 1, tables => do
      let demands := Demand.normalize (← allInteractions ensemble publicInput tables)
      if demands.isEmpty then return tables
      match ← findAction config.modes demands with
      | none =>
          let channels := String.intercalate ", " (demands.map (·.channel))
          throw s!"unhandled channel imbalance on: {channels}"
      | some (demand, index) =>
          generateLoop ensemble config publicInput fuel
            (← handle ensemble config tables demand index)

private structure AssembledTables (components : List (Component F)) where
  tables : List (Table F)
  same_length : components.length = tables.length
  same_circuits : ∀ index (hindex : index < components.length),
    components[index] = tables[index].component
  data_eq : ∀ table ∈ tables, table.data = emptyData F

private def assembleTables :
    (components : List (Component F)) → List (GeneratedTable F) →
      Except String (AssembledTables components)
  | [], [] => .ok {
      tables := []
      same_length := rfl
      same_circuits := by simp
      data_eq := by simp
    }
  | component :: components, generated :: generatedTables => do
      let rows := generated.rows.map (·.values)
      if h : ∀ row ∈ rows, row.size = component.width then
        let table : Table F := {
          component
          width := component.width
          table := rows
          data := emptyData F
          uniform_width := h
        }
        let rest ← assembleTables components generatedTables
        return {
          tables := table :: rest.tables
          same_length := by simp [rest.same_length]
          same_circuits := by
            intro index hindex
            cases index with
            | zero => rfl
            | succ index =>
                simp only [List.getElem_cons_succ]
                exact rest.same_circuits index (by simp at hindex; omega)
          data_eq := by
            intro candidate hcandidate
            simp only [List.mem_cons] at hcandidate
            rcases hcandidate with rfl | hrest
            · rfl
            · exact rest.data_eq candidate hrest
        }
      else
        throw "generated table contains a row of the wrong width"
  | _, _ => .error "generated-table count does not match ensemble component count"

/-- Execute channel-driven generation and construct a structurally valid ensemble witness. -/
def generate (ensemble : Ensemble F PublicIO) (config : Config F) (publicInput : PublicIO F) :
    Except String (EnsembleWitness ensemble) :=
  match initializeTables ensemble.tables config.modes with
  | .error error => .error error
  | .ok initial =>
    match generateLoop ensemble config publicInput config.fuel initial with
    | .error error => .error error
    | .ok generated =>
      match assembleTables ensemble.tables generated with
      | .error error => .error error
      | .ok assembled => .ok {
          tables := assembled.tables
          data := emptyData F
          publicInput
          same_length := assembled.same_length
          same_circuits := assembled.same_circuits
          same_data := assembled.data_eq
        }

/-- Executable constraint check for the no-legacy-lookup initial milestone. -/
def constraintsHold {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  witness.allTables.all fun table =>
    table.table.all fun row =>
      table.component.operations.lookups.isEmpty &&
      table.component.operations.constraints.all fun constraint =>
        constraint.eval (table.environment row) == 0

/-- Executable balance check using the same normalized worklist representation. -/
def channelsBalanced {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  Demand.normalize witness.interactions |>.isEmpty

end Air.Flat.WitnessGeneration
