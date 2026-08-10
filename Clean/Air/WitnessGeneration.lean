import Clean.Air.FlatEnsemble
import Clean.Circuit.WitnessGeneration

/-!
# Channel-driven ensemble witness generation

This file contains the executable reference builder for flat AIR ensemble witnesses.
It is intentionally not completeness-proved: malformed generation metadata or a public
input for which generation does not terminate produces an explicit error. Soundness does
not depend on this builder; generated rows still have to satisfy the component constraints
and global channel-balance relation.

The evaluator maintains channel imbalance incrementally. New rows add their interactions;
updated rows first remove their previous contribution and then add their new contribution.
Unchanged nested interactions are therefore never counted twice.
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

/-- A semantic row used to extend one component to a power-of-two trace height. -/
structure Padding (F : Type) where
  input : Array F
  minimumRows : ℕ := 1

/-- Generation and padding metadata are aligned with `Ensemble.tables`. -/
structure Config (F : Type) where
  modes : List (Mode F)
  padding : List (Padding F)
  fuel : ℕ

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

def opposite (demand : Demand F) : Demand F :=
  { demand with direction := match demand.direction with
      | .pull => .push
      | .push => .pull }

def addInteractions (demands : List (Demand F)) (interactions : List (Interaction F)) :
    List (Demand F) :=
  interactions.foldl (fun demands interaction =>
    match ofInteraction interaction with
    | none => demands
    | some demand => add demands demand) demands

def removeInteractions (demands : List (Demand F)) (interactions : List (Interaction F)) :
    List (Demand F) :=
  interactions.foldl (fun demands interaction =>
    match ofInteraction interaction with
    | none => demands
    | some demand => add demands demand.opposite) demands

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

private structure PreparedComponent (F : Type) [FiniteField F] where
  component : Component F
  inputWidth : ℕ
  width : ℕ
  witgenOps : List (FlatOperation F)
  interactions : List (AbstractInteraction F)

private def witnessOperationsOnly : List (FlatOperation F) → List (FlatOperation F)
  | [] => []
  | operation :: operations =>
      match operation with
      | .witness _ _ => operation :: witnessOperationsOnly operations
      | .assert _ | .lookup _ | .interact _ => witnessOperationsOnly operations

private def prepareComponent (component : Component F) : PreparedComponent F :=
  let operations := component.rowOperations
  {
    component
    inputWidth := component.rowOffset
    width := component.width
    witgenOps := witnessOperationsOnly operations.toFlat
    interactions := operations.interactions
  }

private def witgenStepWithData (data : ProverData F) (hint : ProverHint F)
    (acc : Array F) : FlatOperation F → Array F
  | .witness _ code =>
      let environment : ProverEnvironment F := {
        get index := acc[index]?.getD 0
        data
        hint
      }
      acc ++ (code.eval environment).toArray
  | .assert _ | .lookup _ | .interact _ => acc

private def witgenWithData (data : ProverData F) (hint : ProverHint F)
    (ops : List (FlatOperation F)) (input : Array F) : Array F :=
  ops.foldl (witgenStepWithData data hint) input

/-- The runtime view of the same complete circuit inputs used by `deriveProverData`. -/
private def generatedData :
    List (PreparedComponent F) → List (GeneratedTable F) → ProverData F
  | prepared, tables => fun name n =>
      match prepared.zip tables |>.find? (fun (component, _) => component.component.circuit.name == name) with
      | some (component, table) =>
          if h : size component.component.Input = n then
            h ▸ (table.rows.map (inputRow component.component.Input ∘ (·.input)) |>.toArray)
          else #[]
      | none => #[]

private def completeRow (prepared : PreparedComponent F) (input : Array F)
    (data : ProverData F) (origin : Option (Origin F) := none) : Except String (GeneratedRow F) := do
  unless input.size = prepared.inputWidth do
    throw s!"component input has width {input.size}, expected {prepared.inputWidth}"
  let values := witgenWithData data (ProverHint.empty F) prepared.witgenOps input
  unless values.size = prepared.width do
    throw s!"generated row has width {values.size}, expected {prepared.width}"
  return { input, values, origin }

private def initializeTableInputs :
    List (PreparedComponent F) → List (Mode F) → Except String (List (GeneratedTable F))
  | [], [] => .ok []
  | _ :: components, mode :: modes => do
      let rows ← match mode with
        | .demand _ => pure []
        | .fixed inputRows _ => pure <| inputRows.map fun input => { input, values := input }
      let rest ← initializeTableInputs components modes
      return { rows } :: rest
  | _, _ => .error "generation-mode count does not match ensemble component count"

private def completeInitialTables (data : ProverData F) :
    List (PreparedComponent F) → List (GeneratedTable F) →
      Except String (List (GeneratedTable F))
  | [], [] => pure []
  | prepared :: components, table :: tables => do
      let rows ← table.rows.mapM fun row => completeRow prepared row.input data row.origin
      let rest ← completeInitialTables data components tables
      return { rows } :: rest
  | _, _ => .error "generated-table count does not match ensemble component count"

private def rowInteractions (prepared : PreparedComponent F) (row : GeneratedRow F)
    (data : ProverData F) :
    List (Interaction F) :=
  let environment := Environment.fromArray row.values data
  prepared.interactions.map (·.eval environment)

private def tableInteractions (data : ProverData F) :
    List (PreparedComponent F) → List (GeneratedTable F) → Except String (List (Interaction F))
  | [], [] => .ok []
  | prepared :: components, table :: tables => do
      let rest ← tableInteractions data components tables
      return table.rows.flatMap (rowInteractions prepared · data) ++ rest
  | _, _ => .error "generated-table count does not match ensemble component count"

private def allInteractions (ensemble : Ensemble F PublicIO) (publicInput : PublicIO F)
    (prepared : List (PreparedComponent F)) (tables : List (GeneratedTable F))
    (data : ProverData F) :
    Except String (List (Interaction F)) := do
  let verifier := ensemble.verifierOperations.interactionValues
    (.fromInput publicInput data)
  return verifier ++ (← tableInteractions data prepared tables)

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

private def createDemandRow (prepared : PreparedComponent F) (mode : DemandMode F)
    (demand : Demand F) (multiplicity : ℕ) (data : ProverData F) :
    Except String (GeneratedRow F) := do
  let origin : Origin F := {
    channel := mode.channel
    direction := mode.direction
    message := demand.message
    multiplicity
  }
  completeRow prepared (← mode.input.eval demand.message multiplicity) data (some origin)

private structure TableMutation (F : Type) where
  table : GeneratedTable F
  removedRows : List (GeneratedRow F) := []
  addedRows : List (GeneratedRow F) := []
  directDemands : List (Demand F) := []

private def handleDemand (prepared : PreparedComponent F) (mode : DemandMode F)
    (demand : Demand F) (table : GeneratedTable F) (data : ProverData F) :
    Except String (TableMutation F) := do
  match mode.aggregation with
  | .perOccurrence =>
      let rows ← (List.replicate demand.count ()).mapM fun _ =>
        createDemandRow prepared mode demand 1 data
      return { table := { table with rows := table.rows ++ rows }, addedRows := rows }
  | .byMessage =>
      match findOriginIndex table.rows mode demand with
      | none =>
          let row ← createDemandRow prepared mode demand demand.count data
          return { table := { table with rows := table.rows ++ [row] }, addedRows := [row] }
      | some index =>
          let some row := table.rows[index]?
            | throw "coalesced row index is out of bounds"
          let some origin := row.origin
            | throw "coalesced row has no origin"
          let updated ← createDemandRow prepared mode demand (origin.multiplicity + demand.count) data
          return {
            table := { table with rows := table.rows.set index updated }
            removedRows := [row]
            addedRows := [updated]
          }

private def findFixedSlot (slots : List (FixedSlot F)) (demand : Demand F) :
    Except String (FixedSlot F) :=
  match slots.filter fun slot =>
    slot.channel == demand.channel && slot.direction == demand.direction &&
      slot.message == demand.message with
  | [slot] => .ok slot
  | [] => .error s!"fixed handler has no slot for channel '{demand.channel}' message"
  | _ => .error s!"fixed handler has duplicate slots for channel '{demand.channel}' message"

private def handleFixed (prepared : PreparedComponent F) (slots : List (FixedSlot F))
    (demand : Demand F) (table : GeneratedTable F) (data : ProverData F) :
    Except String (TableMutation F) := do
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
  let updated ← completeRow prepared input data
  return {
    table := { table with rows := table.rows.set slot.row updated }
    directDemands := [{
      channel := slot.channel
      direction := match slot.direction with
        | .pull => .push
        | .push => .pull
      message := slot.message
      count := demand.count
    }]
  }

private structure Mutation (F : Type) where
  tables : List (GeneratedTable F)
  removed : List (Interaction F)
  added : List (Interaction F)
  directDemands : List (Demand F) := []

private def handle (prepared : List (PreparedComponent F)) (config : Config F)
    (tables : List (GeneratedTable F)) (demand : Demand F) (index : ℕ)
    (data : ProverData F) :
    Except String (Mutation F) := do
  let some component := prepared[index]?
    | throw s!"component index {index} is out of bounds"
  let some mode := config.modes[index]?
    | throw s!"generation mode index {index} is out of bounds"
  let some table := tables[index]?
    | throw s!"generated table index {index} is out of bounds"
  let tableMutation ← match mode with
    | .demand mode => handleDemand component mode demand table data
    | .fixed _ slots => handleFixed component slots demand table data
  return {
    tables := tables.set index tableMutation.table
    removed := tableMutation.removedRows.flatMap (rowInteractions component · data)
    added := tableMutation.addedRows.flatMap (rowInteractions component · data)
    directDemands := tableMutation.directDemands
  }

private def generateLoop (ensemble : Ensemble F PublicIO) (config : Config F)
    (prepared : List (PreparedComponent F)) (publicInput : PublicIO F) (data : ProverData F) :
    ℕ → List (GeneratedTable F) → List (Demand F) →
    Except String (List (GeneratedTable F))
  | 0, _, _ => .error "ensemble witness generation exhausted its fuel"
  | fuel + 1, tables, demands => do
      if demands.isEmpty then return tables
      match ← findAction config.modes demands with
      | none =>
          let channels := String.intercalate ", " (demands.map (·.channel))
          throw s!"unhandled channel imbalance on: {channels}"
      | some (demand, index) =>
          let mutation ← handle prepared config tables demand index data
          let demands := Demand.addInteractions
            (Demand.removeInteractions demands mutation.removed) mutation.added
          let demands := mutation.directDemands.foldl Demand.add demands
          generateLoop ensemble config prepared publicInput data fuel mutation.tables demands

private def nextPowerOfTwoAux (target : ℕ) : ℕ → ℕ → ℕ
  | 0, power => power
  | fuel + 1, power =>
      if target ≤ power then power else nextPowerOfTwoAux target fuel (power * 2)

private def nextPowerOfTwo (value : ℕ) : ℕ :=
  nextPowerOfTwoAux (max value 1) value 1

def Padding.targetHeight (padding : Padding F) (rowCount : ℕ) : ℕ :=
  nextPowerOfTwo (max rowCount padding.minimumRows)

private structure PaddingMutation (F : Type) where
  tables : List (GeneratedTable F)
  added : List (Interaction F)

private def padTables (data : ProverData F) :
    List (PreparedComponent F) → List (Padding F) → List (GeneratedTable F) →
      Except String (PaddingMutation F)
  | [], [], [] => .ok { tables := [], added := [] }
  | prepared :: components, padding :: paddings, table :: tables => do
      let count := padding.targetHeight table.rows.length - table.rows.length
      let rows ← (List.replicate count ()).mapM fun _ =>
        completeRow prepared padding.input data
      let rest ← padTables data components paddings tables
      return {
        tables := { table with rows := table.rows ++ rows } :: rest.tables
        added := rows.flatMap (rowInteractions prepared · data) ++ rest.added
      }
  | _, _, _ => .error "padding count does not match ensemble component count"

private def tablesArePadded : List (GeneratedTable F) → List (Padding F) → Bool
  | [], [] => true
  | table :: tables, padding :: paddings =>
      table.rows.length == padding.targetHeight table.rows.length &&
        tablesArePadded tables paddings
  | _, _ => false

private def validateModes :
    List (PreparedComponent F) → List (Mode F) → List (Padding F) → Except String Unit
  | [], [], [] => pure ()
  | prepared :: components, mode :: modes, padding :: paddings => do
      match prepared.component.fixedColumns, mode with
      | some _, .demand _ =>
          throw s!"fixed-column component '{prepared.component.circuit.name}' must use fixed generation"
      | some fixed, .fixed inputRows slots =>
          unless FixedColumns.RowsMatch fixed inputRows do
            throw s!"fixed input rows for component '{prepared.component.circuit.name}' do not match its fixed columns"
          unless padding.targetHeight inputRows.length = inputRows.length do
            throw s!"fixed-column component '{prepared.component.circuit.name}' cannot change height during padding"
          unless slots.all fun slot => fixed.width ≤ slot.column do
            throw s!"fixed handler for component '{prepared.component.circuit.name}' mutates a fixed column"
      | none, _ => pure ()
      validateModes components modes paddings
  | _, _, _ => .error "generation metadata does not match ensemble component count"

private def padAndBalance (ensemble : Ensemble F PublicIO) (config : Config F)
    (prepared : List (PreparedComponent F)) (publicInput : PublicIO F) (data : ProverData F) :
    ℕ → List (GeneratedTable F) → Except String (List (GeneratedTable F))
  | 0, _ => .error "ensemble padding exhausted its fuel"
  | fuel + 1, tables => do
      let mutation ← padTables data prepared config.padding tables
      let tables ← generateLoop ensemble config prepared publicInput data config.fuel mutation.tables
        (Demand.normalize mutation.added)
      if tablesArePadded tables config.padding then return tables
      padAndBalance ensemble config prepared publicInput data fuel tables

private structure AssembledTables (components : List (Component F)) where
  tables : List (Table F)
  same_length : components.length = tables.length
  same_circuits : ∀ index (hindex : index < components.length),
    components[index] = tables[index].component

private structure MatchedFixedRows (component : Component F) (rows : List (Array F)) where
  marker : Unit := ()
  property : component.fixedRowsMatch rows

private def validateFixedRows (component : Component F) (rows : List (Array F)) :
    Except String (MatchedFixedRows component rows) :=
  match hcolumns : component.fixedColumns with
  | none => .ok ⟨(), by simp [Component.fixedRowsMatch, hcolumns]⟩
  | some fixed =>
      if hrows : FixedColumns.RowsMatch fixed rows then
        .ok ⟨(), by simpa [Component.fixedRowsMatch, hcolumns] using hrows⟩
      else
        .error "generated table does not match its fixed columns"

private def assembleTables :
    (components : List (Component F)) → List (GeneratedTable F) →
      Except String (AssembledTables components)
  | [], [] => .ok {
      tables := []
      same_length := rfl
      same_circuits := by simp
    }
  | component :: components, generated :: generatedTables => do
      let rows := generated.rows.map (·.values)
      if h : ∀ row ∈ rows, row.size = component.width then
        match validateFixedRows component rows with
        | .error error => .error error
        | .ok matched => do
          let table : Table F := {
            component
            table := rows
            uniform_width := h
            fixed_rows_match := matched.property
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
          }
      else
        throw "generated table contains a row of the wrong width"
  | _, _ => .error "generated-table count does not match ensemble component count"

/-- Execute channel-driven generation and construct a structurally valid ensemble witness. -/
def generate (ensemble : Ensemble F PublicIO) (config : Config F) (publicInput : PublicIO F) :
    Except String (EnsembleWitness ensemble) :=
  let prepared := ensemble.tables.map prepareComponent
  match validateModes prepared config.modes config.padding with
  | .error error => .error error
  | .ok () => match initializeTableInputs prepared config.modes with
  | .error error => .error error
  | .ok initialInputs =>
    let data := generatedData prepared initialInputs
    match completeInitialTables data prepared initialInputs with
    | .error error => .error error
    | .ok initial => match allInteractions ensemble publicInput prepared initial data with
    | .error error => .error error
    | .ok interactions =>
      match generateLoop ensemble config prepared publicInput data config.fuel initial
          (Demand.normalize interactions) with
      | .error error => .error error
      | .ok generated =>
        match padAndBalance ensemble config prepared publicInput data config.fuel generated with
        | .error error => .error error
        | .ok padded => match assembleTables ensemble.tables padded with
        | .error error => .error error
        | .ok assembled => .ok {
            tables := assembled.tables
            publicInput
            same_length := assembled.same_length
            same_circuits := assembled.same_circuits
          }

/-- Executable constraint check for the no-legacy-lookup initial milestone. -/
def constraintsHold {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  witness.tables.all fun table =>
    table.table.all fun row =>
      table.component.operations.lookups.isEmpty &&
      table.component.operations.constraints.all fun constraint =>
        constraint.eval (Environment.fromArray row witness.data) == 0

/-- Executable balance check using the same normalized worklist representation. -/
def channelsBalanced {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  Demand.normalize witness.interactions |>.isEmpty

end Air.Flat.WitnessGeneration
