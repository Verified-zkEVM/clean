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

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable {ProverInput : TypeMap} [ProvableType ProverInput]

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

/-- One cell of a preallocated component input. Prover-input cells read a strided
position from the serialized, runtime-supplied prover input. -/
inductive PreallocatedCell (F : Type) where
  | proverInput (offset stride : ℕ)
  | const (value : F)

namespace PreallocatedCell

def eval (proverInput : Array F) (row : ℕ) : PreallocatedCell F → Except String F
  | .proverInput offset stride =>
      match proverInput[offset + row * stride]? with
      | some value => .ok value
      | none => .error s!"prover input has no element at index {offset + row * stride}"
  | .const value => .ok value

end PreallocatedCell

/-- A channel handler for preallocated rows. The interaction is the component
interaction whose message selects a row; `column` is the generated multiplicity
input updated when the opposite demand arrives. -/
structure PreallocatedHandler where
  interaction : ℕ
  column : ℕ

/-- Rows allocated before channel balancing. Fixed columns, when present, are
prepended by the generic builder; `input` describes only the prover-owned suffix. -/
structure PreallocatedMode (F : Type) where
  rows : ℕ
  input : List (PreallocatedCell F)
  handlers : List PreallocatedHandler

/-- The row-allocation modes needed by flat AIR ensembles. Fixed columns are an
orthogonal component property and are not themselves a generation mode. -/
inductive Mode (F : Type) where
  | demand (mode : DemandMode F)
  | preallocated (mode : PreallocatedMode F)

/-- A semantic row used to extend one component to a power-of-two trace height. -/
structure Padding (F : Type) where
  input : Array F
  minimumRows : ℕ := 1

/-- Generation and padding metadata are aligned with `Ensemble.tables`. `ProverInput`
is witness-construction input only; semantic `ProverData` is still derived from the
final committed component rows. -/
structure Config (F : Type) (ProverInput : TypeMap) [ProvableType ProverInput] where
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

private def fixedPrefix (component : Component F) (row : ℕ) : Except String (Array F) :=
  match component.fixedColumns with
  | none => .ok #[]
  | some fixed =>
      match fixed.rows[row]? with
      | some values => .ok values
      | none => .error s!"fixed component '{component.circuit.name}' has no row {row}"

private def initializeInput (prepared : PreparedComponent F) (mode : PreallocatedMode F)
    (proverInput : Array F) (row : ℕ) : Except String (Array F) := do
  let fixed ← fixedPrefix prepared.component row
  let suffix ← mode.input.mapM (PreallocatedCell.eval proverInput row)
  let input := fixed ++ suffix.toArray
  unless input.size = prepared.inputWidth do
    throw s!"component '{prepared.component.circuit.name}' initialized an input of width \
      {input.size}, expected {prepared.inputWidth}"
  return input

private def initializeTableInputs (proverInput : Array F) :
    List (PreparedComponent F) → List (Mode F) → Except String (List (GeneratedTable F))
  | [], [] => .ok []
  | prepared :: components, mode :: modes => do
      let rows ← match mode with
        | .demand _ => pure []
        | .preallocated mode =>
            (List.range mode.rows).mapM fun row => do
              let input ← initializeInput prepared mode proverInput row
              return { input, values := input }
      let rest ← initializeTableInputs proverInput components modes
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

private def handlerDirection (interaction : AbstractInteraction F) : Direction :=
  if interaction.assumeGuarantees then .push else .pull

private def PreallocatedHandler.handles (prepared : PreparedComponent F)
    (handler : PreallocatedHandler) (demand : Demand F) : Bool :=
  match prepared.interactions[handler.interaction]? with
  | none => false
  | some interaction =>
      interaction.channel.name == demand.channel &&
        handlerDirection interaction == demand.direction

private def Mode.handles (prepared : PreparedComponent F) (mode : Mode F)
    (demand : Demand F) : Bool :=
  match mode with
  | .demand mode => mode.channel == demand.channel && mode.direction == demand.direction
  | .preallocated mode => mode.handlers.any fun handler => handler.handles prepared demand

private def handlerIndices (prepared : List (PreparedComponent F)) (modes : List (Mode F))
    (demand : Demand F) : List ℕ :=
  (prepared.zip modes).zipIdx.filterMap fun ((component, mode), index) =>
    if mode.handles component demand then some index else none

private def findAction (prepared : List (PreparedComponent F)) (modes : List (Mode F)) :
    List (Demand F) → Except String (Option (Demand F × ℕ))
  | [] => .ok none
  | demand :: demands =>
      match handlerIndices prepared modes demand with
      | [] => findAction prepared modes demands
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

private structure PreallocatedMatch (F : Type) where
  handler : PreallocatedHandler
  rowIndex : ℕ
  row : GeneratedRow F

private def findPreallocatedMatch (prepared : PreparedComponent F)
    (handlers : List PreallocatedHandler) (demand : Demand F) (table : GeneratedTable F)
    (data : ProverData F) : Except String (PreallocatedMatch F) :=
  let candidates := handlers.flatMap fun handler =>
    if handler.handles prepared demand then
      table.rows.zipIdx.filterMap fun (row, rowIndex) =>
        match prepared.interactions[handler.interaction]? with
        | none => none
        | some abstract =>
            let interaction := abstract.eval (Environment.fromArray row.values data)
            if interaction.msg == demand.message then some { handler, rowIndex, row } else none
    else []
  match candidates with
  | [found] => .ok found
  | [] => .error s!"preallocated handler has no row for channel '{demand.channel}' message"
  | _ => .error s!"preallocated handler has multiple rows for channel '{demand.channel}' message"

private def handlePreallocated (prepared : PreparedComponent F)
    (handlers : List PreallocatedHandler) (demand : Demand F) (table : GeneratedTable F)
    (data : ProverData F) : Except String (TableMutation F) := do
  let found ← findPreallocatedMatch prepared handlers demand table data
  let some current := found.row.input[found.handler.column]?
    | throw s!"preallocated handler column {found.handler.column} is out of bounds"
  let count := FiniteField.val current + demand.count
  let value := FiniteField.fromNat (F := F) count
  unless FiniteField.val value = count do
    throw s!"preallocated multiplicity {count} overflows the field characteristic"
  let input := (found.row.input.toList.set found.handler.column value).toArray
  let updated ← completeRow prepared input data
  return {
    table := { table with rows := table.rows.set found.rowIndex updated }
    removedRows := [found.row]
    addedRows := [updated]
  }

private structure Mutation (F : Type) where
  tables : List (GeneratedTable F)
  removed : List (Interaction F)
  added : List (Interaction F)

private def handle (prepared : List (PreparedComponent F)) (config : Config F ProverInput)
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
    | .preallocated mode => handlePreallocated component mode.handlers demand table data
  return {
    tables := tables.set index tableMutation.table
    removed := tableMutation.removedRows.flatMap (rowInteractions component · data)
    added := tableMutation.addedRows.flatMap (rowInteractions component · data)
  }

private def generateLoop (ensemble : Ensemble F PublicIO) (config : Config F ProverInput)
    (prepared : List (PreparedComponent F)) (publicInput : PublicIO F) (data : ProverData F) :
    ℕ → List (GeneratedTable F) → List (Demand F) →
    Except String (List (GeneratedTable F))
  | 0, _, _ => .error "ensemble witness generation exhausted its fuel"
  | fuel + 1, tables, demands => do
      if demands.isEmpty then return tables
      match ← findAction prepared config.modes demands with
      | none =>
          let channels := String.intercalate ", " (demands.map (·.channel))
          throw s!"unhandled channel imbalance on: {channels}"
      | some (demand, index) =>
          let mutation ← handle prepared config tables demand index data
          let demands := Demand.addInteractions
            (Demand.removeInteractions demands mutation.removed) mutation.added
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

private def validateModes (proverInputWidth : ℕ) :
    List (PreparedComponent F) → List (Mode F) → List (Padding F) → Except String Unit
  | [], [], [] => pure ()
  | prepared :: components, mode :: modes, padding :: paddings => do
      let fixedWidth := prepared.component.fixedWidth
      match prepared.component.fixedColumns, mode with
      | some _, .demand _ =>
          throw s!"fixed-column component '{prepared.component.circuit.name}' must use preallocated generation"
      | some fixed, .preallocated preallocated =>
          unless preallocated.rows = fixed.rows.length do
            throw s!"preallocated row count for component '{prepared.component.circuit.name}' \
              does not match its fixed-column height"
          unless padding.targetHeight preallocated.rows = preallocated.rows do
            throw s!"fixed-column component '{prepared.component.circuit.name}' cannot change height during padding"
      | none, _ => pure ()
      match mode with
      | .demand _ => pure ()
      | .preallocated preallocated =>
          unless fixedWidth + preallocated.input.length = prepared.inputWidth do
            throw s!"preallocated input suffix for component '{prepared.component.circuit.name}' has width \
              {preallocated.input.length}, expected {prepared.inputWidth - fixedWidth}"
          for cell in preallocated.input do
            if let .proverInput offset stride := cell then
              if preallocated.rows > 0 then
                let last := offset + (preallocated.rows - 1) * stride
                unless last < proverInputWidth do
                  throw s!"preallocated input for component '{prepared.component.circuit.name}' reads \
                    prover-input cell {last}, but the input width is {proverInputWidth}"
          for handler in preallocated.handlers do
            unless handler.interaction < prepared.interactions.length do
              throw s!"preallocated handler interaction {handler.interaction} for component \
                '{prepared.component.circuit.name}' is out of bounds"
            unless fixedWidth ≤ handler.column && handler.column < prepared.inputWidth do
              throw s!"preallocated handler column {handler.column} for component \
                '{prepared.component.circuit.name}' is not a mutable input column"
      validateModes proverInputWidth components modes paddings
  | _, _, _ => .error "generation metadata does not match ensemble component count"

private def padAndBalance (ensemble : Ensemble F PublicIO) (config : Config F ProverInput)
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
def generate (ensemble : Ensemble F PublicIO) (config : Config F ProverInput)
    (publicInput : PublicIO F) (proverInput : ProverInput F) :
    Except String (EnsembleWitness ensemble) :=
  let prepared := ensemble.tables.map prepareComponent
  match validateModes (size ProverInput) prepared config.modes config.padding with
  | .error error => .error error
  | .ok () => match initializeTableInputs (toElements proverInput).toArray prepared config.modes with
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
