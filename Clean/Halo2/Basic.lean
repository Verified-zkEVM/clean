import Clean.Circuit.Expression

namespace Halo2

inductive ColumnKind where
  | advice
  | fixed
  | instance
deriving DecidableEq, Repr

structure Column (kind : ColumnKind) where
  index : ℕ
deriving DecidableEq, Repr

structure Selector where
  index : ℕ
  simple : Bool
deriving DecidableEq, Repr

/-- Halo2 rotations are relative row offsets. -/
abbrev Rotation := Int

inductive Query where
  | selector : Selector → Query
  | fixed : Column .fixed → Query
  | advice : Column .advice → Rotation → Query
  | instance : Column .instance → Rotation → Query
deriving DecidableEq, Repr

abbrev Variable (F : Type) := VariableWithLocation F Query

abbrev Expression (F : Type) := ExpressionWithLocation F Query

def Expression.containsSimpleSelector {F : Type} : Expression F → Bool
  | .var { index := .selector selector } => selector.simple
  | .var _ => false
  | .const _ => false
  | .add x y => Expression.containsSimpleSelector x || Expression.containsSimpleSelector y
  | .mul x y => Expression.containsSimpleSelector x || Expression.containsSimpleSelector y

structure TableColumn where
  inner : Column .fixed
deriving DecidableEq, Repr

structure VirtualCell where
  query : Query
deriving DecidableEq, Repr

structure VirtualCellsState where
  queriedSelectors : Array Selector := #[]
  queriedCells : Array VirtualCell := #[]

abbrev VirtualCells (_ : Type) := StateM VirtualCellsState

def querySelector {F : Type} (selector : Selector) : VirtualCells F (Expression F) := do
  modify fun state => { state with queriedSelectors := state.queriedSelectors.push selector }
  return .var { index := .selector selector }

def queryFixed {F : Type} (column : Column .fixed) : VirtualCells F (Expression F) := do
  modify fun state => { state with queriedCells := state.queriedCells.push { query := .fixed column } }
  return .var { index := .fixed column }

def queryAdvice {F : Type} (column : Column .advice) (rotation : Rotation) : VirtualCells F (Expression F) := do
  modify fun state => { state with queriedCells := state.queriedCells.push { query := .advice column rotation } }
  return .var { index := .advice column rotation }

def queryInstance {F : Type} (column : Column .instance) (rotation : Rotation) : VirtualCells F (Expression F) := do
  modify fun state => { state with queriedCells := state.queriedCells.push { query := .instance column rotation } }
  return .var { index := .instance column rotation }

structure Constraint (F : Type) where
  name : String := ""
  expression : Expression F

structure Gate (F : Type) where
  name : String
  constraints : Array (Constraint F)
  queriedSelectors : Array Selector
  queriedCells : Array VirtualCell

structure Lookup (F : Type) where
  name : String
  tableMap : Array (Expression F × TableColumn)
  queriedCells : Array VirtualCell

def Lookup.containsSimpleSelector {F : Type} (lookup : Lookup F) : Bool :=
  lookup.tableMap.any fun (input, _) => input.containsSimpleSelector

structure ConfigureState (F : Type) where
  nextAdvice : ℕ := 0
  nextFixed : ℕ := 0
  nextInstance : ℕ := 0
  nextSelector : ℕ := 0
  gates : Array (Gate F) := #[]
  lookups : Array (Lookup F) := #[]

abbrev Configure (F : Type) := StateM (ConfigureState F)

def adviceColumn {F : Type} : Configure F (Column .advice) := do
  let state ← get
  let column := { index := state.nextAdvice }
  set { state with nextAdvice := state.nextAdvice + 1 }
  return column

def fixedColumn {F : Type} : Configure F (Column .fixed) := do
  let state ← get
  let column := { index := state.nextFixed }
  set { state with nextFixed := state.nextFixed + 1 }
  return column

def instanceColumn {F : Type} : Configure F (Column .instance) := do
  let state ← get
  let column := { index := state.nextInstance }
  set { state with nextInstance := state.nextInstance + 1 }
  return column

def selector {F : Type} : Configure F Selector := do
  let state ← get
  let selector := { index := state.nextSelector, simple := true }
  set { state with nextSelector := state.nextSelector + 1 }
  return selector

def complexSelector {F : Type} : Configure F Selector := do
  let state ← get
  let selector := { index := state.nextSelector, simple := false }
  set { state with nextSelector := state.nextSelector + 1 }
  return selector

def lookupTableColumn {F : Type} : Configure F TableColumn := do
  let column ← fixedColumn
  return { inner := column }

def createGate {F : Type}
    (name : String)
    (build : VirtualCells F (Array (Constraint F))) :
    Configure F Unit := do
  let (constraints, cells) := build.run {}
  let state ← get
  set {
    state with
    gates := state.gates.push {
      name
      constraints
      queriedSelectors := cells.queriedSelectors
      queriedCells := cells.queriedCells
    }
  }

def createLookup
    {F : Type}
    (name : String)
    (build : VirtualCells F (Array (Expression F × TableColumn))) :
    Configure F Unit := do
  let (tableMap, cells) := build.run {}
  let state ← get
  set {
    state with
    lookups := state.lookups.push {
      name
      tableMap
      queriedCells := cells.queriedCells
    }
  }

end Halo2
