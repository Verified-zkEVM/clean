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

structure Constraint (F : Type) where
  name : String := ""
  expression : Expression F

structure VirtualCell where
  query : Query
deriving DecidableEq, Repr

structure VirtualCellsState (F : Type) where
  queriedSelectors : Array Selector := #[]
  queriedCells : Array VirtualCell := #[]
  constraints : Array (Constraint F) := #[]
  registeredInputs : Option (Array (Expression F)) := none

def VirtualCells (F : Type) (α : Type) := VirtualCellsState F → α × VirtualCellsState F

namespace VirtualCells

def bind {F : Type} {α β : Type} (x : VirtualCells F α) (f : α → VirtualCells F β) :
    VirtualCells F β := fun state =>
  let (a, state') := x state
  f a state'

instance {F : Type} : Monad (VirtualCells F) where
  pure a := fun state => (a, state)
  bind := bind

def run {F : Type} {α : Type} (x : VirtualCells F α) (state : VirtualCellsState F) :
    α × VirtualCellsState F :=
  x state

@[circuit_norm]
theorem bind_def {F : Type} {α β : Type} (x : VirtualCells F α) (f : α → VirtualCells F β) :
    x >>= f = fun state =>
      let (a, state') := x state
      f a state' := rfl

@[circuit_norm]
theorem pure_def {F : Type} {α : Type} (a : α) :
    (pure a : VirtualCells F α) = fun state => (a, state) := rfl

@[circuit_norm]
theorem run_def {F : Type} {α : Type} (x : VirtualCells F α) (state : VirtualCellsState F) :
    x.run state = x state := rfl

end VirtualCells

def querySelector {F : Type} (selector : Selector) : VirtualCells F (Expression F) := fun state =>
  (.var { index := .selector selector },
    { state with queriedSelectors := state.queriedSelectors.push selector })

def queryFixed {F : Type} (column : Column .fixed) : VirtualCells F (Expression F) := fun state =>
  (.var { index := .fixed column },
    { state with queriedCells := state.queriedCells.push { query := .fixed column } })

def queryAdvice {F : Type} (column : Column .advice) (rotation : Rotation) : VirtualCells F (Expression F) := fun state =>
  (.var { index := .advice column rotation },
    { state with queriedCells := state.queriedCells.push { query := .advice column rotation } })

def queryInstance {F : Type} (column : Column .instance) (rotation : Rotation) : VirtualCells F (Expression F) := fun state =>
  (.var { index := .instance column rotation },
    { state with queriedCells := state.queriedCells.push { query := .instance column rotation } })

def assertZero {F : Type} (expression : Expression F) : VirtualCells F Unit := fun state =>
  ((), { state with constraints := state.constraints.push { expression } })

def assertEq {F : Type} [Field F] (x y : Expression F) : VirtualCells F Unit :=
  assertZero (x - y)

scoped infix:50 " === " => assertEq

structure Gate (F : Type) where
  name : String
  constraints : Array (Constraint F)
  queriedSelectors : Array Selector
  queriedCells : Array VirtualCell
  registeredInputs : Option (Array (Expression F)) := none

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

def Configure (F : Type) (α : Type) := ConfigureState F → α × ConfigureState F

namespace Configure

def bind {F : Type} {α β : Type} (x : Configure F α) (f : α → Configure F β) :
    Configure F β := fun state =>
  let (a, state') := x state
  f a state'

instance {F : Type} : Monad (Configure F) where
  pure a := fun state => (a, state)
  bind := bind

def run {F : Type} {α : Type} (x : Configure F α) (state : ConfigureState F) :
    α × ConfigureState F :=
  x state

@[circuit_norm]
theorem bind_def {F : Type} {α β : Type} (x : Configure F α) (f : α → Configure F β) :
    x >>= f = fun state =>
      let (a, state') := x state
      f a state' := rfl

@[circuit_norm]
theorem pure_def {F : Type} {α : Type} (a : α) :
    (pure a : Configure F α) = fun state => (a, state) := rfl

@[circuit_norm]
theorem run_def {F : Type} {α : Type} (x : Configure F α) (state : ConfigureState F) :
    x.run state = x state := rfl

end Configure

def adviceColumn {F : Type} : Configure F (Column .advice) := fun state =>
  let column := { index := state.nextAdvice }
  (column, { state with nextAdvice := state.nextAdvice + 1 })

def fixedColumn {F : Type} : Configure F (Column .fixed) := fun state =>
  let column := { index := state.nextFixed }
  (column, { state with nextFixed := state.nextFixed + 1 })

def instanceColumn {F : Type} : Configure F (Column .instance) := fun state =>
  let column := { index := state.nextInstance }
  (column, { state with nextInstance := state.nextInstance + 1 })

def selector {F : Type} : Configure F Selector := fun state =>
  let selector := { index := state.nextSelector, simple := true }
  (selector, { state with nextSelector := state.nextSelector + 1 })

def complexSelector {F : Type} : Configure F Selector := fun state =>
  let selector := { index := state.nextSelector, simple := false }
  (selector, { state with nextSelector := state.nextSelector + 1 })

def lookupTableColumn {F : Type} : Configure F TableColumn := do
  let column ← fixedColumn
  return { inner := column }

def createGateRaw {F : Type}
    (name : String)
    (build : VirtualCells F (Array (Constraint F))) :
    Configure F Unit := fun state =>
  let (constraints, cells) := build.run ({} : VirtualCellsState F)
  ((), {
    state with
    gates := state.gates.push {
      name
      constraints
      queriedSelectors := cells.queriedSelectors
      queriedCells := cells.queriedCells
      registeredInputs := cells.registeredInputs
    }
  })

def createGate {F : Type}
    (name : String)
    (build : VirtualCells F Unit) :
    Configure F Unit := fun state =>
  let (_, cells) := build.run ({} : VirtualCellsState F)
  ((), {
    state with
    gates := state.gates.push {
      name
      constraints := cells.constraints
      queriedSelectors := cells.queriedSelectors
      queriedCells := cells.queriedCells
      registeredInputs := cells.registeredInputs
    }
  })

def createLookup
    {F : Type}
    (name : String)
    (build : VirtualCells F (Array (Expression F × TableColumn))) :
    Configure F Unit := fun state =>
  let (tableMap, cells) := build.run ({} : VirtualCellsState F)
  ((), {
    state with
    lookups := state.lookups.push {
      name
      tableMap
      queriedCells := cells.queriedCells
    }
  })

end Halo2
