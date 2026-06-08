import Clean.Halo2.Synthesis

/-!
# Clean-like formal semantics for Halo2 circuits

This module is the beginning of the proof-facing Halo2 layer.  The names mirror
Clean's core vocabulary (`Operation`, `Circuit`, `FormalCircuit`) while keeping
Halo2's row/column arithmetization explicit: cells are addressed by columns and
rows, gates are evaluated at rows with rotations, and copy constraints are first
class operations rather than being erased into ordinary equality assertions.
-/

namespace Halo2

open Halo2.Pinned

/-- A concrete assignment for a Halo2 arithmetization trace.  Rows are integers
so that rotations are interpreted directly; well-formed circuits can separately
rule out invalid negative accesses if needed. -/
structure Trace (F : Type) where
  advice : Nat → Int → F
  fixed : Nat → Int → F
  instanceValue : Nat → Int → F
  constant : String → F

namespace Trace

variable {F : Type}

/-- Evaluate a concrete Halo2 cell in a trace. -/
def evalCell (t : Trace F) (cell : Synthesis.Cell) : F :=
  match cell.column.columnType with
  | ColumnKind.Advice => t.advice cell.column.index cell.row
  | ColumnKind.Fixed => t.fixed cell.column.index cell.row
  | ColumnKind.Instance => t.instanceValue cell.column.index cell.row

/-- View a global trace from a region starting at `baseRow`.  Gadget specs can
use this relative view and avoid mentioning global Plonk row numbers. -/
def relative (t : Trace F) (baseRow : Int) : Trace F where
  advice column row := t.advice column (baseRow + row)
  fixed column row := t.fixed column (baseRow + row)
  instanceValue column row := t.instanceValue column (baseRow + row)
  constant := t.constant

end Trace

/-- A cell addressed relative to the start of a gadget/region. -/
structure LocalCell where
  column : Pinned.Column
  row : Nat
  deriving Repr, DecidableEq, BEq

namespace LocalCell

/-- Local advice cell constructor. -/
def advice (column row : Nat) : LocalCell :=
  { column := Pinned.Column.advice column, row }

/-- Local fixed cell constructor. -/
def fixed (column row : Nat) : LocalCell :=
  { column := Pinned.Column.fixed column, row }

/-- Local instance cell constructor. -/
def instanceCol (column row : Nat) : LocalCell :=
  { column := Pinned.Column.instanceCol column, row }

/-- Place a local cell at an absolute row in the global Plonk trace. -/
def place (baseRow : Nat) (cell : LocalCell) : Synthesis.Cell :=
  { column := cell.column, row := baseRow + cell.row }

/-- Use a local cell as an expression inside a gate at local row `gateRow`.
The resulting expression uses a Halo2 rotation from the gate row to the cell row. -/
def expr (cell : LocalCell) (gateRow : Nat) (query : Nat := 0) : Pinned.Expression :=
  let rotation : Int := cell.row - gateRow
  match cell.column.columnType with
  | ColumnKind.Advice => .advice query cell.column.index (.rot rotation)
  | ColumnKind.Fixed => .fixed query cell.column.index (.rot rotation)
  | ColumnKind.Instance => .instance query cell.column.index (.rot rotation)

/-- Evaluate a local cell in a relative trace. -/
def eval {F : Type} (trace : Trace F) (cell : LocalCell) : F :=
  match cell.column.columnType with
  | ColumnKind.Advice => trace.advice cell.column.index cell.row
  | ColumnKind.Fixed => trace.fixed cell.column.index cell.row
  | ColumnKind.Instance => trace.instanceValue cell.column.index cell.row

@[simp]
theorem eval_relative {F : Type} (trace : Trace F) (baseRow : Nat) (cell : LocalCell) :
    cell.eval (trace.relative baseRow) = trace.evalCell (cell.place baseRow) := by
  cases cell with
  | mk column row =>
    cases column with
    | mk columnType index =>
      cases columnType <;> rfl

end LocalCell

namespace Pinned.Expression

/-- Evaluate a pinned Halo2 expression at a particular base row.  Query indices
are metadata and do not affect semantics; column, kind, and rotation do. -/
def eval {F : Type} [Ring F] (trace : Trace F) (row : Int) : Expression → F
  | .constant c => trace.constant c
  | .selector i => trace.fixed i row
  | .fixed _ column (.rot r) => trace.fixed column (row + r)
  | .advice _ column (.rot r) => trace.advice column (row + r)
  | .instance _ column (.rot r) => trace.instanceValue column (row + r)
  | .negated e => - eval trace row e
  | .sum a b => eval trace row a + eval trace row b
  | .product a b => eval trace row a * eval trace row b
  | .scaled e c => eval trace row e * trace.constant c

@[simp]
theorem eval_relative {F : Type} [Ring F] (trace : Trace F) (baseRow row : Int)
    (expr : Expression) :
    expr.eval (trace.relative baseRow) row = expr.eval trace (baseRow + row) := by
  induction expr generalizing row with
  | constant c => rfl
  | selector i => rfl
  | fixed query column rotation =>
    cases rotation
    simp [eval, Trace.relative, Int.add_assoc]
  | advice query column rotation =>
    cases rotation
    simp [eval, Trace.relative, Int.add_assoc]
  | «instance» query column rotation =>
    cases rotation
    simp [eval, Trace.relative, Int.add_assoc]
  | negated e ih => simp [eval, ih]
  | sum a b iha ihb => simp [eval, iha, ihb]
  | product a b iha ihb => simp [eval, iha, ihb]
  | scaled e c ih =>
    change eval (trace.relative baseRow) row e * (trace.relative baseRow).constant c =
      eval trace (baseRow + row) e * trace.constant c
    rw [ih row]
    rfl

end Pinned.Expression

namespace LocalCell

@[simp]
theorem expr_eval_at_gate_row {F : Type} [Ring F] (trace : Trace F)
    (cell : LocalCell) (gateRow : Nat) :
    (cell.expr gateRow).eval trace gateRow = cell.eval trace := by
  cases cell with
  | mk column row =>
    cases column with
    | mk index columnType =>
      have hRow : (gateRow : Int) + ((row : Int) - (gateRow : Int)) = row := by
        omega
      cases columnType <;> simp [expr, eval, Pinned.Expression.eval, hRow]

end LocalCell

/-- Halo2 operations, with Clean-like naming but Halo2-native structure. -/
inductive Operation where
  /-- A custom-gate polynomial evaluated at a concrete row. -/
  | gate : Nat → Pinned.Expression → Operation
  /-- A Halo2 copy/permutation edge.  This is intentionally not represented as
  an ordinary gate assertion, even though satisfaction implies equality of the
  two assigned values. -/
  | wire : Synthesis.Cell → Synthesis.Cell → Operation
  /-- A fixed-column assignment generated by layout/table assignment. -/
  | fixed : Synthesis.Cell → String → Operation
  /-- A lookup argument at a row.  Its semantics is supplied by the trace-local
  lookup predicate, so the core DSL can support different table interpretations. -/
  | lookup : Nat → List Pinned.Expression → List Pinned.Expression → Operation
  deriving Repr, DecidableEq, BEq

namespace Operation

/-- Clean-style alias for a Halo2 custom-gate assertion at a concrete row. -/
def assert (row : Nat) (expr : Pinned.Expression) : Operation :=
  .gate row expr

/-- Semantic satisfaction of one Halo2 operation. -/
def Satisfied {F : Type} [Ring F]
    (lookup : List F → List F → Prop) (trace : Trace F) : Operation → Prop
  | .gate row expr => expr.eval trace row = 0
  | .wire left right => trace.evalCell left = trace.evalCell right
  | .fixed cell value => trace.evalCell cell = trace.constant value
  | .lookup row inputs table =>
      lookup (inputs.map (Pinned.Expression.eval trace row))
        (table.map (Pinned.Expression.eval trace row))

@[simp]
theorem gate_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {expr : Pinned.Expression} :
    Operation.Satisfied lookup trace (.gate row expr) ↔ expr.eval trace row = 0 :=
  Iff.rfl

@[simp]
theorem wire_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {left right : Synthesis.Cell} :
    Operation.Satisfied lookup trace (.wire left right) ↔ trace.evalCell left = trace.evalCell right :=
  Iff.rfl

@[simp]
theorem fixed_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {cell : Synthesis.Cell} {value : String} :
    Operation.Satisfied lookup trace (.fixed cell value) ↔ trace.evalCell cell = trace.constant value :=
  Iff.rfl

@[simp]
theorem lookup_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {inputs table : List Pinned.Expression} :
    Operation.Satisfied lookup trace (.lookup row inputs table) ↔
      lookup (inputs.map (Pinned.Expression.eval trace row))
        (table.map (Pinned.Expression.eval trace row)) :=
  Iff.rfl

end Operation

/-- A gadget/region-local Halo2 operation.  Rows are relative to the start of the
region, so gadget authors do not need to know the operation's final global row. -/
inductive LocalOperation where
  | gate : Nat → Pinned.Expression → LocalOperation
  | wire : LocalCell → LocalCell → LocalOperation
  | fixed : LocalCell → String → LocalOperation
  | lookup : Nat → List Pinned.Expression → List Pinned.Expression → LocalOperation
  deriving Repr, DecidableEq, BEq

namespace LocalOperation

/-- Clean-style alias for a local custom-gate assertion. -/
def assert (row : Nat) (expr : Pinned.Expression) : LocalOperation :=
  .gate row expr

/-- Place a local operation at an absolute base row. -/
def place (baseRow : Nat) : LocalOperation → Operation
  | .gate row expr => .gate (baseRow + row) expr
  | .wire left right => .wire (left.place baseRow) (right.place baseRow)
  | .fixed cell value => .fixed (cell.place baseRow) value
  | .lookup row inputs table => .lookup (baseRow + row) inputs table

/-- Satisfaction of a local operation against a relative trace. -/
def Satisfied {F : Type} [Ring F]
    (lookup : List F → List F → Prop) (trace : Trace F) : LocalOperation → Prop
  | .gate row expr => expr.eval trace row = 0
  | .wire left right => left.eval trace = right.eval trace
  | .fixed cell value => cell.eval trace = trace.constant value
  | .lookup row inputs table =>
      lookup (inputs.map (Pinned.Expression.eval trace row))
        (table.map (Pinned.Expression.eval trace row))

@[simp]
theorem place_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {baseRow : Nat} {op : LocalOperation} :
    (op.place baseRow).Satisfied lookup trace ↔
      op.Satisfied lookup (trace.relative baseRow) := by
  cases op with
  | gate row expr =>
    simp [place, Satisfied, Pinned.Expression.eval_relative, Nat.cast_add]
  | wire left right =>
    simp [place, Satisfied]
  | fixed cell value =>
    simp [place, Satisfied]
    change trace.evalCell (cell.place baseRow) = trace.constant value ↔
      trace.evalCell (cell.place baseRow) = trace.constant value
    rfl
  | lookup row inputs table =>
    have hInputs : inputs.map (Pinned.Expression.eval (trace.relative baseRow) row) =
        inputs.map (Pinned.Expression.eval trace (baseRow + row)) := by
      apply List.map_congr_left
      intro expr _
      simp [Pinned.Expression.eval_relative]
    have hTable : table.map (Pinned.Expression.eval (trace.relative baseRow) row) =
        table.map (Pinned.Expression.eval trace (baseRow + row)) := by
      apply List.map_congr_left
      intro expr _
      simp [Pinned.Expression.eval_relative]
    simp [place, Satisfied, hInputs, hTable, Nat.cast_add]

end LocalOperation

/-- A Halo2 circuit as a list of proof-facing operations.  This intentionally
resembles Clean's `Circuit`, but its operations are Halo2-native. -/
structure Circuit where
  operations : List Operation := []
deriving Repr, DecidableEq, BEq

namespace Circuit

instance : EmptyCollection Circuit where
  emptyCollection := {}

/-- Append one operation to a Halo2 circuit. -/
def push (c : Circuit) (op : Operation) : Circuit :=
  { c with operations := c.operations ++ [op] }

/-- A one-operation custom-gate circuit. -/
def gate (row : Nat) (expr : Pinned.Expression) : Circuit :=
  { operations := [Operation.gate row expr] }

/-- Clean-style name for a one-operation Halo2 assertion circuit. -/
def assertZero (row : Nat) (expr : Pinned.Expression) : Circuit :=
  gate row expr

/-- A one-operation wire/copy-constraint circuit. -/
def wire (left right : Synthesis.Cell) : Circuit :=
  { operations := [Operation.wire left right] }

/-- A one-operation fixed-assignment circuit. -/
def fixed (cell : Synthesis.Cell) (value : String) : Circuit :=
  { operations := [Operation.fixed cell value] }

/-- A one-operation lookup circuit. -/
def lookup (row : Nat) (inputs table : List Pinned.Expression) : Circuit :=
  { operations := [Operation.lookup row inputs table] }

/-- Append many operations to a Halo2 circuit. -/
def append (c d : Circuit) : Circuit :=
  { operations := c.operations ++ d.operations }

instance : Append Circuit where
  append := append

/-- Semantic satisfaction of a Halo2 circuit. -/
def Satisfied {F : Type} [Ring F]
    (c : Circuit) (lookup : List F → List F → Prop) (trace : Trace F) : Prop :=
  ∀ op ∈ c.operations, op.Satisfied lookup trace

@[simp]
theorem empty_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} :
    ({ operations := [] } : Circuit).Satisfied lookup trace := by
  intro op h
  cases h

theorem append_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {c d : Circuit} :
    (c ++ d).Satisfied lookup trace ↔ c.Satisfied lookup trace ∧ d.Satisfied lookup trace := by
  constructor
  · intro h
    constructor
    · intro op hop
      apply h op
      change op ∈ c.operations ++ d.operations
      exact List.mem_append_left d.operations hop
    · intro op hop
      apply h op
      change op ∈ c.operations ++ d.operations
      exact List.mem_append_right c.operations hop
  · intro h op hop
    rcases h with ⟨hc, hd⟩
    change op ∈ c.operations ++ d.operations at hop
    rcases List.mem_append.mp hop with hopLeft | hopRight
    · exact hc op hopLeft
    · exact hd op hopRight

@[simp]
theorem push_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {c : Circuit} {op : Operation} :
    (c.push op).Satisfied lookup trace ↔ c.Satisfied lookup trace ∧ op.Satisfied lookup trace := by
  constructor
  · intro h
    constructor
    · intro op' hop'
      exact h op' (by simp [push, hop'])
    · exact h op (by simp [push])
  · intro h op' hop'
    rcases h with ⟨hc, hop⟩
    simp [push] at hop'
    rcases hop' with hop' | hop'
    · exact hc op' hop'
    · subst op'
      exact hop

@[simp]
theorem gate_circuit_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {expr : Pinned.Expression} :
    (gate row expr).Satisfied lookup trace ↔ expr.eval trace row = 0 := by
  constructor
  · intro h
    simpa [gate] using h (Operation.gate row expr) (by simp [gate])
  · intro h op hop
    simp [gate] at hop
    subst op
    simpa using h

@[simp]
theorem assertZero_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {expr : Pinned.Expression} :
    (assertZero row expr).Satisfied lookup trace ↔ expr.eval trace row = 0 := by
  simp [assertZero]

@[simp]
theorem wire_circuit_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {left right : Synthesis.Cell} :
    (wire left right).Satisfied lookup trace ↔ trace.evalCell left = trace.evalCell right := by
  constructor
  · intro h
    simpa [wire] using h (Operation.wire left right) (by simp [wire])
  · intro h op hop
    simp [wire] at hop
    subst op
    simpa using h

@[simp]
theorem fixed_circuit_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {cell : Synthesis.Cell} {value : String} :
    (fixed cell value).Satisfied lookup trace ↔ trace.evalCell cell = trace.constant value := by
  constructor
  · intro h
    simpa [fixed] using h (Operation.fixed cell value) (by simp [fixed])
  · intro h op hop
    simp [fixed] at hop
    subst op
    simpa using h

@[simp]
theorem lookup_circuit_satisfied {F : Type} [Ring F] {lookupRel : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {inputs table : List Pinned.Expression} :
    (lookup row inputs table).Satisfied lookupRel trace ↔
      lookupRel (inputs.map (Pinned.Expression.eval trace row))
        (table.map (Pinned.Expression.eval trace row)) := by
  constructor
  · intro h
    simpa [lookup] using h (Operation.lookup row inputs table) (by simp [lookup])
  · intro h op hop
    simp [lookup] at hop
    subst op
    simpa using h

/-- Create gate operations by checking every gate at every row. -/
def gatesFromConstraintSystem (cs : ConstraintSystem) (numRows : Nat) : Circuit :=
  { operations := List.flatten ((List.range numRows).map fun row =>
      cs.gates.map (fun gate => Operation.gate row gate)) }

/-- Create lookup operations by checking every lookup argument at every row. -/
def lookupsFromConstraintSystem (cs : ConstraintSystem) (numRows : Nat) : Circuit :=
  { operations := List.flatten ((List.range numRows).map fun row =>
      cs.lookups.map (fun lookup => Operation.lookup row lookup.inputExpressions lookup.tableExpressions)) }

/-- Proof-facing operations generated directly from pinned constraint-system metadata. -/
def fromConstraintSystem (cs : ConstraintSystem) (numRows : Nat) : Circuit :=
  gatesFromConstraintSystem cs numRows ++ lookupsFromConstraintSystem cs numRows

/-- Fixed assignments as proof-facing operations. -/
def fixedAssignments (assignments : List (Synthesis.Cell × String)) : Circuit :=
  { operations := assignments.map (fun (cell, value) => Operation.fixed cell value) }

/-- Copy constraints as proof-facing wire operations. -/
def wires (copies : List (Synthesis.Cell × Synthesis.Cell)) : Circuit :=
  { operations := copies.map (fun (left, right) => Operation.wire left right) }

/-- Convert a configured Halo2 circuit to the proof-facing operation list that is
visible from configuration and synthesis/layout metadata. -/
def fromConfigured {Config : Type} (c : Synthesis.ConfiguredCircuit Config) : Circuit :=
  let layout := c.synthesize c.config
  let rows := max 1 (max (Synthesis.activationRows layout.selectorActivations) layout.usedRows)
  fromConstraintSystem c.cs rows ++ fixedAssignments layout.fixedAssignments ++ wires layout.copyConstraints

end Circuit

/-- A gadget-local Halo2 circuit.  This is the API shape intended for reusable
gadgets: operations mention rows relative to a region, not absolute Plonk rows. -/
structure LocalCircuit where
  operations : List LocalOperation := []
deriving Repr, DecidableEq, BEq

namespace LocalCircuit

instance : EmptyCollection LocalCircuit where
  emptyCollection := {}

/-- Append one local operation. -/
def push (c : LocalCircuit) (op : LocalOperation) : LocalCircuit :=
  { c with operations := c.operations ++ [op] }

/-- A one-operation local custom-gate circuit. -/
def gate (row : Nat) (expr : Pinned.Expression) : LocalCircuit :=
  { operations := [LocalOperation.gate row expr] }

/-- Clean-style name for a one-operation local custom-gate assertion. -/
def assertZero (row : Nat) (expr : Pinned.Expression) : LocalCircuit :=
  gate row expr

/-- A one-operation local wire/copy constraint. -/
def wire (left right : LocalCell) : LocalCircuit :=
  { operations := [LocalOperation.wire left right] }

/-- A one-operation local fixed assignment. -/
def fixed (cell : LocalCell) (value : String) : LocalCircuit :=
  { operations := [LocalOperation.fixed cell value] }

/-- A one-operation local lookup. -/
def lookup (row : Nat) (inputs table : List Pinned.Expression) : LocalCircuit :=
  { operations := [LocalOperation.lookup row inputs table] }

/-- Append local circuits. -/
def append (c d : LocalCircuit) : LocalCircuit :=
  { operations := c.operations ++ d.operations }

instance : Append LocalCircuit where
  append := append

/-- Place a local circuit at an absolute base row. -/
def place (baseRow : Nat) (c : LocalCircuit) : Circuit :=
  { operations := c.operations.map (LocalOperation.place baseRow) }

/-- Semantic satisfaction of a local circuit against a relative trace. -/
def Satisfied {F : Type} [Ring F]
    (c : LocalCircuit) (lookup : List F → List F → Prop) (trace : Trace F) : Prop :=
  ∀ op ∈ c.operations, op.Satisfied lookup trace

@[simp]
theorem place_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {baseRow : Nat} {c : LocalCircuit} :
    (c.place baseRow).Satisfied lookup trace ↔
      c.Satisfied lookup (trace.relative baseRow) := by
  constructor
  · intro h op hop
    have hPlaced : LocalOperation.place baseRow op ∈ (c.place baseRow).operations := by
      exact List.mem_map.mpr ⟨op, hop, rfl⟩
    simpa using h (LocalOperation.place baseRow op) hPlaced
  · intro h op hop
    simp [place] at hop
    rcases hop with ⟨localOp, hLocal, rfl⟩
    simpa using h localOp hLocal

/-- Local circuit satisfaction composes under append. -/
theorem append_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {c d : LocalCircuit} :
    (c ++ d).Satisfied lookup trace ↔ c.Satisfied lookup trace ∧ d.Satisfied lookup trace := by
  constructor
  · intro h
    constructor
    · intro op hop
      exact h op (List.mem_append_left d.operations hop)
    · intro op hop
      exact h op (List.mem_append_right c.operations hop)
  · intro h op hop
    rcases h with ⟨hc, hd⟩
    change op ∈ c.operations ++ d.operations at hop
    rcases List.mem_append.mp hop with hopLeft | hopRight
    · exact hc op hopLeft
    · exact hd op hopRight

@[simp]
theorem push_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {c : LocalCircuit} {op : LocalOperation} :
    (c.push op).Satisfied lookup trace ↔ c.Satisfied lookup trace ∧ op.Satisfied lookup trace := by
  constructor
  · intro h
    constructor
    · intro op' hop'
      exact h op' (by simp [push, hop'])
    · exact h op (by simp [push])
  · intro h op' hop'
    rcases h with ⟨hc, hop⟩
    simp [push] at hop'
    rcases hop' with hop' | hop'
    · exact hc op' hop'
    · subst op'
      exact hop

@[simp]
theorem gate_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {expr : Pinned.Expression} :
    (gate row expr).Satisfied lookup trace ↔ expr.eval trace row = 0 := by
  constructor
  · intro h
    simpa [gate] using h (LocalOperation.gate row expr) (by simp [gate])
  · intro h op hop
    simp [gate] at hop
    subst op
    simpa [LocalOperation.Satisfied] using h

@[simp]
theorem assertZero_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {expr : Pinned.Expression} :
    (assertZero row expr).Satisfied lookup trace ↔ expr.eval trace row = 0 := by
  simp [assertZero]

@[simp]
theorem wire_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {left right : LocalCell} :
    (wire left right).Satisfied lookup trace ↔ left.eval trace = right.eval trace := by
  constructor
  · intro h
    simpa [wire] using h (LocalOperation.wire left right) (by simp [wire])
  · intro h op hop
    simp [wire] at hop
    subst op
    simpa [LocalOperation.Satisfied] using h

@[simp]
theorem fixed_satisfied {F : Type} [Ring F] {lookup : List F → List F → Prop}
    {trace : Trace F} {cell : LocalCell} {value : String} :
    (fixed cell value).Satisfied lookup trace ↔ cell.eval trace = trace.constant value := by
  constructor
  · intro h
    simpa [fixed] using h (LocalOperation.fixed cell value) (by simp [fixed])
  · intro h op hop
    simp [fixed] at hop
    subst op
    simpa [LocalOperation.Satisfied] using h

@[simp]
theorem lookup_satisfied {F : Type} [Ring F] {lookupRel : List F → List F → Prop}
    {trace : Trace F} {row : Nat} {inputs table : List Pinned.Expression} :
    (lookup row inputs table).Satisfied lookupRel trace ↔
      lookupRel (inputs.map (Pinned.Expression.eval trace row))
        (table.map (Pinned.Expression.eval trace row)) := by
  constructor
  · intro h
    simpa [lookup] using h (LocalOperation.lookup row inputs table) (by simp [lookup])
  · intro h op hop
    simp [lookup] at hop
    subst op
    simpa [LocalOperation.Satisfied] using h

end LocalCircuit

/-- Soundness statement for a Halo2 circuit: under assumptions, satisfying the
Halo2-native operations implies the Lean-level spec. -/
def Soundness {F : Type} [Ring F] (circuit : Circuit) (lookup : List F → List F → Prop)
    (Assumptions Spec : Trace F → Prop) : Prop :=
  ∀ {trace : Trace F}, Assumptions trace → circuit.Satisfied lookup trace → Spec trace

/-- Soundness statement for a reusable local gadget.  The trace passed to
`Assumptions` and `Spec` is relative to the gadget's region. -/
def GadgetSoundness {F : Type} [Ring F] (circuit : LocalCircuit)
    (lookup : List F → List F → Prop) (Assumptions Spec : Trace F → Prop) : Prop :=
  ∀ {trace : Trace F}, Assumptions trace → circuit.Satisfied lookup trace → Spec trace

/-- A proof-carrying local Halo2 gadget.  This is the scalable API for reusable
gadgets: proofs talk about local rows and local cells; placement into the global
Plonk trace is a separate operation. -/
structure FormalGadget (F : Type) [Ring F] where
  name : String := "anonymous"
  circuit : LocalCircuit
  lookup : List F → List F → Prop := fun _ _ => True
  Assumptions : Trace F → Prop := fun _ => True
  Spec : Trace F → Prop
  soundness : GadgetSoundness circuit lookup Assumptions Spec

namespace FormalGadget

/-- Use the local soundness proof packaged in a `FormalGadget`. -/
theorem sound {F : Type} [Ring F] (g : FormalGadget F) {trace : Trace F}
    (hAssumptions : g.Assumptions trace)
    (h : g.circuit.Satisfied g.lookup trace) : g.Spec trace :=
  g.soundness hAssumptions h

end FormalGadget

/-- A proof-carrying Halo2 circuit, mirroring Clean's `FormalCircuit` idea:
`circuit` is the Halo2 arithmetization, `Assumptions` are preconditions on the
trace, `Spec` is a Lean predicate over traces, and `soundness` proves that
satisfying the Halo2 operations implies the spec.  Unlike Clean's ordinary
`FormalCircuit`, this intentionally does not package completeness yet: Daira's
plan only needs knowledge soundness at this layer. -/
structure FormalCircuit (F : Type) [Ring F] where
  name : String := "anonymous"
  circuit : Circuit
  lookup : List F → List F → Prop := fun _ _ => True
  Assumptions : Trace F → Prop := fun _ => True
  Spec : Trace F → Prop
  soundness : Soundness circuit lookup Assumptions Spec

namespace FormalCircuit

/-- Package a configured/synthesized Halo2 circuit as a proof-carrying
`FormalCircuit`.  This is the intended bridge from the Halo2-like configure /
synthesize API to Clean-style formal reasoning. -/
def fromConfigured {F Config : Type} [Ring F] (name : String)
    (configured : Synthesis.ConfiguredCircuit Config)
    (lookup : List F → List F → Prop)
    (Assumptions Spec : Trace F → Prop)
    (soundness : Soundness (Circuit.fromConfigured configured) lookup Assumptions Spec) :
    FormalCircuit F :=
  { name, circuit := Circuit.fromConfigured configured, lookup, Assumptions, Spec, soundness }

/-- Use the soundness proof packaged in a `FormalCircuit`. -/
theorem sound {F : Type} [Ring F] (c : FormalCircuit F) {trace : Trace F}
    (hAssumptions : c.Assumptions trace)
    (h : c.circuit.Satisfied c.lookup trace) : c.Spec trace :=
  c.soundness hAssumptions h

end FormalCircuit

namespace FormalGadget

/-- Place a local gadget at an absolute base row to obtain a global
`FormalCircuit`.  The resulting global spec is phrased over the relative view of
the global trace at that base row. -/
def place {F : Type} [Ring F] (g : FormalGadget F) (baseRow : Nat) : FormalCircuit F :=
  { name := g.name
    circuit := g.circuit.place baseRow
    lookup := g.lookup
    Assumptions := fun trace => g.Assumptions (trace.relative baseRow)
    Spec := fun trace => g.Spec (trace.relative baseRow)
    soundness := by
      intro trace hAssumptions hSatisfied
      exact g.sound hAssumptions (LocalCircuit.place_satisfied.mp hSatisfied) }

/-- Direct use form of placed-gadget soundness. -/
theorem sound_placed {F : Type} [Ring F] (g : FormalGadget F) (baseRow : Nat)
    {trace : Trace F} (hAssumptions : g.Assumptions (trace.relative baseRow))
    (h : (g.circuit.place baseRow).Satisfied g.lookup trace) :
    g.Spec (trace.relative baseRow) :=
  g.sound hAssumptions (LocalCircuit.place_satisfied.mp h)

end FormalGadget

end Halo2
