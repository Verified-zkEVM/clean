import Clean.Gadgets.Equality

/-!
# A small Halo2-in-Clean framework

This module models the Halo2 layout layer as data, and interprets that data as a
Clean circuit.  The intent is that custom gates and copy constraints are not a
separate semantics: they compile to ordinary Clean assertions.

The `PinnedVerificationKey` below is deliberately a structural, audit-friendly
record of the arithmetization data that affects verification: columns, gates,
selectors, fixed cells, and copy constraints.  It is the object we compare
against fixtures produced from Rust.
-/

namespace Halo2

variable {F : Type} [Field F]

inductive ColumnType where
  | advice
  | fixed
  | instance
deriving Repr, DecidableEq, BEq

structure Column where
  type : ColumnType
  index : Nat
deriving Repr, DecidableEq, BEq

structure Cell where
  column : Column
  row : Nat
deriving Repr, DecidableEq, BEq

namespace Column

def advice (index : Nat) : Column := ⟨.advice, index⟩
def fixed (index : Nat) : Column := ⟨.fixed, index⟩
def instanceCol (index : Nat) : Column := ⟨.instance, index⟩

end Column

/-- Expressions in the pinned Halo2 arithmetization. Constants are named so this
structure is field-independent and can be used as a VK fixture. -/
inductive Expr where
  | query : Column → Int → Expr
  | const : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
deriving Repr, DecidableEq, BEq

namespace Expr

instance : Neg Expr where neg := Expr.neg
instance : Add Expr where add := Expr.add
instance : Sub Expr where sub a b := a + (-b)
instance : Mul Expr where mul := Expr.mul

/-- Evaluate a Halo2 expression at a row into a Clean expression over cells. -/
def toClean (constValue : String → F) (cellValue : Cell → Expression F)
    (row : Nat) : Expr → Expression F
  | .query column rot =>
      let shifted : Int := Int.ofNat row + rot
      match shifted with
      | .ofNat row' => cellValue ⟨column, row'⟩
      | .negSucc _ => 0
  | .const name => constValue name
  | .add a b => toClean constValue cellValue row a + toClean constValue cellValue row b
  | .mul a b => toClean constValue cellValue row a * toClean constValue cellValue row b
  | .neg a => - toClean constValue cellValue row a

end Expr

/-- A custom gate constraint, before selector multiplication. -/
structure GateConstraint where
  name : String
  expr : Expr
deriving Repr, DecidableEq, BEq

/-- One Halo2 custom gate. If `selector = some q`, each constraint is enforced as
`q(row) * expr(row) = 0`; if `none`, it is always enabled. -/
structure CustomGate where
  name : String
  selector : Option Column := none
  constraints : List GateConstraint
deriving Repr, DecidableEq, BEq

structure CopyConstraint where
  left : Cell
  right : Cell
deriving Repr, DecidableEq, BEq

structure FixedAssignment where
  cell : Cell
  value : String
deriving Repr, DecidableEq, BEq

/-- A laid-out Halo2 circuit, expressed as data but with Clean semantics via
`toCleanCircuit`. -/
structure CircuitDescription where
  k : Nat
  adviceColumns : Nat
  fixedColumns : Nat
  instanceColumns : Nat
  equalityEnabled : List Column := []
  lookupTables : List String := []
  gates : List CustomGate := []
  copyConstraints : List CopyConstraint := []
  fixedAssignments : List FixedAssignment := []
deriving Repr, DecidableEq, BEq

/-- The pinned verification-key data that our current model records. -/
structure PinnedVerificationKey where
  k : Nat
  adviceColumns : Nat
  fixedColumns : Nat
  instanceColumns : Nat
  equalityEnabled : List Column
  lookupTables : List String
  gates : List CustomGate
  copyConstraints : List CopyConstraint
  fixedAssignments : List FixedAssignment
deriving Repr, DecidableEq, BEq

namespace CircuitDescription

/-- Step 2: compile the Lean Halo2 circuit description to a pinned VK. -/
def compile (c : CircuitDescription) : PinnedVerificationKey where
  k := c.k
  adviceColumns := c.adviceColumns
  fixedColumns := c.fixedColumns
  instanceColumns := c.instanceColumns
  equalityEnabled := c.equalityEnabled
  lookupTables := c.lookupTables
  gates := c.gates
  copyConstraints := c.copyConstraints
  fixedAssignments := c.fixedAssignments

private def assertExpr (e : Expression F) : Circuit F Unit :=
  assertZero e

private def assertGateConstraint (constValue : String → F) (cellValue : Cell → Expression F)
    (row : Nat) (selector : Option Column) (constraint : GateConstraint) : Circuit F Unit :=
  let e := constraint.expr.toClean constValue cellValue row
  let selected :=
    match selector with
    | none => e
    | some q => cellValue ⟨q, row⟩ * e
  assertExpr selected

private def assertGateAtRow (constValue : String → F) (cellValue : Cell → Expression F)
    (row : Nat) (gate : CustomGate) : Circuit F Unit := do
  for constraint in gate.constraints do
    assertGateConstraint constValue cellValue row gate.selector constraint

private def assertCopy (cellValue : Cell → Expression F) (copy : CopyConstraint) : Circuit F Unit :=
  assertZero (cellValue copy.left - cellValue copy.right)

private def assertFixed (constValue : String → F) (cellValue : Cell → Expression F)
    (fixed : FixedAssignment) : Circuit F Unit :=
  assertZero (cellValue fixed.cell - constValue fixed.value)

/-- Interpret the laid-out Halo2 circuit as ordinary Clean assertions. -/
def toCleanCircuit (c : CircuitDescription) (constValue : String → F)
    (cellValue : Cell → Expression F) : Circuit F Unit := do
  for row in List.range (2 ^ c.k) do
    for gate in c.gates do
      assertGateAtRow constValue cellValue row gate
  for copy in c.copyConstraints do
    assertCopy cellValue copy
  for fixed in c.fixedAssignments do
    assertFixed constValue cellValue fixed

@[simp]
theorem compile_eq (c : CircuitDescription) : c.compile = {
    k := c.k
    adviceColumns := c.adviceColumns
    fixedColumns := c.fixedColumns
    instanceColumns := c.instanceColumns
    equalityEnabled := c.equalityEnabled
    lookupTables := c.lookupTables
    gates := c.gates
    copyConstraints := c.copyConstraints
    fixedAssignments := c.fixedAssignments } := rfl

end CircuitDescription

end Halo2
