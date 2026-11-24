import Midnight.SHA256.WitnessCircuit
import Midnight.SHA256.SynthesisLayout

/-! Lossless structural encoding, independent of the closed source comparison.
Keeping these definitions separate lets bounded source proofs use the encoding
without importing the equality they establish. -/
namespace Midnight.SHA256.WitnessErasure
open Halo2

namespace Code
/-- Lossless structural representation with exactly the advice program omitted. -/
inductive Region where
  | advice (column : Column .advice) (row : Nat)
  | fixed (column : Column .fixed) (row : Nat) (value : F)
  | gate (gate : Gate F) (row : Nat)
  | lookup (argument : LookupArgument F) (enabled : List Selector) (row : Nat)
  | equal (left right : Halo2.Cell)
  | constant (cell : Halo2.Cell) (value : F)
  | instanceCopy (cell : Halo2.Cell) (column : Column .instance) (row : Nat)
  deriving DecidableEq

def encodeRegion : RegionOperation F → Region
  | .assignAdvice column row _ => .advice column row
  | .assignFixed column row value => .fixed column row value
  | .enableGate gate row => .gate gate row
  | .enableLookup argument enabled row => .lookup argument enabled row
  | .constrainEqual left right => .equal left right
  | .constrainConstant cell value => .constant cell value
  | .constrainInstance cell column row => .instanceCopy cell column row

def decodeRegion : Region → RegionOperation F
  | .advice column row => .assignAdvice column row (.ofFExpr (.const 0))
  | .fixed column row value => .assignFixed column row value
  | .gate gate row => .enableGate gate row
  | .lookup argument enabled row => .enableLookup argument enabled row
  | .equal left right => .constrainEqual left right
  | .constant cell value => .constrainConstant cell value
  | .instanceCopy cell column row => .constrainInstance cell column row

inductive Top where
  | region (name : String) (body : List Region)
  | instanceCopy (cell : Halo2.Cell) (column : Column .instance) (row : Nat)
  | table (column : TableColumn) (values : List F)
  deriving DecidableEq

def encode : Operation F → Top
  | .region name body => .region name (body.map encodeRegion)
  | .constrainInstance cell column row => .instanceCopy cell column row
  | .loadTable column values => .table column values

def decode : Top → Operation F
  | .region name body => .region name (body.map decodeRegion)
  | .instanceCopy cell column row => .constrainInstance cell column row
  | .table column values => .loadTable column values

end Code

/-- One closed input used solely to discharge the structural comparison. No
input values are evaluated by the operation builder or this theorem. -/
def referenceInput : Vector (WitgenIR F 1) 24 := Vector.replicate 24 (.ofFExpr (.const 0))

end Midnight.SHA256.WitnessErasure
