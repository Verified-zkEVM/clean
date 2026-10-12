module

public import Clean.Backends.Plonky3.Rust

@[expose] public section

/-!
# Witness IR to Rust model

Translates Clean expressions and witness programs into the typed Rust model. The translation is
total; `Correctness.lean` proves that the Rust model computes the witness IR's values.

The witness IR's index `.idx` is the row index outside loops and the loop variable inside
`mapRange`; `inLoop` records which one an expression is translated for.
-/

namespace Backends.Plonky3.Codegen

open Rust

variable {F : Type}

/-- A circuit expression reading cells of the function's row slice. -/
def expression : Expression F → FieldExpr F
  | .var cell => .cell cell.index
  | .const value => .const value
  | .add left right => .add (expression left) (expression right)
  | .mul left right => .mul (expression left) (expression right)

/-- The values of a list of constant expressions, if all are constants. -/
def constants? : List (Witgen.FExpr F) → Option (List F)
  | [] => some []
  | .const value :: values => (constants? values).map (value :: ·)
  | _ => none

mutual

def fieldExpr (inLoop : Bool) : Witgen.FExpr F → FieldExpr F
  | .expr e => expression e
  | .const value => .const value
  | .localVar index => .localVar index
  | .add left right => .add (fieldExpr inLoop left) (fieldExpr inLoop right)
  | .mul left right => .mul (fieldExpr inLoop left) (fieldExpr inLoop right)
  | .inv value => .inverseOrZero (fieldExpr inLoop value)
  | .ofU64 value => .fromU64 (u64Expr inLoop value)
  | .ite condition thenValue elseValue =>
      .ite (boolExpr inLoop condition) (fieldExpr inLoop thenValue) (fieldExpr inLoop elseValue)
  | .listGet values index =>
      match constants? values with
      | some constants => .constMatch constants (u64Expr inLoop index)
      | none => .arrayGet (fieldExprList inLoop values) (u64Expr inLoop index)
  | .dataGet key width row column => .dataGet key width (u64Expr inLoop row) column.val
  | .hintGet key width row column => .hintGet key width (u64Expr inLoop row) column.val

def fieldExprList (inLoop : Bool) : List (Witgen.FExpr F) → List (FieldExpr F)
  | [] => []
  | value :: values => fieldExpr inLoop value :: fieldExprList inLoop values

def u64Expr (inLoop : Bool) : Witgen.U64Expr F → U64Expr F
  | .const value => .const value
  | .val value => .canonical (fieldExpr inLoop value)
  | .idx => if inLoop then .loopVar else .rowIndex
  | .localVar index => .localVar index
  | .add left right => .wrappingAdd (u64Expr inLoop left) (u64Expr inLoop right)
  | .mul left right => .wrappingMul (u64Expr inLoop left) (u64Expr inLoop right)
  | .div left right => .safeDiv (u64Expr inLoop left) (u64Expr inLoop right)
  | .mod left right => .safeRem (u64Expr inLoop left) (u64Expr inLoop right)
  | .land left right => .and (u64Expr inLoop left) (u64Expr inLoop right)
  | .lor left right => .or (u64Expr inLoop left) (u64Expr inLoop right)
  | .lxor left right => .xor (u64Expr inLoop left) (u64Expr inLoop right)
  | .shiftL left right => .wrappingShl (u64Expr inLoop left) (u64Expr inLoop right)
  | .shiftR left right => .wrappingShr (u64Expr inLoop left) (u64Expr inLoop right)
  | .ite condition thenValue elseValue =>
      .ite (boolExpr inLoop condition) (u64Expr inLoop thenValue) (u64Expr inLoop elseValue)

def boolExpr (inLoop : Bool) : Witgen.BExpr F → BoolExpr F
  | .true => .true
  | .false => .false
  | .feq left right => .fieldEq (fieldExpr inLoop left) (fieldExpr inLoop right)
  | .neq left right => .u64Eq (u64Expr inLoop left) (u64Expr inLoop right)
  | .lt left right => .u64Lt (u64Expr inLoop left) (u64Expr inLoop right)
  | .flt left right =>
      .u64Lt (.canonical (fieldExpr inLoop left)) (.canonical (fieldExpr inLoop right))
  | .bit value bit =>
      if bit < 64 then
        .u64Eq (.and (.wrappingShr (.canonical (fieldExpr inLoop value)) (.const bit.toUInt64))
          (.const 1)) (.const 1)
      else .false
  | .not condition => .not (boolExpr inLoop condition)
  | .and left right => .and (boolExpr inLoop left) (boolExpr inLoop right)

end

/-- `let` statements for witness IR steps. -/
def steps : List (Witgen.Step F) → List (Stmt F)
  | [] => []
  | .letF value :: rest => .letField (fieldExpr false value) :: steps rest
  | .letU value :: rest => .letU64 (u64Expr false value) :: steps rest

/-- Statements pushing a witness IR output vector. -/
def output : {n : ℕ} → Witgen.VExpr F n → List (Stmt F)
  | _, .lit values => values.toList.map fun value => .push (fieldExpr false value)
  | _, .mapRange count body => [.forPush count (fieldExpr true body)]
  | count, .envRange offset => [.forPush count (.cellAtLoop offset)]
  | count, .bitsOf value =>
      [.forPush count (.fromU64 (.loopBit (.canonical (fieldExpr false value))))]
  | _, .append left right => output left ++ output right

/-- The body of a function computing a witness IR program's output vector. -/
def program {n : ℕ} (programSteps : List (Witgen.Step F)) (programOutput : Witgen.VExpr F n) :
    List (Stmt F) :=
  steps programSteps ++ output programOutput

end Backends.Plonky3.Codegen
