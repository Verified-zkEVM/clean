module

public import Clean.Circuit.WitnessIR

@[expose] public section

/-!
# A typed model of the generated Rust witness code

The Rust code generated for witness programs, row programs, and fixed columns is built as values of
this model and printed structurally. Each constructor corresponds to one Rust expression or
statement shape, and `eval`/`run` state its meaning: generic field arithmetic over
`F: WitnessField`, wrapping `u64` arithmetic, and reads that return zero when out of range.

The semantics describe the generated Rust for fields whose order is at most `2^64`, which the
backend's `WitnessField: PrimeField64` bound guarantees: `canonical` is the field element's value.
-/

namespace Backends.Plonky3.Rust

variable {F : Type}

mutual

/-- Rust expressions of the generic field type `F`. -/
inductive FieldExpr (F : Type) where
  /-- `F::from_u64(c)`, or its negation for large constants. -/
  | const (value : F)
  /-- `row.get(index).copied().unwrap_or(F::ZERO)` on the function's row slice. -/
  | cell (index : ℕ)
  /-- `row.get(offset + idx as usize).copied().unwrap_or(F::ZERO)` inside a loop. -/
  | cellAtLoop (offset : ℕ)
  /-- `local_{index}`, the result of an earlier `let`. -/
  | localVar (index : ℕ)
  | add (left right : FieldExpr F)
  | mul (left right : FieldExpr F)
  /-- `value.inverse_or_zero()`. -/
  | inverseOrZero (value : FieldExpr F)
  /-- `F::from_u64(value)`. -/
  | fromU64 (value : U64Expr F)
  /-- `if condition { thenValue } else { elseValue }`. -/
  | ite (condition : BoolExpr F) (thenValue elseValue : FieldExpr F)
  /-- `[values..].get(index as usize).copied().unwrap_or(F::ZERO)`. -/
  | arrayGet (values : List (FieldExpr F)) (index : U64Expr F)
  /-- `match index as usize { 0 => values[0], .., _ => F::ZERO }` over constants. -/
  | constMatch (values : List F) (index : U64Expr F)
  /-- `_data.get(key, width, row as usize, column)` on committed prover data. -/
  | dataGet (key : String) (width : ℕ) (row : U64Expr F) (column : ℕ)
  /-- `_hint.get(key, width, row as usize, column)` on the prover hint. -/
  | hintGet (key : String) (width : ℕ) (row : U64Expr F) (column : ℕ)

/-- Rust expressions of type `u64`. -/
inductive U64Expr (F : Type) where
  | const (value : UInt64)
  /-- `value.canonical_u64()`. -/
  | canonical (value : FieldExpr F)
  /-- `local_{index}`, the result of an earlier `let`. -/
  | localVar (index : ℕ)
  /-- `idx`, the variable of the enclosing `for` loop. -/
  | loopVar
  /-- `row`, the row index argument of a row function. -/
  | rowIndex
  | wrappingAdd (left right : U64Expr F)
  | wrappingMul (left right : U64Expr F)
  /-- `safe_div(left, right)`, which is zero when `right` is zero. -/
  | safeDiv (left right : U64Expr F)
  /-- `safe_rem(left, right)`, which is `left` when `right` is zero. -/
  | safeRem (left right : U64Expr F)
  | and (left right : U64Expr F)
  | or (left right : U64Expr F)
  | xor (left right : U64Expr F)
  /-- `left.wrapping_shl((right & 63) as u32)`. -/
  | wrappingShl (left right : U64Expr F)
  /-- `left.wrapping_shr((right & 63) as u32)`. -/
  | wrappingShr (left right : U64Expr F)
  /-- `if idx < 64 { (value >> idx) & 1 } else { 0 }`, bit `idx` of `value` inside a loop. -/
  | loopBit (value : U64Expr F)
  | ite (condition : BoolExpr F) (thenValue elseValue : U64Expr F)

/-- Rust expressions of type `bool`. -/
inductive BoolExpr (F : Type) where
  | true
  | false
  | fieldEq (left right : FieldExpr F)
  | u64Eq (left right : U64Expr F)
  | u64Lt (left right : U64Expr F)
  | not (condition : BoolExpr F)
  | and (left right : BoolExpr F)

end

/-- Statements of a generated function body, which fills a vector `output`. -/
inductive Stmt (F : Type) where
  /-- `let local_k: F = value;`, where `k` counts the earlier `let`s. -/
  | letField (value : FieldExpr F)
  /-- `let local_k: u64 = value;`, where `k` counts the earlier `let`s. -/
  | letU64 (value : U64Expr F)
  /-- `output.push(value);` -/
  | push (value : FieldExpr F)
  /-- `for idx in 0u64..count { output.push(value); }` -/
  | forPush (count : ℕ) (value : FieldExpr F)

/-- The inputs of a generated function: the row slice it reads, the row index argument, committed
prover data, and the prover hint. -/
structure Env (F : Type) where
  row : Array F
  rowIndex : UInt64
  data : ProverData F
  hint : ProverHint F

/-- Values of the `let` locals, and the `idx` variable of the enclosing loop. -/
structure Frame (F : Type) where
  locals : Array (F ⊕ UInt64)
  loopVar : ℕ

section Eval
variable [FiniteField F] (env : Env F) (frame : Frame F)

/-- Read a named table of `width`-element rows at `row` and `column`, zero when absent. -/
def tableGet (table : String → (n : ℕ) → Array (Vector F n)) (key : String) (width : ℕ)
    (row : UInt64) (column : ℕ) : F :=
  ((table key width)[row.toNat]?.bind fun values => values[column]?).getD 0

mutual

def FieldExpr.eval : FieldExpr F → F
  | .const value => value
  | .cell index => env.row[index]?.getD 0
  | .cellAtLoop offset => env.row[offset + frame.loopVar]?.getD 0
  | .localVar index =>
      match frame.locals[index]? with
      | some (.inl value) => value
      | _ => 0
  | .add left right => left.eval + right.eval
  | .mul left right => left.eval * right.eval
  | .inverseOrZero value => value.eval⁻¹
  | .fromU64 value => FiniteField.fromNat value.eval.toNat
  | .ite condition thenValue elseValue =>
      if condition.eval then thenValue.eval else elseValue.eval
  | .arrayGet values index => (FieldExpr.evalList values)[(index.eval).toNat]?.getD 0
  | .constMatch values index => values[(index.eval).toNat]?.getD 0
  | .dataGet key width row column => tableGet env.data key width row.eval column
  | .hintGet key width row column => tableGet env.hint key width row.eval column

def FieldExpr.evalList : List (FieldExpr F) → List F
  | [] => []
  | value :: values => value.eval :: FieldExpr.evalList values

def U64Expr.eval : U64Expr F → UInt64
  | .const value => value
  | .canonical value => UInt64.ofNat (FiniteField.val value.eval)
  | .localVar index =>
      match frame.locals[index]? with
      | some (.inr value) => value
      | _ => 0
  | .loopVar => UInt64.ofNat frame.loopVar
  | .rowIndex => env.rowIndex
  | .wrappingAdd left right => left.eval + right.eval
  | .wrappingMul left right => left.eval * right.eval
  | .safeDiv left right => left.eval / right.eval
  | .safeRem left right => left.eval % right.eval
  | .and left right => left.eval &&& right.eval
  | .or left right => left.eval ||| right.eval
  | .xor left right => left.eval ^^^ right.eval
  | .wrappingShl left right => left.eval <<< right.eval
  | .wrappingShr left right => left.eval >>> right.eval
  | .loopBit value =>
      if frame.loopVar < 64 then (value.eval >>> UInt64.ofNat frame.loopVar) &&& 1 else 0
  | .ite condition thenValue elseValue =>
      if condition.eval then thenValue.eval else elseValue.eval

def BoolExpr.eval : BoolExpr F → Bool
  | .true => true
  | .false => false
  | .fieldEq left right => decide (left.eval = right.eval)
  | .u64Eq left right => decide (left.eval = right.eval)
  | .u64Lt left right => decide (left.eval < right.eval)
  | .not condition => !condition.eval
  | .and left right => left.eval && right.eval

end

end Eval

/-- The locals and output vector built by a function body. -/
structure State (F : Type) where
  locals : Array (F ⊕ UInt64)
  output : Array F

/-- Execute one statement. -/
def Stmt.run [FiniteField F] (env : Env F) (state : State F) : Stmt F → State F
  | .letField value =>
      { state with locals := state.locals.push (.inl (value.eval env ⟨state.locals, 0⟩)) }
  | .letU64 value =>
      { state with locals := state.locals.push (.inr (value.eval env ⟨state.locals, 0⟩)) }
  | .push value =>
      { state with output := state.output.push (value.eval env ⟨state.locals, 0⟩) }
  | .forPush count value =>
      { state with output := state.output ++ (List.range count).toArray.map fun index =>
          value.eval env ⟨state.locals, index⟩ }

/-- Execute a function body from no locals and an empty output. -/
def run [FiniteField F] (env : Env F) (body : List (Stmt F)) : State F :=
  body.foldl (Stmt.run env) { locals := #[], output := #[] }

end Backends.Plonky3.Rust
