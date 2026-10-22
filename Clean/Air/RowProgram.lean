module

public import Clean.Circuit.WitnessIRSugar

@[expose] public section

/-!
# Row programs

Witness programs that compute a segment of a row from the row index: fixed columns, and the inputs
of preallocated components. The latter can also read the hint.
-/

namespace Witgen
variable {F : Type}

/-- What a row program computes: fixed columns, or inputs of preallocated components. -/
inductive RowProgram.Source where
  | fixed
  | prover
deriving DecidableEq

@[circuit_norm]
def RowProgram.Source.allowsHints : RowProgram.Source → Bool
  | .fixed => false
  | .prover => true

mutual

/-- Whether an expression is valid in a row program: it reads no row or prover data, and only
prover row programs read hints. -/
def FExpr.validForRow (source : RowProgram.Source) : FExpr F → Bool
  | .expr _ => false
  | .const _ | .localVar _ => true
  | .add left right | .mul left right =>
      left.validForRow source && right.validForRow source
  | .inv value => value.validForRow source
  | .ofU64 value => value.validForRow source
  | .ite condition thenValue elseValue =>
      condition.validForRow source &&
        thenValue.validForRow source && elseValue.validForRow source
  | .listGet values index =>
      FExprList.validForRow source values && index.validForRow source
  | .dataGet .. => false
  | .hintGet _ _ row _ => source.allowsHints && row.validForRow source

def U64Expr.validForRow (source : RowProgram.Source) : U64Expr F → Bool
  | .const _ | .idx | .localVar _ => true
  | .val value => value.validForRow source
  | .add left right | .mul left right | .div left right | .mod left right |
      .land left right | .lor left right | .lxor left right |
      .shiftL left right | .shiftR left right =>
        left.validForRow source && right.validForRow source
  | .ite condition thenValue elseValue =>
      condition.validForRow source &&
        thenValue.validForRow source && elseValue.validForRow source

def BExpr.validForRow (source : RowProgram.Source) : BExpr F → Bool
  | .true | .false => true
  | .feq left right | .flt left right =>
      left.validForRow source && right.validForRow source
  | .neq left right | .lt left right =>
      left.validForRow source && right.validForRow source
  | .bit value _ => value.validForRow source
  | .not condition => condition.validForRow source
  | .and left right =>
      left.validForRow source && right.validForRow source

def FExprList.validForRow (source : RowProgram.Source) : List (FExpr F) → Bool
  | [] => true
  | value :: values =>
      value.validForRow source && FExprList.validForRow source values

end

@[simp]
theorem FExprList.validForRow_map_const (source : RowProgram.Source) (values : List F) :
    FExprList.validForRow source (values.map FExpr.const) = true := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [FExprList.validForRow, FExpr.validForRow, ih]

def Step.validForRow (source : RowProgram.Source) : Step F → Bool
  | .letF value => value.validForRow source
  | .letU value => value.validForRow source

def VExpr.validForRow (source : RowProgram.Source) : {n : ℕ} → VExpr F n → Bool
  | _, .lit values => values.toList.all (FExpr.validForRow source)
  | _, .mapRange _ body => body.validForRow source
  | _, .envRange _ => false
  | _, .bitsOf value => value.validForRow source
  | _, .append left right =>
      left.validForRow source && right.validForRow source

attribute [circuit_norm] FExpr.validForRow U64Expr.validForRow BExpr.validForRow
  FExprList.validForRow Step.validForRow VExpr.validForRow

/-- Whether a witness program is valid in a row program. -/
@[circuit_norm]
def M.ValidForRow {Row : TypeMap} [ProvableType Row] (program : M F (Row (FExpr F)))
    (source : RowProgram.Source) : Prop :=
  ((program #[]).2.toList.all (Step.validForRow source) &&
    (VExpr.lit (toElements (program #[]).1)).validForRow source) = true

/-- Evaluate a witness program at row `row`, which `.idx` reads. Only prover row programs read
`hint`. -/
@[circuit_norm]
def M.evalRow [FiniteField F] {Row : TypeMap} [ProvableType Row]
    (program : M F (Row (FExpr F))) (row : UInt64) (hint : ProverHint F := .empty F) : Row F :=
  let env : ProverEnvironment F := { get _ := 0, data := .empty F, hint }
  Witgen.eval {
    env
    locals := evalSteps env (program #[]).2.toList #[] row.toNat
    idx := row.toNat
  } (program #[]).1

/-- A program computing a row segment of type `Row` from the row index. -/
structure RowProgram (F : Type) (source : RowProgram.Source) where
  {Row : TypeMap} [provableRow : ProvableType Row]
  /-- The values of row `i`. -/
  row (i : U64Expr F) : M F (Row (FExpr F))
  valid : (row .idx).ValidForRow source := by simp [circuit_norm]

instance {source : RowProgram.Source} (program : RowProgram F source) :
    ProvableType program.Row :=
  program.provableRow

namespace RowProgram
variable {source : Source}

abbrev width (program : RowProgram F source) : ℕ := size program.Row

/-- The program as witness IR. -/
def ir (program : RowProgram F source) : WitgenIR F program.width :=
  (program.row .idx).toIRLiteral

/-- The values of row `i`. -/
@[circuit_norm]
def eval [FiniteField F] (program : RowProgram F source) (i : UInt64)
    (hint : ProverHint F := .empty F) : program.Row F :=
  (program.row .idx).evalRow i hint

end RowProgram

end Witgen
