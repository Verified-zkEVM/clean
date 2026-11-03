module

public import Clean.Circuit.WitnessIRSugar

@[expose] public section

/-!
# Row programs

Witness programs that compute the input of a row from the row index: the inputs of preallocated
components. Their fixed cells are computed from the index alone; their witness cells can also read
the hint.
-/

namespace Witgen
variable {F : Type}

/-- What a row program computes: fixed cells, or witness cells of preallocated components. -/
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

def Step.validForRow (source : RowProgram.Source) : Step F → Bool
  | .letF value => value.validForRow source
  | .letU value => value.validForRow source

/-- Evaluate a fixed row program at row `row`, which `.idx` reads. -/
@[circuit_norm]
def M.evalRow [FiniteField F] {Row : TypeMap} [ProvableType Row]
    (program : M F (Row (FExpr F))) (row : UInt64) : Row F :=
  let env : ProverEnvironment F := { get _ := 0, data := .empty F, hint := .empty F }
  Witgen.eval {
    env
    locals := evalSteps env (program #[]).2.toList #[] row.toNat
    idx := row.toNat
  } (program #[]).1

end Witgen
