module

public import Clean.Circuit.WitnessIRSugar

@[expose] public section

/-!
# Row programs

Index-aware witness programs that produce one segment of an AIR row: verifier-known fixed columns,
and prover-committed inputs of preallocated components. They read the row index and, for prover
inputs, the runtime prover input, but no circuit environment.
-/

namespace Witgen
variable {F : Type}

/-- A structured, index-aware program producing one row segment. Unlike `WitgenIR`, this has no
native-closure escape hatch and can therefore be interpreted identically by Lean and extracted
backends. -/
structure RowProgram (F : Type) where
  width : ℕ
  steps : List (Step F)
  output : VExpr F width

namespace RowProgram

/-- Evaluate a row program at `row`, which `U64Expr.idx` reads. Prover row programs may read `hint`;
fixed-column programs cannot. -/
def eval [FiniteField F] (program : RowProgram F) (row : UInt64) (hint : ProverHint F) :
    Vector F program.width :=
  let env : ProverEnvironment F := {
    get := fun _ => 0
    data := fun _ _ => #[]
    hint
  }
  program.output.eval {
    env
    locals := evalSteps env program.steps #[] row.toNat
    idx := row.toNat
  }

def empty (F : Type) : RowProgram F where
  width := 0
  steps := []
  output := .lit #v[]

def ofFExprs {n : ℕ} (values : Vector (FExpr F) n) : RowProgram F where
  width := n
  steps := []
  output := .lit values

/-- The row program computing a provable value with a witness program. -/
@[circuit_norm]
def ofM {Row : TypeMap} [ProvableType Row] (program : M F (Row (FExpr F))) : RowProgram F where
  width := size Row
  steps := (program #[]).2.toList
  output := .lit (toElements (program #[]).1)

/-- The empty environment of fixed rows, which read nothing but the row index. -/
@[circuit_norm]
def fixedEnvironment (F : Type) [Field F] : ProverEnvironment F where
  get _ := 0
  data _ _ := #[]
  hint := .empty F

/-- Evaluate a witness program for a fixed row at row `row`. -/
@[circuit_norm]
def _root_.Witgen.M.evalRow [FiniteField F] {Row : TypeMap} [ProvableType Row]
    (program : M F (Row (FExpr F))) (row : UInt64) : Row F :=
  Witgen.eval {
    env := fixedEnvironment F
    locals := evalSteps (fixedEnvironment F) (program #[]).2.toList #[] row.toNat
    idx := row.toNat
  } (program #[]).1

theorem eval_ofM [FiniteField F] {Row : TypeMap} [ProvableType Row] (program : M F (Row (FExpr F)))
    (row : UInt64) : (ofM program).eval row (.empty F) = toElements (program.evalRow row) := by
  simp only [eval, ofM, M.evalRow, fixedEnvironment, Witgen.eval, VExpr.eval,
    ProvableType.toElements_fromElements]

end RowProgram

/-- External inputs available to an index-aware row program. -/
inductive RowProgram.Source where
  | fixed
  | prover
deriving DecidableEq

def RowProgram.Source.allowsHints : RowProgram.Source → Bool
  | .fixed => false
  | .prover => true

mutual

/-- Whether an expression is valid in a row program. These programs have no circuit-row or
semantic-data environment. Prover row programs additionally read hints; fixed programs do not. -/
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

namespace RowProgram

@[circuit_norm]
def Valid (program : RowProgram F) (source : Source) : Prop :=
  program.steps.all (Step.validForRow source) &&
    program.output.validForRow source = true

end RowProgram

end Witgen
