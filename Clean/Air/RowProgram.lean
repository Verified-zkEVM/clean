module

public import Clean.Circuit.WitnessIRSugar

@[expose] public section

/-!
# Row programs

Witness programs that compute the input of a row from the row index: the inputs of preallocated
components. Their fixed cells are computed from the index alone; their witness cells can also read
the hint.

Segment programs compute the inputs of a component's rows in segments of consecutive rows: the first
row of a segment like a row program, every other row also from the previous row's values, which
carry the segment's state. For example, the 24 rows of a Keccak-f permutation: the first row reads
the permutation's input from the hint, every later row continues from the state of the row before.
-/

namespace Witgen
variable {F : Type}

/-- What a row program computes: fixed cells, witness cells of preallocated components, or the
inputs of the rows of a segment after its first, which read the previous row's first `width`
cells. -/
inductive RowProgram.Source where
  | fixed
  | prover
  | continuation (width : ℕ)
deriving DecidableEq

@[circuit_norm]
def RowProgram.Source.allowsHints : RowProgram.Source → Bool
  | .fixed => false
  | .prover | .continuation _ => true

/-- Whether an expression reads only cells below `width`. -/
def _root_.Expression.readsBelow (width : ℕ) : Expression F → Bool
  | .var cell => cell.index < width
  | .const _ => true
  | .add left right | .mul left right => left.readsBelow width && right.readsBelow width

/-- Which circuit expressions a row program reads: those of the previous row in a continuation, and
none otherwise. -/
@[circuit_norm]
def RowProgram.Source.allowsRead (source : RowProgram.Source) (e : Expression F) : Bool :=
  match source with
  | .fixed | .prover => false
  | .continuation width => e.readsBelow width

mutual

/-- Whether an expression is valid in a row program: it reads no prover data, only prover row
programs and continuations read hints, and only continuations read cells, of the previous row. -/
def FExpr.validForRow (source : RowProgram.Source) : FExpr F → Bool
  | .expr e => source.allowsRead e
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
  let env : ProverEnvironment F := { get _ := 0, data _ _ := #[], hint := .empty F }
  Witgen.eval {
    env
    locals := evalSteps env (program #[]).2.toList #[] row.toNat
    idx := row.toNat
  } (program #[]).1

/-- Whether a witness program is valid in a row program. -/
def M.ValidForRow {Row : TypeMap} [ProvableType Row] (program : M F (Row (FExpr F)))
    (source : RowProgram.Source) : Prop :=
  ((program #[]).2.toList.all (Step.validForRow source) &&
    (toElements (program #[]).1).toList.all (FExpr.validForRow source)) = true

/-- Evaluate a witness program at row `row` after a row with the values `previous`, which `.expr`
reads, with the hint `hint`. -/
def M.evalRowAfter [FiniteField F] {Row : TypeMap} [ProvableType Row]
    (program : M F (Row (FExpr F))) (previous : Array F) (row : UInt64) (hint : ProverHint F) :
    Row F :=
  let env : ProverEnvironment F := { get j := previous[j]?.getD 0, data _ _ := #[], hint }
  Witgen.eval {
    env
    locals := evalSteps env (program #[]).2.toList #[] row.toNat
    idx := row.toNat
  } (program #[]).1

/-- A program computing rows of type `Row` in segments of `length` consecutive rows. Row `i` starts
a segment if `i % length = 0`, so with `length = 0` only row 0 does. A row that starts a segment is
computed from its index, like a row program; every other row from its index and the previous row's
values, which carry the segment's state. -/
structure SegmentProgram (F : Type) where
  {Row : TypeMap} [provableRow : ProvableType Row]
  length : ℕ
  /-- The values of row `i`, which starts a segment. -/
  first (i : U64Expr F) : M F (Row (FExpr F))
  /-- The values of row `i`, which continues the segment of the row `previous`. -/
  next (i : U64Expr F) (previous : Row (Expression F)) : M F (Row (FExpr F))

instance (program : SegmentProgram F) : ProvableType program.Row := program.provableRow

namespace SegmentProgram

abbrev width (program : SegmentProgram F) : ℕ := size program.Row

/-- The program of rows that start a segment. -/
def firstProgram (program : SegmentProgram F) : M F (program.Row (FExpr F)) := program.first .idx

/-- The program of the other rows, which reads the previous row's cells. -/
def nextProgram (program : SegmentProgram F) : M F (program.Row (FExpr F)) :=
  program.next .idx (varFromOffset program.Row 0)

/-- Whether a row starts a segment. -/
def StartsSegment (program : SegmentProgram F) (row : UInt64) : Prop :=
  row.toNat % program.length = 0

instance (program : SegmentProgram F) (row : UInt64) : Decidable (program.StartsSegment row) :=
  inferInstanceAs (Decidable (_ = _))

/-- Whether the program reads no prover data, and reads only the previous row's cells after the
first row of a segment. -/
def Valid (program : SegmentProgram F) : Prop :=
  program.firstProgram.ValidForRow .prover ∧
    program.nextProgram.ValidForRow (.continuation program.width)

instance (program : SegmentProgram F) : Decidable program.Valid := by
  unfold Valid M.ValidForRow
  infer_instance

variable [FiniteField F]

/-- The values of row `i` after a row with the values `previous`. A row that starts a segment reads
no cells, so it is evaluated after no row. -/
def evalRow (program : SegmentProgram F) (i : UInt64) (previous : program.Row F)
    (hint : ProverHint F) : program.Row F :=
  if program.StartsSegment i then program.firstProgram.evalRowAfter #[] i hint
  else program.nextProgram.evalRowAfter (toElements previous).toArray i hint

/-- The values of the rows `0, …, count - 1`. -/
def rows (program : SegmentProgram F) (count : ℕ) (hint : ProverHint F) : List (program.Row F) :=
  let step (state : Array (program.Row F) × program.Row F) (i : ℕ) :=
    let row := program.evalRow (UInt64.ofNat i) state.2 hint
    (state.1.push row, row)
  ((List.range count).foldl step (#[], fromElements (Vector.replicate _ 0))).1.toList

end SegmentProgram

end Witgen
