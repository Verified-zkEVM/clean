module

public import Clean.Backends.Program

@[expose] public section

/-!
# Rust printer for extraction programs

Prints a validated `Backends.Program` as Rust for the `clean_backend` crate, one constructor at a
time. Each component becomes a Rust module with the same items: its shape, its witness and
fixed-column programs, and its constraints and interactions. A final `clean_backend::ensemble!`
invocation lists the modules; the macro implements the crate's traits on top of them, so dispatch,
width checks, and Plonky3 plumbing are written once in Rust.

Constraints and interactions are printed as functions generic over a Rust ring type `E`, reading a
complete row whose fixed columns come first. The crate instantiates them with field elements for
witness generation and with symbolic Plonky3 expressions for the AIR. Witness programs are printed
over field elements, reading the partially built row.
-/

namespace Backends.Plonky3.Print

open Air.Flat
open Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Order of the field the generated code is printed for. Generated programs and AIRs reject any
  other Rust field. -/
def fieldOrder : ℕ := FiniteField.size (F := F)

/-- A field constant in the Rust ring type `ty`. Values above half the field order are printed as
  negations, so that e.g. `-1` reads as `-ty::from_u64(1u64)`. -/
def fieldIn (ty : String) (value : F) : String :=
  let value := FiniteField.val value
  if 2 * value > fieldOrder (F := F) then s!"-{ty}::from_u64({fieldOrder (F := F) - value}u64)"
  else s!"{ty}::from_u64({value}u64)"

def quoted (value : String) : String := reprStr value

def commaSep (values : List String) : String :=
  String.intercalate ", " values

def lines (values : List String) : String :=
  String.intercalate "\n" values

/-! ## Constraints and interactions, generic over the ring type `E` -/

def exprToRust : Expression F → String
  | .var cell => s!"row[{cell.index}].clone()"
  | .const value => fieldIn "E" value
  | .add left right => s!"({exprToRust left} + {exprToRust right})"
  | .mul left right => s!"({exprToRust left} * {exprToRust right})"

def interactionToRust (interaction : AbstractInteraction F) : String :=
  let message := commaSep (interaction.msg.toList.map exprToRust)
  s!"Interaction \{ channel: {quoted interaction.channel.name}, multiplicity: \
      {exprToRust interaction.mult}, message: vec![{message}], \
      assume_guarantees: {interaction.assumeGuarantees} }"

/-- `fn constraints<E>(row: &[E]) -> Vec<E>` -/
def constraintsToRust (constraints : List (Expression F)) : String :=
  s!"pub fn constraints<E: PrimeCharacteristicRing + Clone>(row: &[E]) -> Vec<E> \{
    vec![{commaSep (constraints.map exprToRust)}]
}"

/-- `fn interactions<E>(row: &[E]) -> Vec<Interaction<E>>` -/
def interactionsToRust (interactions : List (AbstractInteraction F)) : String :=
  s!"pub const INTERACTIONS: usize = {interactions.length};

pub fn interactions<E: PrimeCharacteristicRing + Clone>(row: &[E]) -> Vec<Interaction<E>> \{
    vec![{commaSep (interactions.map interactionToRust)}]
}"

/-! ## Witness IR, over field elements

Printed function bodies read the row slice `row`, the row index `row_index`, the prover data `data`,
and the hint `hint`. Inside loops, `idx` is the loop index. `inLoop` records whether `.idx` is the
loop index or the row index. -/

mutual

def fexprToRust (inLoop : Bool) : Witgen.FExpr F → String
  | .expr e => witnessExprToRust e
  | .const value => fieldIn "F" value
  | .localVar index => s!"local_{index}"
  | .add left right => s!"({fexprToRust inLoop left} + {fexprToRust inLoop right})"
  | .mul left right => s!"({fexprToRust inLoop left} * {fexprToRust inLoop right})"
  | .inv value => s!"({fexprToRust inLoop value}).inverse_or_zero()"
  | .ofU64 value => s!"F::from_u64({u64exprToRust inLoop value})"
  | .ite condition thenValue elseValue =>
      s!"if {bexprToRust inLoop condition} \{ {fexprToRust inLoop thenValue} } else \{ \
          {fexprToRust inLoop elseValue} }"
  | .listGet values index =>
      s!"[{commaSep (fexprListToRust inLoop values)}].get(({u64exprToRust inLoop index}) as \
          usize).copied().unwrap_or(F::ZERO)"
  | .dataGet key width row column =>
      s!"data.get({quoted key}, {width}, ({u64exprToRust inLoop row}) as usize, {column})"
  | .hintGet key width row column =>
      s!"hint.get({quoted key}, {width}, ({u64exprToRust inLoop row}) as usize, {column})"

def fexprListToRust (inLoop : Bool) : List (Witgen.FExpr F) → List String
  | [] => []
  | value :: values => fexprToRust inLoop value :: fexprListToRust inLoop values

def u64exprToRust (inLoop : Bool) : Witgen.U64Expr F → String
  | .const value => s!"{value.toNat}u64"
  | .val value => s!"({fexprToRust inLoop value}).canonical_u64()"
  | .idx => if inLoop then "idx" else "row_index"
  | .localVar index => s!"local_{index}"
  | .add left right => s!"({u64exprToRust inLoop left}).wrapping_add({u64exprToRust inLoop right})"
  | .mul left right => s!"({u64exprToRust inLoop left}).wrapping_mul({u64exprToRust inLoop right})"
  | .div left right => s!"safe_div({u64exprToRust inLoop left}, {u64exprToRust inLoop right})"
  | .mod left right => s!"safe_rem({u64exprToRust inLoop left}, {u64exprToRust inLoop right})"
  | .land left right => s!"({u64exprToRust inLoop left} & {u64exprToRust inLoop right})"
  | .lor left right => s!"({u64exprToRust inLoop left} | {u64exprToRust inLoop right})"
  | .lxor left right => s!"({u64exprToRust inLoop left} ^ {u64exprToRust inLoop right})"
  | .shiftL left right => s!"shift_left({u64exprToRust inLoop left}, {u64exprToRust inLoop right})"
  | .shiftR left right => s!"shift_right({u64exprToRust inLoop left}, {u64exprToRust inLoop right})"
  | .ite condition thenValue elseValue =>
      s!"if {bexprToRust inLoop condition} \{ {u64exprToRust inLoop thenValue} } else \{ \
          {u64exprToRust inLoop elseValue} }"

def bexprToRust (inLoop : Bool) : Witgen.BExpr F → String
  | .true => "true"
  | .false => "false"
  | .feq left right => s!"({fexprToRust inLoop left} == {fexprToRust inLoop right})"
  | .neq left right => s!"({u64exprToRust inLoop left} == {u64exprToRust inLoop right})"
  | .lt left right => s!"({u64exprToRust inLoop left} < {u64exprToRust inLoop right})"
  | .flt left right =>
      s!"(({fexprToRust inLoop left}).canonical_u64() < \
          ({fexprToRust inLoop right}).canonical_u64())"
  | .bit value index => s!"bit(({fexprToRust inLoop value}).canonical_u64(), {min index 64})"
  | .not condition => s!"!({bexprToRust inLoop condition})"
  | .and left right => s!"({bexprToRust inLoop left} && {bexprToRust inLoop right})"

/-- A circuit expression read from the partially built row. -/
def witnessExprToRust : Expression F → String
  | .var cell => s!"row.get({cell.index}).copied().unwrap_or(F::ZERO)"
  | .const value => fieldIn "F" value
  | .add left right => s!"({witnessExprToRust left} + {witnessExprToRust right})"
  | .mul left right => s!"({witnessExprToRust left} * {witnessExprToRust right})"

end

/-- `let` statements for witness IR steps, numbering locals in order. -/
def stepsToRust (lets : ℕ) : List (Witgen.Step F) → List String
  | [] => []
  | .letF value :: steps => s!"let local_{lets}: F = {fexprToRust false value};" :: stepsToRust
      (lets + 1) steps
  | .letU value :: steps => s!"let local_{lets}: u64 = {u64exprToRust false value};" ::
      stepsToRust (lets + 1) steps

/-- Statements pushing a witness IR output vector to `output`. -/
def outputToRust : {n : ℕ} → Witgen.VExpr F n → List String
  | _, .lit values => values.toList.map fun value => s!"output.push({fexprToRust false value});"
  | _, .mapRange count body => [s!"for idx in 0u64..{count}u64 \{ \
      output.push({fexprToRust true body}); }"]
  | count, .envRange offset =>
      [s!"for idx in 0u64..{count}u64 \{ output.push(row.get({offset} + idx as \
          usize).copied().unwrap_or(F::ZERO)); }"]
  | count, .bitsOf value =>
      [s!"for idx in 0u64..{count}u64 \{ \
          output.push(F::from_u64(bit_u64(({fexprToRust false value}).canonical_u64(), idx))); }"]
  | _, .append left right => outputToRust left ++ outputToRust right

/-- A block computing a witness IR program into a fresh vector `output`. -/
def programToRust {n : ℕ} (steps : List (Witgen.Step F)) (output : Witgen.VExpr F n) : String :=
  lines (["let mut output: Vec<F> = Vec::with_capacity(" ++ toString n ++ ");"] ++
    stepsToRust 0 steps ++ outputToRust output)

/-! ## Components -/

/-- `fn fixed_row(row_index) -> Vec<F>` -/
def fixedRowToRust : Option (FixedColumnsProgram F) → String
  | none => "pub const FIXED_WIDTH: usize = 0;
pub const FIXED_HEIGHT: usize = 0;

pub fn fixed_row<F: WitnessField>(_row_index: u64) -> Vec<F> {
    Vec::new()
}"
  | some fixed => s!"pub const FIXED_WIDTH: usize = {fixed.width};
pub const FIXED_HEIGHT: usize = {fixed.height};

pub fn fixed_row<F: WitnessField>(row_index: u64) -> Vec<F> \{
    let row: &[F] = &[];
    {programToRust fixed.program.steps fixed.program.output}
    output
}"

/-- `fn complete(row, data, hint)`, appending the witnesses to the row's input. -/
def completeToRust (witnesses : List (WitnessBlock F)) : String :=
  let blocks := witnesses.map fun block =>
    s!"    \{\n{programToRust block.steps block.output}\n    row.extend(output);\n    }"
  s!"pub fn complete<F: WitnessField>(row: &mut Vec<F>, data: &WitnessData<F>, hint: \
      &WitnessData<F>) \{
    let row_index = 0u64;
{lines blocks}
}"

def inputCellToRust : InputCell F → String
  | .message index => s!"InputCell::Message({index})"
  | .multiplicity => "InputCell::Multiplicity"
  | .const value => s!"InputCell::Constant({fieldIn "F" value})"

def directionToRust : Direction → String
  | .pull => "Direction::Pull"
  | .push => "Direction::Push"

def aggregationToRust : Aggregation → String
  | .perOccurrence => "Aggregation::PerOccurrence"
  | .byMessage => "Aggregation::ByMessage"

def handlerToRust (handler : HandlerProgram) : String :=
  s!"PreallocatedHandler \{ channel: {quoted handler.channel}, direction: \
      {directionToRust handler.direction}, interaction: {handler.interaction}, column:
      {handler.column} }"

/-- `fn mode()`, and `fn initial_row(row_index, hint)`, which for preallocated components is the
  fixed prefix followed by the row program's values. -/
def modeToRust : ModeProgram F → String
  | .demand mode => s!"pub fn mode<F: WitnessField>() -> Mode<F> \{
    Mode::Demand(DemandMode \{ channel: {quoted mode.channel.name}, direction: \
        {directionToRust mode.direction}, aggregation: {aggregationToRust mode.aggregation}, \
        input: vec![{commaSep (mode.input.cells.map inputCellToRust)}] })
}

pub fn initial_row<F: WitnessField>(_row_index: u64, _hint: &WitnessData<F>) -> Vec<F> \{
    Vec::new()
}"
  | .preallocated rows input handlers => s!"pub fn mode<F: WitnessField>() -> Mode<F> \{
    Mode::Preallocated \{ rows: {rows}, handlers: vec![{commaSep (handlers.map handlerToRust)}] }
}

pub fn initial_row<F: WitnessField>(row_index: u64, hint: &WitnessData<F>) -> Vec<F> \{
    let row: &[F] = &[];
    let mut input = fixed_row::<F>(row_index);
    {programToRust input.steps input.output}
    input.extend(output);
    input
}"

def paddingToRust (padding : Padding F) : String :=
  s!"pub fn padding<F: WitnessField>() -> Padding<F> \{
    Padding \{ input: vec![{commaSep (padding.input.toList.map (fieldIn "F"))}], minimum_rows: \
        {padding.minimumRows} }
}"

def componentToRust (index : ℕ) (component : ComponentProgram F) (mode : ModeProgram F)
    (padding : Padding F) : String :=
  s!"#[allow(unused_variables, unused_mut, unused_parens)]
pub mod component_{index} \{
use super::*;

pub const NAME: &str = {quoted component.name};
pub const INPUT_WIDTH: usize = {component.inputWidth};
pub const WIDTH: usize = {component.width};

{fixedRowToRust component.fixedColumns}

{completeToRust component.witnesses}

{constraintsToRust component.constraints}

{interactionsToRust component.interactions}

{modeToRust mode}

{paddingToRust padding}
}"

def hintTableToRust (table : HintTable) : String :=
  s!"HintTable \{ key: {quoted table.key}, width: {table.width}, offset: {table.offset}, rows: \
      {table.rows} }"

def prelude : String := "// Generated by Clean from an extraction program. Do not edit.
use clean_backend::witness_generation::*;
use p3_field::PrimeCharacteristicRing;
use alloc::{vec, vec::Vec};
"

/-- Print a validated extraction program as a Rust module body. -/
def programToRustFile (program : Program F) : String :=
  let components := ((program.components.zip (program.modes.zip program.padding)).zipIdx.map
    fun ((component, mode, padding), index) => componentToRust index component mode padding)
  let names := commaSep (program.components.zipIdx.map fun (_, index) => s!"component_{index}")
  s!"{prelude}
{lines (components.map (· ++ "\n"))}
#[allow(unused_variables, unused_parens)]
pub mod verifier \{
use super::*;

{interactionsToRust program.verifierInteractions}
}

clean_backend::ensemble! \{
    field_order: {fieldOrder (F := F)},
    fuel: {program.fuel},
    public_inputs: {program.publicInputWidth},
    prover_inputs: {program.proverInputWidth},
    hint_tables: [{commaSep (program.hintTables.map hintTableToRust)}],
    components: [{names}],
}
"

/-- Lower an ensemble to an extraction program and print it as Rust. -/
def ensembleToRust (ens : FormalEnsemble F PublicIO) (config : Config F) : Except String String :=
    do
  let program ← lower ens config |>.mapError toString
  return programToRustFile program

end Backends.Plonky3.Print
