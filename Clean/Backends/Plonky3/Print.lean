module

public import Clean.Backends.Plonky3.Lower
public import Clean.Backends.Plonky3.Codegen

@[expose] public section

/-!
# Rust rendering for typed AIR extraction programs

This is the only string-producing part of ensemble extraction. It consumes a validated
`Backends.Plonky3.Program`; lowering, validation, and executable semantics live in `Program.lean` and
`Lower.lean`. Generic Plonky3 `Air` plumbing lives in the Rust backend.
-/

namespace Backends.Plonky3.Print

open Air.Flat
open Air.Flat.WitnessGeneration
open Backends.Plonky3

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Order of the field the generated code is printed for. Generated programs and AIRs reject
any other Rust field. -/
def fieldOrder : ℕ := FiniteField.size (F := F)

/-- A field constant in the Rust field type `ty`. Values above half the field order are printed as
negations, so that e.g. `-1` reads as `-ty::from_u64(1u64)`. -/
def fieldIn (ty : String) (value : F) : String :=
  let value := FiniteField.val value
  if 2 * value > fieldOrder (F := F) then s!"-{ty}::from_u64({fieldOrder (F := F) - value}u64)"
  else s!"{ty}::from_u64({value}u64)"

def field (value : F) : String := fieldIn "F" value

def quoted (value : String) : String := reprStr value

def commaSep (values : List String) : String :=
  String.intercalate ", " values

def constantLookupToRust (index : String) (values : List F) : String :=
  let cases := values.zipIdx.map fun (value, i) => s!"{i} => {field value}, "
  s!"match ({index}) as usize \{ {String.join cases}_ => F::ZERO }"

def exprToRust (row : String) : Expression F → String
  | .var cell => s!"{row}.get({cell.index}).copied().unwrap_or(F::ZERO)"
  | .const value => field value
  | .add left right => s!"({exprToRust row left} + {exprToRust row right})"
  | .mul left right => s!"({exprToRust row left} * {exprToRust row right})"

/-- Names of the Rust variables a function body reads: the row slice and the row index. -/
structure Names where
  row : String
  rowIndex : String

mutual

def fieldToRust (names : Names) : Rust.FieldExpr F → String
  | .const value => field value
  | .cell index => s!"{names.row}.get({index}).copied().unwrap_or(F::ZERO)"
  | .cellAtLoop offset =>
      s!"{names.row}.get({offset}usize + idx as usize).copied().unwrap_or(F::ZERO)"
  | .localVar index => s!"local_{index}"
  | .add left right => s!"({fieldToRust names left} + {fieldToRust names right})"
  | .mul left right => s!"({fieldToRust names left} * {fieldToRust names right})"
  | .inverseOrZero value => s!"({fieldToRust names value}).inverse_or_zero()"
  | .fromU64 value => s!"F::from_u64({u64ToRust names value})"
  | .ite condition thenValue elseValue =>
      s!"if {boolToRust names condition} \{ {fieldToRust names thenValue} } else \{ {fieldToRust names elseValue} }"
  | .arrayGet values index =>
      s!"[{commaSep (fieldListToRust names values)}].get(({u64ToRust names index}) as usize).copied().unwrap_or(F::ZERO)"
  | .constMatch values index => constantLookupToRust (u64ToRust names index) values
  | .dataGet key width row column =>
      s!"_data.get({quoted key}, {width}, ({u64ToRust names row}) as usize, {column})"
  | .hintGet key width row column =>
      s!"_hint.get({quoted key}, {width}, ({u64ToRust names row}) as usize, {column})"

def fieldListToRust (names : Names) : List (Rust.FieldExpr F) → List String
  | [] => []
  | value :: values => fieldToRust names value :: fieldListToRust names values

def u64ToRust (names : Names) : Rust.U64Expr F → String
  | .const value => s!"{value.toNat}u64"
  | .canonical value => s!"({fieldToRust names value}).canonical_u64()"
  | .localVar index => s!"local_{index}"
  | .loopVar => "idx"
  | .rowIndex => names.rowIndex
  | .wrappingAdd left right => s!"({u64ToRust names left}).wrapping_add({u64ToRust names right})"
  | .wrappingMul left right => s!"({u64ToRust names left}).wrapping_mul({u64ToRust names right})"
  | .safeDiv left right => s!"safe_div({u64ToRust names left}, {u64ToRust names right})"
  | .safeRem left right => s!"safe_rem({u64ToRust names left}, {u64ToRust names right})"
  | .and left right => s!"({u64ToRust names left} & {u64ToRust names right})"
  | .or left right => s!"({u64ToRust names left} | {u64ToRust names right})"
  | .xor left right => s!"({u64ToRust names left} ^ {u64ToRust names right})"
  | .wrappingShl left right =>
      s!"({u64ToRust names left}).wrapping_shl(({u64ToRust names right} & 63) as u32)"
  | .wrappingShr left right =>
      s!"({u64ToRust names left}).wrapping_shr(({u64ToRust names right} & 63) as u32)"
  | .loopBit value =>
      s!"(if idx < 64 \{ ({u64ToRust names value} >> idx) & 1 } else \{ 0 })"
  | .ite condition thenValue elseValue =>
      s!"if {boolToRust names condition} \{ {u64ToRust names thenValue} } else \{ {u64ToRust names elseValue} }"

def boolToRust (names : Names) : Rust.BoolExpr F → String
  | .true => "true"
  | .false => "false"
  | .fieldEq left right => s!"({fieldToRust names left} == {fieldToRust names right})"
  | .u64Eq left right => s!"({u64ToRust names left} == {u64ToRust names right})"
  | .u64Lt left right => s!"({u64ToRust names left} < {u64ToRust names right})"
  | .not condition => s!"!({boolToRust names condition})"
  | .and left right => s!"({boolToRust names left} && {boolToRust names right})"

end

/-- Print statements, numbering `let` locals in order. -/
def stmtsToRust (names : Names) (lets : ℕ) : List (Rust.Stmt F) → List String
  | [] => []
  | .letField value :: rest =>
      s!"        let local_{lets}: F = {fieldToRust names value};" :: stmtsToRust names (lets + 1) rest
  | .letU64 value :: rest =>
      s!"        let local_{lets}: u64 = {u64ToRust names value};" :: stmtsToRust names (lets + 1) rest
  | .push value :: rest =>
      s!"        output.push({fieldToRust names value});" :: stmtsToRust names lets rest
  | .forPush count value :: rest =>
      s!"        for idx in 0u64..{count}u64 \{\n            output.push({fieldToRust names value});\n        }" ::
        stmtsToRust names lets rest

/-- Print the Rust function body of a witness IR program, filling a vector `output` of `width`
elements. -/
def outputToRust {n : ℕ} (steps : List (Witgen.Step F)) (output : Witgen.VExpr F n)
    (names : Names) : String :=
  let body := String.intercalate "\n" (stmtsToRust names 0 (Codegen.program steps output))
  s!"        let mut output: Vec<F> = Vec::with_capacity({n});\n{body}\n        debug_assert_eq!(output.len(), {n});"

def witnessBlockToRust (block : WitnessBlock F) (row : String) : String :=
  s!"{outputToRust block.steps block.output ⟨row, "0u64"⟩}\n        {row}.extend(output);"

def fixedRowFunctionToRust (index : ℕ) (component : ComponentProgram F) :
    Except String (Option String) :=
  match component.fixedColumns with
  | none => pure none
  | some fixed => do
      let program := outputToRust fixed.program.steps fixed.program.output ⟨"&[]", "row"⟩
      return some s!"fn component_{index}_fixed_row<F: WitnessField>(row: u64) -> Vec<F> \{
{program}
    output
}"

def witnessBlocksToRust (blocks : List (WitnessBlock F)) : Except String String := do
  let rendered := blocks.map fun block => s!"    \{\n{witnessBlockToRust block "row"}\n    }"
  return String.intercalate "\n" rendered

def interactionToRust (row : String) (interaction : AbstractInteraction F) : String :=
  let message := interaction.msg.toList.map (exprToRust row)
  s!"Interaction \{ channel: {quoted interaction.channel.name}, multiplicity: {exprToRust row interaction.mult}, message: vec![{commaSep message}], assume_guarantees: {interaction.assumeGuarantees} }"

def interactionsToRust (row : String) (interactions : List (AbstractInteraction F)) : String :=
  s!"vec![{commaSep (interactions.map (interactionToRust row))}]"

def airExprToRust (fixedWidth : ℕ) (fixed main : String) : Expression F → String
  | .var cell =>
      if cell.index < fixedWidth then
        s!"Into::<AB::Expr>::into({fixed}[{cell.index}].clone())"
      else
        s!"Into::<AB::Expr>::into({main}[{cell.index - fixedWidth}].clone())"
  | .const value =>
      s!"Into::<AB::Expr>::into({fieldIn "AB::F" value})"
  | .add left right =>
      s!"({airExprToRust fixedWidth fixed main left} + {airExprToRust fixedWidth fixed main right})"
  | .mul left right =>
      s!"({airExprToRust fixedWidth fixed main left} * {airExprToRust fixedWidth fixed main right})"

def symbolicExprToRust (fixedWidth : ℕ) (fixed main : String) : Expression F → String
  | .var cell =>
      if cell.index < fixedWidth then
        s!"SymbolicExpression::<F>::from({fixed}[{cell.index}])"
      else
        s!"SymbolicExpression::<F>::from({main}[{cell.index - fixedWidth}])"
  | .const value =>
      s!"SymbolicExpression::<F>::from({field value})"
  | .add left right =>
      s!"({symbolicExprToRust fixedWidth fixed main left} + {symbolicExprToRust fixedWidth fixed main right})"
  | .mul left right =>
      s!"({symbolicExprToRust fixedWidth fixed main left} * {symbolicExprToRust fixedWidth fixed main right})"

def componentFixedWidth (component : ComponentProgram F) : ℕ :=
  component.fixedColumns.map (·.width) |>.getD 0

def componentCommittedWidth (component : ComponentProgram F) : ℕ :=
  component.width - componentFixedWidth component

def constraintCaseToRust (index : ℕ) (component : ComponentProgram F) : String :=
  let constraints := component.constraints.map
    (airExprToRust (componentFixedWidth component) "fixed" "local")
  s!"            {index} => vec![{commaSep constraints}],"

def lookupToRust (fixedWidth : ℕ) (fixed main : String)
    (interaction : AbstractInteraction F) : String :=
  let message := commaSep <| interaction.msg.toList.map
    (symbolicExprToRust fixedWidth fixed main)
  let multiplicity := symbolicExprToRust fixedWidth fixed main interaction.mult
  let (multiplicity, direction) := if interaction.assumeGuarantees then
    (s!"-({multiplicity})", "LookupDirection::Receive")
  else
    (multiplicity, "LookupDirection::Send")
  s!"                lookups.push(GeneratedLookup \{ channel: {quoted interaction.channel.name}.into(), message: vec![{message}], multiplicity: {multiplicity}, direction: {direction} });"

def lookupCaseToRust (index fixedWidth : ℕ) (fixed main : String)
    (interactions : List (AbstractInteraction F)) : String :=
  let lookups := String.intercalate "\n" <|
    interactions.map (lookupToRust fixedWidth fixed main)
  s!"            {index} => \{\n{lookups}\n            }"

def airToRust (name : String) (program : Program F) : Except String String := do
  let widths := program.components.map (toString ∘ componentCommittedWidth)
  let fixedWidths := program.components.map (toString ∘ componentFixedWidth)
  let fixedHeights := program.components.map fun component =>
    toString (component.fixedColumns.map (·.height) |>.getD 0)
  let interactionsPerRow := program.components.map fun component =>
    toString component.interactions.length
  let constraintCases := String.intercalate "\n" <|
    program.components.zipIdx.map fun (component, index) => constraintCaseToRust index component
  let tableCases := String.intercalate "\n" <| program.components.zipIdx.map fun (component, index) =>
    lookupCaseToRust index (componentFixedWidth component) "fixed" "local" component.interactions
  let fixedCases := String.intercalate "\n" <| program.components.zipIdx.filterMap
    fun (component, index) => component.fixedColumns.map fun _ =>
      s!"            {index} => component_{index}_fixed_row::<F>(row),"
  return s!"#[derive(Clone, Debug)]\n\
pub struct {name}AirSpec;\n\
\n\
impl GeneratedAirSpec for {name}AirSpec \{\n\
    const FIELD_ORDER: u64 = {fieldOrder (F := F)};\n\
    const PUBLIC_VALUES: usize = {program.publicInputWidth};\n\
    const WIDTHS: &'static [usize] = &[{commaSep widths}];\n\
    const FIXED_WIDTHS: &'static [usize] = &[{commaSep fixedWidths}];\n\
    const FIXED_HEIGHTS: &'static [usize] = &[{commaSep fixedHeights}];\n\
    const INTERACTIONS_PER_ROW: &'static [usize] = &[{commaSep interactionsPerRow}];\n\
    const VERIFIER_INTERACTIONS: usize = {program.verifierInteractions.length};\n\
\n\
    fn fixed_row<F: WitnessField>(component: usize, row: u64) -> Vec<F> \{\n\
        match component \{\n\
{fixedCases}\n\
            _ => unreachable!(\"component without fixed columns\"),\n\
        }\n\
    }\n\
\n\
    fn constraints<AB>(component: usize, fixed: &[AB::Var], local: &[AB::Var]) -> Vec<AB::Expr>\n\
    where\n\
        AB: AirBuilderWithPublicValues,\n\
        AB::F: Field + PrimeCharacteristicRing,\n\
    \{\n\
        let _ = fixed;\n\
        match component \{\n\
{constraintCases}\n\
            _ => unreachable!(\"invalid generated AIR component\"),\n\
        }\n\
    }\n\
\n\
    fn lookups<F: Field>(\n\
        component: usize,\n\
        fixed: &[SymbolicVariable<F>],\n\
        local: &[SymbolicVariable<F>],\n\
    ) -> Vec<GeneratedLookup<F>> \{\n\
        let mut lookups = Vec::new();\n\
        match component \{\n\
{tableCases}\n\
            _ => unreachable!(\"invalid generated AIR component\"),\n\
        }\n\
        lookups\n\
    }\n\
\n\
    fn verifier_interactions<F: WitnessField>(public_values: &[F]) -> Vec<Interaction<F>> \{\n\
        public_interactions(public_values)\n\
    }\n\
}\n\
\n\
pub type {name}Statement<F> = GeneratedEnsemble<F, {name}AirSpec>;"

def componentToRust (index : ℕ) (component : ComponentProgram F) : Except String String := do
  let witgen ← witnessBlocksToRust component.witnesses
  let mutable := if component.witnesses.isEmpty then "" else "mut "
  let interactions := interactionsToRust "row" component.interactions
  return s!"fn component_{index}<F: WitnessField>(input: &[F], _data: &WitnessData<F>, _hint: &WitnessData<F>) -> Result<Vec<F>, String> \{\n    if input.len() != {component.inputWidth} \{ return Err(format!(\"component input has width \{}, expected {component.inputWidth}\", input.len())); }\n    let {mutable}row = input.to_vec();\n{witgen}\n    if row.len() != {component.width} \{ return Err(format!(\"generated row has width \{}, expected {component.width}\", row.len())); }\n    Ok(row)\n}\n\nfn component_{index}_interactions<F: WitnessField>(row: &[F]) -> Vec<Interaction<F>> \{\n    {interactions}\n}"

def inputCellToRust : InputCell F → String
  | .message index => s!"InputCell::Message({index})"
  | .multiplicity => "InputCell::Multiplicity"
  | .const value => s!"InputCell::Constant({field value})"

def directionToRust : Direction → String
  | .pull => "Direction::Pull"
  | .push => "Direction::Push"

def aggregationToRust : Aggregation → String
  | .perOccurrence => "Aggregation::PerOccurrence"
  | .byMessage => "Aggregation::ByMessage"

def rowToRust (row : Array F) : String :=
  s!"vec![{commaSep (row.toList.map field)}]"

def preallocatedHandlerToRust (component : ComponentProgram F)
    (handler : PreallocatedHandler) : Except String String := do
  let some interaction := component.interactions[handler.interaction]?
    | throw s!"preallocated handler interaction {handler.interaction} is out of bounds"
  let direction := if interaction.assumeGuarantees then Direction.push else Direction.pull
  return s!"PreallocatedHandler \{ channel: {quoted interaction.channel.name}, direction: \
    {directionToRust direction}, interaction: {handler.interaction}, column: {handler.column} }"

def modeToRust (component : ComponentProgram F) : Mode F → Except String String
  | .demand mode =>
      let input := commaSep (mode.input.cells.map inputCellToRust)
      pure s!"Mode::Demand(DemandMode \{ channel: {quoted mode.channel.name}, direction: {directionToRust mode.direction}, aggregation: {aggregationToRust mode.aggregation}, input: vec![{input}] })"
  | .preallocated mode => do
      let handlers ← mode.handlers.mapM (preallocatedHandlerToRust component)
      return s!"Mode::Preallocated \{ rows: {mode.rows}, handlers: vec![{commaSep handlers}] }"

/-- The initial input of a row of a preallocated component: its fixed prefix followed by its row
program's values. -/
def initialRowToRust (index : ℕ) (component : ComponentProgram F) : Mode F → Option String
  | .demand _ => none
  | .preallocated mode =>
      let suffix := outputToRust mode.input.steps mode.input.output ⟨"&[]", "row"⟩
      let fixed := match component.fixedColumns with
        | none => "Vec::new()"
        | some _ => s!"component_{index}_fixed_row::<F>(row)"
      some s!"fn component_{index}_initial_row<F: WitnessField>(row: u64, _hint: &WitnessData<F>) -> Vec<F> \{
    let mut input = {fixed};
{suffix}
    input.extend(output);
    input
}"

def paddingToRust (padding : Padding F) : String :=
  s!"Padding \{ input: {rowToRust padding.input}, minimum_rows: {padding.minimumRows} }"

/-- Rust helpers implementing the `UInt64` division semantics of the witness IR. -/
def u64Helpers : String := "#[inline(always)]\n\
fn safe_div(left: u64, right: u64) -> u64 { if right == 0 { 0 } else { left / right } }\n\
#[inline(always)]\n\
fn safe_rem(left: u64, right: u64) -> u64 { if right == 0 { left } else { left % right } }\n"

def prelude : String := "// Generated by Clean from a typed extraction program. Do not edit.\n\
use clean_backend::witness_generation::{Aggregation, DemandMode, Direction, EnsembleWitness, HintTable, InputCell, Interaction, Mode, Padding, PreallocatedHandler, Program, WitnessData, WitnessField, WitnessGenerationError};\n\
use clean_backend::{GeneratedAirSpec, GeneratedEnsemble, GeneratedLookup};\n\
use p3_air::lookup::Direction as LookupDirection;\n\
use p3_air::{AirBuilderWithPublicValues, SymbolicExpression, SymbolicVariable};\n\
use p3_field::{Field, PrimeCharacteristicRing};\n\
use alloc::{format, vec, vec::Vec};\n\
use alloc::string::String;\n\
\n" ++ u64Helpers

/-- Render a validated extraction program as direct Rust witness and constraint code. -/
def programToRust (name : String) (program : Program F) : Except String String := do
  let components ← program.components.zipIdx.mapM fun (component, index) =>
    componentToRust index component
  let fixedRows ← program.components.zipIdx.filterMapM fun (component, index) =>
    fixedRowFunctionToRust index component
  let components := components ++ fixedRows
  let initialRows := (program.components.zip program.modes).zipIdx.filterMap fun
    | ((component, mode), index) => initialRowToRust index component mode
  let verifier := interactionsToRust "public_input" program.verifierInteractions
  let air ← airToRust name program
  let modes ← (program.components.zip program.modes).mapM fun (component, mode) =>
    modeToRust component mode
  let modes := commaSep modes
  let padding := commaSep (program.padding.map paddingToRust)
  let componentNames := commaSep (program.components.map (quoted ∘ (·.name)))
  let hintTables := commaSep <| program.hintTables.map fun table =>
    s!"HintTable \{ key: {quoted table.key}, width: {table.width}, offset: {table.offset}, rows: {table.rows} }"
  let fixedWidths := commaSep (program.components.map (toString ∘ componentFixedWidth))
  let completeCases := String.intercalate "\n" <| program.components.zipIdx.map fun (_, index) =>
    s!"            {index} => component_{index}(input, data, hint),"
  let initialCases := String.intercalate "\n" <| (program.modes.zipIdx.filter fun
    | (.preallocated _, _) => true
    | (.demand _, _) => false).map fun (_, index) =>
      s!"            {index} => component_{index}_initial_row(row, hint),"
  let interactionCases := String.intercalate "\n" <| program.components.zipIdx.map fun (_, index) =>
    s!"            {index} => component_{index}_interactions(row),"
  return s!"{prelude}\n{String.intercalate "\n\n" components}\n\n{String.intercalate "\n\n" initialRows}\n\nfn public_interactions<F: WitnessField>(public_input: &[F]) -> Vec<Interaction<F>> \{\n    {verifier}\n}\n\n{air}\n\npub struct {name};\n\nimpl<F: WitnessField> Program<F> for {name} \{\n    const FIELD_ORDER: u64 = {fieldOrder (F := F)};\n    const FUEL: usize = {program.fuel};\n    const COMPONENTS: usize = {program.components.length};\n    const PUBLIC_INPUTS: usize = {program.publicInputWidth};\n    const PROVER_INPUTS: usize = {program.proverInputWidth};\n    const HINT_TABLES: &'static [HintTable] = &[{hintTables}];\n    const FIXED_WIDTHS: &'static [usize] = &[{fixedWidths}];\n    const COMPONENT_NAMES: &'static [&'static str] = &[{componentNames}];\n\n    fn modes() -> Vec<Mode<F>> \{ vec![{modes}] }\n\n    fn padding() -> Vec<Padding<F>> \{ vec![{padding}] }\n\n    fn initial_row(component: usize, row: u64, hint: &WitnessData<F>) -> Vec<F> \{\n        match component \{\n{initialCases}\n            _ => unreachable!(\"component without preallocated rows\"),\n        }\n    }\n\n    fn complete_row(component: usize, input: &[F], data: &WitnessData<F>, hint: &WitnessData<F>) -> Result<Vec<F>, String> \{\n        match component \{\n{completeCases}\n            _ => Err(format!(\"component index \{component} is out of bounds\")),\n        }\n    }\n\n    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>> \{\n        match component \{\n{interactionCases}\n            _ => vec![],\n        }\n    }\n\n    fn verifier_interactions(public_input: &[F]) -> Vec<Interaction<F>> \{\n        public_interactions(public_input)\n    }\n}\n\npub fn generate<F: WitnessField>(public_input: &[F], prover_input: &[F]) -> Result<EnsembleWitness<F>, WitnessGenerationError> \{\n    clean_backend::witness_generation::generate::<F, {name}>(public_input, prover_input)\n}\n"

/-- Validate an ensemble into the typed artifact and render that artifact as Rust. -/
def ensembleToRust (name : String) (ens : FormalEnsemble F PublicIO)
    (config : Config F) :
    Except String String := do
  let program ← lower ens config |>.mapError toString
  programToRust name program

end Backends.Plonky3.Print
