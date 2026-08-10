import Clean.Air.Extraction.Lower

/-!
# Rust rendering for typed AIR extraction programs

This is the only string-producing part of ensemble extraction. It consumes a validated
`Extraction.Program`; lowering, validation, and executable semantics live in `IR.lean` and
`Lower.lean`. Generic Plonky3 `Air` plumbing lives in the Rust backend.
-/

namespace Air.Flat.Extraction.Rust

open Air.Flat.WitnessGeneration
open Air.Flat.Extraction

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

private def field (value : F) : String :=
  s!"F::from_canonical_u64({FiniteField.val value}u64)"

private def airField (value : F) : String :=
  s!"F::from_u64({FiniteField.val value}u64)"

private def quoted (value : String) : String := reprStr value

private def commaSep (values : List String) : String :=
  String.intercalate ", " values

private def exprToRust (row : String) : Expression F → String
  | .var cell => s!"{row}.get({cell.index}).copied().unwrap_or(F::ZERO)"
  | .const value => field value
  | .add left right => s!"({exprToRust row left} + {exprToRust row right})"
  | .mul left right => s!"({exprToRust row left} * {exprToRust row right})"

mutual

private def fexprToRust (locals : Array LocalSort) (row idx : String) :
    Witgen.FExpr F → Except String String
  | .expr expression => pure (exprToRust row expression)
  | .const value => pure (field value)
  | .localVar index =>
      match locals[index]? with
      | some .field => pure s!"local_{index}"
      | _ => throw s!"invalid field local {index} reached the validated Rust renderer"
  | .add left right => return s!"({← fexprToRust locals row idx left} + {← fexprToRust locals row idx right})"
  | .mul left right => return s!"({← fexprToRust locals row idx left} * {← fexprToRust locals row idx right})"
  | .inv value => return s!"({← fexprToRust locals row idx value}).inverse_or_zero()"
  | .ofU64 value => return s!"F::from_canonical_u64({← u64exprToRust locals row idx value})"
  | .ite condition thenValue elseValue =>
      return s!"if {← bexprToRust locals row idx condition} \{ {← fexprToRust locals row idx thenValue} } else \{ {← fexprToRust locals row idx elseValue} }"
  | .listGet values index => do
      let values ← fexprListToRust locals row idx values
      return s!"[{commaSep values}].get(({← u64exprToRust locals row idx index}) as usize).copied().unwrap_or(F::ZERO)"
  | .dataGet key width dataRow column =>
      return s!"_data.get({quoted key}, {width}, ({← u64exprToRust locals row idx dataRow}) as usize, {column.val})"
  | .hintGet .. => throw "external prover hints cannot be rendered for Rust yet"

private def fexprListToRust (locals : Array LocalSort) (row idx : String) :
    List (Witgen.FExpr F) → Except String (List String)
  | [] => pure []
  | value :: values =>
      return (← fexprToRust locals row idx value) ::
        (← fexprListToRust locals row idx values)

private def u64exprToRust (locals : Array LocalSort) (row idx : String) :
    Witgen.U64Expr F → Except String String
  | .const value => pure s!"{value.toNat}u64"
  | .val value => return s!"({← fexprToRust locals row idx value}).canonical_u64()"
  | .idx => pure idx
  | .localVar index =>
      match locals[index]? with
      | some .u64 => pure s!"local_{index}"
      | _ => throw s!"invalid u64 local {index} reached the validated Rust renderer"
  | .add left right => return s!"({← u64exprToRust locals row idx left}).wrapping_add({← u64exprToRust locals row idx right})"
  | .mul left right => return s!"({← u64exprToRust locals row idx left}).wrapping_mul({← u64exprToRust locals row idx right})"
  | .div left right => return s!"safe_div({← u64exprToRust locals row idx left}, {← u64exprToRust locals row idx right})"
  | .mod left right => return s!"safe_rem({← u64exprToRust locals row idx left}, {← u64exprToRust locals row idx right})"
  | .land left right => return s!"({← u64exprToRust locals row idx left} & {← u64exprToRust locals row idx right})"
  | .lor left right => return s!"({← u64exprToRust locals row idx left} | {← u64exprToRust locals row idx right})"
  | .lxor left right => return s!"({← u64exprToRust locals row idx left} ^ {← u64exprToRust locals row idx right})"
  | .shiftL left right => return s!"({← u64exprToRust locals row idx left}).wrapping_shl(({← u64exprToRust locals row idx right} & 63) as u32)"
  | .shiftR left right => return s!"({← u64exprToRust locals row idx left}).wrapping_shr(({← u64exprToRust locals row idx right} & 63) as u32)"
  | .ite condition thenValue elseValue =>
      return s!"if {← bexprToRust locals row idx condition} \{ {← u64exprToRust locals row idx thenValue} } else \{ {← u64exprToRust locals row idx elseValue} }"

private def bexprToRust (locals : Array LocalSort) (row idx : String) :
    Witgen.BExpr F → Except String String
  | .true => pure "true"
  | .false => pure "false"
  | .feq left right => return s!"({← fexprToRust locals row idx left} == {← fexprToRust locals row idx right})"
  | .neq left right => return s!"({← u64exprToRust locals row idx left} == {← u64exprToRust locals row idx right})"
  | .lt left right => return s!"({← u64exprToRust locals row idx left} < {← u64exprToRust locals row idx right})"
  | .flt left right => return s!"(({← fexprToRust locals row idx left}).canonical_u64() < ({← fexprToRust locals row idx right}).canonical_u64())"
  | .bit value bit => return s!"((({← fexprToRust locals row idx value}).canonical_u64() >> {bit}) & 1) == 1"
  | .not condition => return s!"!({← bexprToRust locals row idx condition})"
  | .and left right => return s!"({← bexprToRust locals row idx left} && {← bexprToRust locals row idx right})"

end

private def stepSort : Witgen.Step F → LocalSort
  | .letF _ => .field
  | .letU _ => .u64

private def stepsToRust (steps : List (Witgen.Step F)) (row : String) : Except String String := do
  let locals := steps.map stepSort |>.toArray
  let lines ← steps.zipIdx.mapM fun (step, index) =>
    match step with
    | .letF value => return s!"        let local_{index}: F = {← fexprToRust locals row "0u64" value};"
    | .letU value => return s!"        let local_{index}: u64 = {← u64exprToRust locals row "0u64" value};"
  return String.intercalate "\n" lines

private def vexprPushRust (locals : Array LocalSort) (row output idx : String) :
    {n : ℕ} → Witgen.VExpr F n → Except String String
  | _, .lit values => do
      let lines ← values.toList.mapM fun value =>
        return s!"        {output}.push({← fexprToRust locals row idx value});"
      return String.intercalate "\n" lines
  | _, .mapRange n body => do
      let body ← fexprToRust locals row "idx" body
      return s!"        for idx in 0u64..{n}u64 \{\n            {output}.push({body});\n        }"
  | n, .envRange offset =>
      pure s!"        for idx in 0usize..{n}usize \{\n            {output}.push({row}.get({offset}usize + idx).copied().unwrap_or(F::ZERO));\n        }"
  | n, .bitsOf value => do
      let value ← fexprToRust locals row idx value
      return s!"        let bits_value = ({value}).canonical_u64();\n        for bit in 0u32..{n}u32 \{\n            {output}.push(F::from_canonical_u64((bits_value >> bit) & 1));\n        }"
  | _, .append left right =>
      return s!"{← vexprPushRust locals row output idx left}\n{← vexprPushRust locals row output idx right}"

private def witnessBlockToRust (block : WitnessBlock F) (row : String) : Except String String := do
  let locals := block.steps.map stepSort |>.toArray
  let stepCode ← stepsToRust block.steps row
  let outputCode ← vexprPushRust locals row "output" "0u64" block.output
  return s!"{stepCode}\n        let mut output = Vec::with_capacity({block.outputWidth});\n{outputCode}\n        debug_assert_eq!(output.len(), {block.outputWidth});\n        {row}.extend(output);"

private def witnessBlocksToRust (blocks : List (WitnessBlock F)) : Except String String := do
  let rendered ← blocks.mapM fun block =>
    return s!"    \{\n{← witnessBlockToRust block "row"}\n    }"
  return String.intercalate "\n" rendered

private def interactionToRust (row : String) (interaction : AbstractInteraction F) : String :=
  let message := interaction.msg.toList.map (exprToRust row)
  s!"Interaction \{ channel: {quoted interaction.channel.name}, multiplicity: {exprToRust row interaction.mult}, message: vec![{commaSep message}], assume_guarantees: {interaction.assumeGuarantees} }"

private def interactionsToRust (row : String) (interactions : List (AbstractInteraction F)) : String :=
  s!"vec![{commaSep (interactions.map (interactionToRust row))}]"

private def airExprToRust (fixedWidth : ℕ) (fixed main : String) : Expression F → String
  | .var cell =>
      if cell.index < fixedWidth then
        s!"Into::<AB::Expr>::into({fixed}[{cell.index}].clone())"
      else
        s!"Into::<AB::Expr>::into({main}[{cell.index - fixedWidth}].clone())"
  | .const value =>
      s!"Into::<AB::Expr>::into(AB::F::from_u64({FiniteField.val value}u64))"
  | .add left right =>
      s!"({airExprToRust fixedWidth fixed main left} + {airExprToRust fixedWidth fixed main right})"
  | .mul left right =>
      s!"({airExprToRust fixedWidth fixed main left} * {airExprToRust fixedWidth fixed main right})"

private def symbolicExprToRust (fixedWidth : ℕ) (fixed main : String) : Expression F → String
  | .var cell =>
      if cell.index < fixedWidth then
        s!"SymbolicExpression::<F>::from({fixed}[{cell.index}])"
      else
        s!"SymbolicExpression::<F>::from({main}[{cell.index - fixedWidth}])"
  | .const value =>
      s!"SymbolicExpression::<F>::from(F::from_u64({FiniteField.val value}u64))"
  | .add left right =>
      s!"({symbolicExprToRust fixedWidth fixed main left} + {symbolicExprToRust fixedWidth fixed main right})"
  | .mul left right =>
      s!"({symbolicExprToRust fixedWidth fixed main left} * {symbolicExprToRust fixedWidth fixed main right})"

private def componentFixedWidth (component : ComponentProgram F) : ℕ :=
  component.fixedColumns.map (·.width) |>.getD 0

private def componentCommittedWidth (component : ComponentProgram F) : ℕ :=
  component.width - componentFixedWidth component

private def constraintCaseToRust (index : ℕ) (component : ComponentProgram F) : String :=
  let constraints := component.constraints.map
    (airExprToRust (componentFixedWidth component) "fixed" "local")
  s!"            {index} => vec![{commaSep constraints}],"

private def lookupToRust (fixedWidth : ℕ) (fixed main : String)
    (interaction : AbstractInteraction F) : String :=
  let message := commaSep <| interaction.msg.toList.map
    (symbolicExprToRust fixedWidth fixed main)
  let multiplicity := symbolicExprToRust fixedWidth fixed main interaction.mult
  let (multiplicity, direction) := if interaction.assumeGuarantees then
    (s!"-({multiplicity})", "LookupDirection::Receive")
  else
    (multiplicity, "LookupDirection::Send")
  s!"                lookups.push(GeneratedLookup \{ channel: {quoted interaction.channel.name}.into(), message: vec![{message}], multiplicity: {multiplicity}, direction: {direction} });"

private def lookupCaseToRust (index fixedWidth : ℕ) (fixed main : String)
    (interactions : List (AbstractInteraction F)) : String :=
  let lookups := String.intercalate "\n" <|
    interactions.map (lookupToRust fixedWidth fixed main)
  s!"            {index} => \{\n{lookups}\n            }"

private def fixedColumnsToRust (component : ComponentProgram F) : String :=
  match component.fixedColumns with
  | none => "None"
  | some fixed =>
      let values := commaSep <| fixed.rows.flatMap fun row => row.toList.map airField
      s!"Some(RowMajorMatrix::new(vec![{values}], {fixed.width}))"

private def airToRust (name : String) (program : Program F) : String :=
  let widths := program.components.map (toString ∘ componentCommittedWidth)
  let fixedWidths := program.components.map (toString ∘ componentFixedWidth)
  let fixedHeights := program.components.map fun component =>
    toString (component.fixedColumns.map (·.rows.length) |>.getD 0)
  let constraintCases := String.intercalate "\n" <|
    program.components.zipIdx.map fun (component, index) => constraintCaseToRust index component
  let tableCases := String.intercalate "\n" <| program.components.zipIdx.map fun (component, index) =>
    lookupCaseToRust index (componentFixedWidth component) "fixed" "local" component.interactions
  let fixedCases := String.intercalate "\n" <| program.components.zipIdx.map fun (component, index) =>
    s!"            {index} => {fixedColumnsToRust component},"
  s!"#[derive(Clone, Debug)]\n\
pub struct {name}AirSpec;\n\
\n\
impl GeneratedAirSpec for {name}AirSpec \{\n\
    const PUBLIC_VALUES: usize = {program.publicInputWidth};\n\
    const WIDTHS: &'static [usize] = &[{commaSep widths}];\n\
    const FIXED_WIDTHS: &'static [usize] = &[{commaSep fixedWidths}];\n\
    const FIXED_HEIGHTS: &'static [usize] = &[{commaSep fixedHeights}];\n\
\n\
    fn fixed_trace<F: Field + PrimeCharacteristicRing>(component: usize) -> Option<RowMajorMatrix<F>> \{\n\
        match component \{\n\
{fixedCases}\n\
            _ => unreachable!(\"invalid generated AIR component\"),\n\
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
pub type {name}Air = GeneratedAir<{name}AirSpec>;"

private def componentToRust (index : ℕ) (component : ComponentProgram F) : Except String String := do
  let witgen ← witnessBlocksToRust component.witnesses
  let mutable := if component.witnesses.isEmpty then "" else "mut "
  let interactions := interactionsToRust "row" component.interactions
  return s!"fn component_{index}<F: WitnessField>(input: &[F], _data: &WitnessData<F>) -> Result<Vec<F>, String> \{\n    if input.len() != {component.inputWidth} \{ return Err(format!(\"component input has width \{}, expected {component.inputWidth}\", input.len())); }\n    let {mutable}row = input.to_vec();\n{witgen}\n    if row.len() != {component.width} \{ return Err(format!(\"generated row has width \{}, expected {component.width}\", row.len())); }\n    Ok(row)\n}\n\nfn component_{index}_interactions<F: WitnessField>(row: &[F]) -> Vec<Interaction<F>> \{\n    {interactions}\n}"

private def inputCellToRust : InputCell F → String
  | .message index => s!"InputCell::Message({index})"
  | .multiplicity => "InputCell::Multiplicity"
  | .const value => s!"InputCell::Constant({field value})"

private def directionToRust : Direction → String
  | .pull => "Direction::Pull"
  | .push => "Direction::Push"

private def aggregationToRust : Aggregation → String
  | .perOccurrence => "Aggregation::PerOccurrence"
  | .byMessage => "Aggregation::ByMessage"

private def rowToRust (row : Array F) : String :=
  s!"vec![{commaSep (row.toList.map field)}]"

private def slotToRust (slot : FixedSlot F) : String :=
  s!"FixedSlot \{ channel: {quoted slot.channel}, direction: {directionToRust slot.direction}, message: {rowToRust slot.message}, row: {slot.row}, column: {slot.column} }"

private def modeToRust : Mode F → String
  | .demand mode =>
      let input := commaSep (mode.input.cells.map inputCellToRust)
      s!"Mode::Demand(DemandMode \{ channel: {quoted mode.channel}, direction: {directionToRust mode.direction}, aggregation: {aggregationToRust mode.aggregation}, input: vec![{input}] })"
  | .fixed rows slots =>
      s!"Mode::Fixed \{ input_rows: vec![{commaSep (rows.map rowToRust)}], slots: vec![{commaSep (slots.map slotToRust)}] }"

private def paddingToRust (padding : Padding F) : String :=
  s!"Padding \{ input: {rowToRust padding.input}, minimum_rows: {padding.minimumRows} }"

private def prelude : String := "// Generated by Clean from a typed extraction program. Do not edit.\n\
use clean_backend::witness_generation::{Aggregation, DemandMode, Direction, EnsembleWitness, FixedSlot, InputCell, Interaction, Mode, Padding, Program, WitnessData, WitnessField};\n\
use clean_backend::{GeneratedAir, GeneratedAirSpec, GeneratedLookup};\n\
use p3_air::lookup::Direction as LookupDirection;\n\
use p3_air::{AirBuilderWithPublicValues, SymbolicExpression, SymbolicVariable};\n\
use p3_field::{Field, PrimeCharacteristicRing};\n\
use p3_matrix::dense::RowMajorMatrix;\n\
use alloc::{format, vec, vec::Vec};\n\
use alloc::string::String;\n\
\n\
#[inline(always)]\n\
fn safe_div(left: u64, right: u64) -> u64 { if right == 0 { 0 } else { left / right } }\n\
#[inline(always)]\n\
fn safe_rem(left: u64, right: u64) -> u64 { if right == 0 { 0 } else { left % right } }\n"

/-- Render a validated extraction program as direct Rust witness and constraint code. -/
def programToRust (name : String) (program : Program F) : Except String String := do
  let components ← program.components.zipIdx.mapM fun (component, index) =>
    componentToRust index component
  let verifier := interactionsToRust "public_input" program.verifierInteractions
  let air := airToRust name program
  let modes := commaSep (program.modes.map modeToRust)
  let padding := commaSep (program.padding.map paddingToRust)
  let componentNames := commaSep (program.components.map (quoted ∘ (·.name)))
  let fixedWidths := commaSep (program.components.map (toString ∘ componentFixedWidth))
  let completeCases := String.intercalate "\n" <| program.components.zipIdx.map fun (_, index) =>
    s!"            {index} => component_{index}(input, data),"
  let interactionCases := String.intercalate "\n" <| program.components.zipIdx.map fun (_, index) =>
    s!"            {index} => component_{index}_interactions(row),"
  return s!"{prelude}\n{String.intercalate "\n\n" components}\n\nfn public_interactions<F: WitnessField>(public_input: &[F]) -> Vec<Interaction<F>> \{\n    {verifier}\n}\n\n{air}\n\npub struct {name};\n\nimpl<F: WitnessField> Program<F> for {name} \{\n    const FUEL: usize = {program.fuel};\n    const COMPONENTS: usize = {program.components.length};\n    const FIXED_WIDTHS: &'static [usize] = &[{fixedWidths}];\n    const COMPONENT_NAMES: &'static [&'static str] = &[{componentNames}];\n\n    fn modes() -> Vec<Mode<F>> \{ vec![{modes}] }\n\n    fn padding() -> Vec<Padding<F>> \{ vec![{padding}] }\n\n    fn complete_row(component: usize, input: &[F], data: &WitnessData<F>) -> Result<Vec<F>, String> \{\n        match component \{\n{completeCases}\n            _ => Err(format!(\"component index \{component} is out of bounds\")),\n        }\n    }\n\n    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>> \{\n        match component \{\n{interactionCases}\n            _ => vec![],\n        }\n    }\n\n    fn verifier_interactions(public_input: &[F]) -> Vec<Interaction<F>> \{\n        public_interactions(public_input)\n    }\n}\n\npub fn generate<F: WitnessField>(public_input: &[F]) -> Result<EnsembleWitness<F>, String> \{\n    clean_backend::witness_generation::generate::<F, {name}>(public_input)\n}\n"

/-- Validate an ensemble into the typed artifact and render that artifact as Rust. -/
def ensembleToRust (name : String) (ensemble : Ensemble F PublicIO) (config : Config F) :
    Except String String := do
  let program ← lower ensemble config |>.mapError toString
  programToRust name program

end Air.Flat.Extraction.Rust
