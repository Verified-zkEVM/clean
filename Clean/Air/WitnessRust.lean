import Clean.Air.WitnessExport

/-!
# Direct Rust extraction for ensemble witness generation

This compiler lowers structured witness IR and channel-generation metadata to ordinary
Rust functions. The generated proving-time path contains no JSON parser or IR
interpreter: witness expressions, row interactions, and generation modes are Rust code.
-/

namespace Air.Flat.WitnessGeneration.Rust

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

private def field (value : F) : String :=
  s!"F::from_canonical_u64({FiniteField.val value}u64)"

private def quoted (value : String) : String := reprStr value

private def commaSep (values : List String) : String :=
  String.intercalate ", " values

inductive LocalSort where
  | field
  | u64
deriving DecidableEq

private partial def exprToRust (row : String) : Expression F → String
  | .var v => s!"{row}.get({v.index}).copied().unwrap_or(F::ZERO)"
  | .const value => field value
  | .add left right => s!"({exprToRust row left} + {exprToRust row right})"
  | .mul left right => s!"({exprToRust row left} * {exprToRust row right})"

mutual

private partial def fexprToRust (locals : Array LocalSort) (row idx : String) :
    Witgen.FExpr F → Except String String
  | .expr expression => pure (exprToRust row expression)
  | .const value => pure (field value)
  | .localVar index =>
      match locals[index]? with
      | some .field => pure s!"local_{index}"
      | _ => pure "F::ZERO"
  | .add left right => return s!"({← fexprToRust locals row idx left} + {← fexprToRust locals row idx right})"
  | .mul left right => return s!"({← fexprToRust locals row idx left} * {← fexprToRust locals row idx right})"
  | .inv value => return s!"({← fexprToRust locals row idx value}).inverse_or_zero()"
  | .ofU64 value => return s!"F::from_canonical_u64({← u64exprToRust locals row idx value})"
  | .ite condition thenValue elseValue =>
      return s!"if {← bexprToRust locals row idx condition} \{ {← fexprToRust locals row idx thenValue} } else \{ {← fexprToRust locals row idx elseValue} }"
  | .listGet values index => do
      let values ← values.mapM (fexprToRust locals row idx)
      return s!"[{commaSep values}].get(({← u64exprToRust locals row idx index}) as usize).copied().unwrap_or(F::ZERO)"
  | .dataGet .. => throw "external ProverData cannot be extracted yet"
  | .hintGet .. => throw "external prover hints cannot be extracted yet"

private partial def u64exprToRust (locals : Array LocalSort) (row idx : String) :
    Witgen.U64Expr F → Except String String
  | .const value => pure s!"{value.toNat}u64"
  | .val value => return s!"({← fexprToRust locals row idx value}).canonical_u64()"
  | .idx => pure idx
  | .localVar index =>
      match locals[index]? with
      | some .u64 => pure s!"local_{index}"
      | _ => pure "0u64"
  | .add left right => return s!"({← u64exprToRust locals row idx left}).wrapping_add({← u64exprToRust locals row idx right})"
  | .mul left right => return s!"({← u64exprToRust locals row idx left}).wrapping_mul({← u64exprToRust locals row idx right})"
  | .div left right => do
      let left ← u64exprToRust locals row idx left
      let right ← u64exprToRust locals row idx right
      return s!"safe_div({left}, {right})"
  | .mod left right => do
      let left ← u64exprToRust locals row idx left
      let right ← u64exprToRust locals row idx right
      return s!"safe_rem({left}, {right})"
  | .land left right => return s!"({← u64exprToRust locals row idx left} & {← u64exprToRust locals row idx right})"
  | .lor left right => return s!"({← u64exprToRust locals row idx left} | {← u64exprToRust locals row idx right})"
  | .lxor left right => return s!"({← u64exprToRust locals row idx left} ^ {← u64exprToRust locals row idx right})"
  | .shiftL left right => return s!"({← u64exprToRust locals row idx left}).wrapping_shl(({← u64exprToRust locals row idx right} & 63) as u32)"
  | .shiftR left right => return s!"({← u64exprToRust locals row idx left}).wrapping_shr(({← u64exprToRust locals row idx right} & 63) as u32)"
  | .ite condition thenValue elseValue =>
      return s!"if {← bexprToRust locals row idx condition} \{ {← u64exprToRust locals row idx thenValue} } else \{ {← u64exprToRust locals row idx elseValue} }"

private partial def bexprToRust (locals : Array LocalSort) (row idx : String) :
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
  | _, .append left right => do
      return s!"{← vexprPushRust locals row output idx left}\n{← vexprPushRust locals row output idx right}"

private def witgenToRust {n : ℕ} (code : Witgen.WitgenIR F n) (row : String) :
    Except String String := do
  match code with
  | .native _ => throw "native witness closures cannot be extracted"
  | .ir steps output =>
      let locals := steps.map stepSort |>.toArray
      let stepCode ← stepsToRust steps row
      let outputCode ← vexprPushRust locals row "output" "0u64" output
      return s!"{stepCode}\n        let mut output = Vec::with_capacity({n});\n{outputCode}\n        debug_assert_eq!(output.len(), {n});\n        row.extend(output);"

private def witnessOpsToRust (operations : List (FlatOperation F)) : Except String String := do
  let blocks ← operations.filterMapM fun operation =>
    match operation with
    | .witness _ code => return some s!"    \{\n{← witgenToRust code "row"}\n    }"
    | _ => return none
  return String.intercalate "\n" blocks

private def interactionToRust (row : String) (interaction : AbstractInteraction F) : String :=
  let message := interaction.msg.toList.map (exprToRust row)
  s!"Interaction \{ channel: {quoted interaction.channel.name}, multiplicity: {exprToRust row interaction.mult}, message: vec![{commaSep message}], assume_guarantees: {interaction.assumeGuarantees} }"

private def interactionsToRust (row : String) (interactions : List (AbstractInteraction F)) : String :=
  s!"vec![{commaSep (interactions.map (interactionToRust row))}]"

private partial def airExprToRust (cells : String) : Expression F → String
  | .var v => s!"Into::<AB::Expr>::into({cells}[{v.index}].clone())"
  | .const value =>
      s!"Into::<AB::Expr>::into(AB::F::from_u64({FiniteField.val value}u64))"
  | .add left right =>
      s!"({airExprToRust cells left} + {airExprToRust cells right})"
  | .mul left right =>
      s!"({airExprToRust cells left} * {airExprToRust cells right})"

private partial def symbolicExprToRust (cells : String) : Expression F → String
  | .var v => s!"SymbolicExpression::<AB::F>::from({cells}[{v.index}])"
  | .const value =>
      s!"SymbolicExpression::<AB::F>::from(AB::F::from_u64({FiniteField.val value}u64))"
  | .add left right =>
      s!"({symbolicExprToRust cells left} + {symbolicExprToRust cells right})"
  | .mul left right =>
      s!"({symbolicExprToRust cells left} * {symbolicExprToRust cells right})"

private def constraintCaseToRust (index : ℕ) (component : Component F) : String :=
  let constraints := component.rowOperations.constraints.map (airExprToRust "local")
  s!"            {index + 1} => vec![{commaSep constraints}],"

private def lookupToRust (cells : String) (selector : Option String)
    (interaction : AbstractInteraction F) : String :=
  let message := commaSep <| interaction.msg.toList.map (symbolicExprToRust cells)
  let multiplicity := match selector with
    | none => symbolicExprToRust cells interaction.mult
    | some selector => s!"({symbolicExprToRust cells interaction.mult} * {selector})"
  let (multiplicity, direction) := if interaction.assumeGuarantees then
    (s!"-({multiplicity})", "LookupDirection::Receive")
  else
    (multiplicity, "LookupDirection::Send")
  s!"        lookups.push(Air::<AB>::register_lookup(self, Kind::Global({quoted interaction.channel.name}.into()), &[(vec![{message}], {multiplicity}, {direction})]));"

private def lookupCaseToRust (index : ℕ) (cells : String) (selector : Option String)
    (interactions : List (AbstractInteraction F)) : String :=
  let lookups := String.intercalate "\n" <| interactions.map (lookupToRust cells selector)
  s!"            {index} => \{\n{lookups}\n            }"

private def airToRust (name : String) (ensemble : Ensemble F PublicIO) : String :=
  let widths := "1" :: ensemble.tables.map (toString ·.width)
  let constraintCases := String.intercalate "\n" <|
    ensemble.tables.zipIdx.map fun (component, index) => constraintCaseToRust index component
  let verifierSelector :=
    "SymbolicExpression::<AB::F>::from(preprocessed_local.as_ref().expect(\"missing verifier selector\")[0])"
  let verifierCase := lookupCaseToRust 0 "public_values" (some verifierSelector)
    ensemble.verifierOperations.interactions
  let tableCases := String.intercalate "\n" <| ensemble.tables.zipIdx.map fun (component, index) =>
    lookupCaseToRust (index + 1) "local" (some verifierSelector)
      component.rowOperations.interactions
  s!"#[derive(Clone, Debug)]\n\
pub struct {name}Air \{ component: usize, trace_height: usize, active_rows: usize, num_lookups: usize }\n\
\n\
impl {name}Air \{\n\
    pub fn all(trace_heights: &[usize], active_rows: &[usize]) -> Vec<Self> \{\n\
        assert_eq!(trace_heights.len(), {ensemble.tables.length + 1});\n\
        assert_eq!(active_rows.len(), {ensemble.tables.length + 1});\n\
        trace_heights.iter().copied().zip(active_rows.iter().copied()).enumerate().map(|(component, (trace_height, active_rows))| Self \{ component, trace_height, active_rows, num_lookups: 0 }).collect()\n\
    }\n\
}\n\
\n\
impl EnsembleAir for {name}Air \{\n\
    fn trace_height(&self) -> usize \{ self.trace_height }\n\
}\n\
\n\
impl<F: Field> BaseAir<F> for {name}Air \{\n\
    fn width(&self) -> usize \{ [{commaSep widths}][self.component] }\n\
\n\
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> \{\n\
        let mut selector = vec![F::ZERO; self.trace_height];\n\
        selector[..self.active_rows].fill(F::ONE);\n\
        Some(RowMajorMatrix::new(selector, 1))\n\
    }\n\
}\n\
\n\
impl<AB: AirBuilderWithPublicValues> Air<AB> for {name}Air\n\
where AB::F: Field + PrimeCharacteristicRing\n\
\{\n\
    fn eval(&self, builder: &mut AB) \{\n\
        let main = builder.main();\n\
        let local = main.row_slice(0).expect(\"empty trace\");\n\
        let preprocessed = builder.preprocessed();\n\
        let preprocessed_local = preprocessed.as_ref().and_then(|matrix| matrix.row_slice(0)).expect(\"missing active-row selector\");\n\
        let active = Into::<AB::Expr>::into(preprocessed_local[0].clone());\n\
        let constraints: Vec<AB::Expr> = match self.component \{\n\
            0 => vec![],\n\
{constraintCases}\n\
            _ => unreachable!(\"invalid generated AIR component\"),\n\
        };\n\
        for constraint in constraints \{ builder.assert_zero(active.clone() * constraint); }\n\
    }\n\
\n\
    fn get_lookups(&mut self) -> Vec<Lookup<AB::F>>\n\
    where AB: PermutationAirBuilder + AirBuilderWithPublicValues\n\
    \{\n\
        self.num_lookups = 0;\n\
        let preprocessed_width = 1;\n\
        let symbolic = SymbolicAirBuilder::<AB::F>::new(preprocessed_width, BaseAir::<AB::F>::width(self), {size PublicIO}, 0, 0);\n\
        let main = AirBuilder::main(&symbolic);\n\
        let local = main.row_slice(0).expect(\"empty symbolic trace\");\n\
        let preprocessed = AirBuilder::preprocessed(&symbolic);\n\
        let preprocessed_local = preprocessed.as_ref().and_then(|matrix| matrix.row_slice(0));\n\
        let public_values = AirBuilderWithPublicValues::public_values(&symbolic);\n\
        let mut lookups = Vec::new();\n\
        match self.component \{\n\
{verifierCase},\n\
{tableCases}\n\
            _ => unreachable!(\"invalid generated AIR component\"),\n\
        }\n\
        lookups\n\
    }\n\
\n\
    fn add_lookup_columns(&mut self) -> Vec<usize> \{\n\
        let index = self.num_lookups;\n\
        self.num_lookups += 1;\n\
        vec![index]\n\
    }\n\
}"

private def componentToRust (index : ℕ) (component : Component F) : Except String String := do
  let operations := component.rowOperations
  let flat := operations.toFlat
  let witgen ← witnessOpsToRust flat
  let mutable := if flat.any fun operation =>
    match operation with | .witness _ _ => true | _ => false then "mut " else ""
  let interactions := interactionsToRust "row" operations.interactions
  return s!"fn component_{index}<F: WitnessField>(input: &[F]) -> Result<Vec<F>, String> \{\n    if input.len() != {component.rowOffset} \{ return Err(format!(\"component input has width \{}, expected {component.rowOffset}\", input.len())); }\n    let {mutable}row = input.to_vec();\n{witgen}\n    if row.len() != {component.width} \{ return Err(format!(\"generated row has width \{}, expected {component.width}\", row.len())); }\n    Ok(row)\n}\n\nfn component_{index}_interactions<F: WitnessField>(row: &[F]) -> Vec<Interaction<F>> \{\n    {interactions}\n}"

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

private def prelude : String := "// Generated by Clean from structured witness IR. Do not edit.\n\
use clean_backend::witness_generation::{Aggregation, DemandMode, Direction, EnsembleWitness, FixedSlot, InputCell, Interaction, Mode, Program, WitnessField};\n\
use clean_backend::EnsembleAir;\n\
use p3_air::lookup::{Direction as LookupDirection, Kind, Lookup};\n\
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PermutationAirBuilder};\n\
use p3_field::{Field, PrimeCharacteristicRing};\n\
use p3_matrix::dense::RowMajorMatrix;\n\
use p3_matrix::Matrix;\n\
use p3_uni_stark::{SymbolicAirBuilder, SymbolicExpression};\n\
use alloc::{format, vec, vec::Vec};\n\
use alloc::string::String;\n\
\n\
#[inline(always)]\n\
fn safe_div(left: u64, right: u64) -> u64 { if right == 0 { 0 } else { left / right } }\n\
#[inline(always)]\n\
fn safe_rem(left: u64, right: u64) -> u64 { if right == 0 { 0 } else { left % right } }\n"

/-- Compile an ensemble witness program to direct Rust source. -/
def ensembleToRust (name : String) (ensemble : Ensemble F PublicIO) (config : Config F) :
    Except String String := do
  unless config.modes.length = ensemble.tables.length do
    throw "generation-mode count does not match ensemble component count"
  let components ← ensemble.tables.zipIdx.mapM fun (component, index) =>
    componentToRust index component
  let verifier := interactionsToRust "public_input" ensemble.verifierOperations.interactions
  let air := airToRust name ensemble
  let components := components ++ [air]
  let modes := commaSep (config.modes.map modeToRust)
  let completeCases := String.intercalate "\n" <| ensemble.tables.zipIdx.map fun (_, index) =>
    s!"            {index} => component_{index}(input),"
  let interactionCases := String.intercalate "\n" <| ensemble.tables.zipIdx.map fun (_, index) =>
    s!"            {index} => component_{index}_interactions(row),"
  return s!"{prelude}\n{String.intercalate "\n\n" components}\n\npub struct {name};\n\nimpl<F: WitnessField> Program<F> for {name} \{\n    const FUEL: usize = {config.fuel};\n    const COMPONENTS: usize = {ensemble.tables.length};\n\n    fn modes() -> Vec<Mode<F>> \{ vec![{modes}] }\n\n    fn complete_row(component: usize, input: &[F]) -> Result<Vec<F>, String> \{\n        match component \{\n{completeCases}\n            _ => Err(format!(\"component index \{component} is out of bounds\")),\n        }\n    }\n\n    fn interactions(component: usize, row: &[F]) -> Vec<Interaction<F>> \{\n        match component \{\n{interactionCases}\n            _ => vec![],\n        }\n    }\n\n    fn verifier_interactions(public_input: &[F]) -> Vec<Interaction<F>> \{\n        {verifier}\n    }\n}\n\npub fn generate<F: WitnessField>(public_input: &[F]) -> Result<EnsembleWitness<F>, String> \{\n    clean_backend::witness_generation::generate::<F, {name}>(public_input)\n}\n"

end Air.Flat.WitnessGeneration.Rust
