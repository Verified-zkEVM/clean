import Midnight.Configuration
import Midnight.Keygen.Normalize
import Midnight.Keygen.DebugEscape
import Lean.Data.Json.FromToJson.Basic

/-! Midnight-specific constraint-system metadata: LogUp degree and chunk counts, the
native blinding formula, the uncompressed selector-to-fixed `finalize`, executable
input validation and the Rust `Debug`/JSON serializers. Gate polynomials are Clean's
`Halo2.Expression`; the serializers run upstream's VK-boundary erasure `Halo2.eraseExpr`
against the recorded query layouts and print the resulting Rust node shapes. -/

namespace Midnight.Keygen
open Lean
open Halo2 (Expression RichExpression QueryState)

private def insertUnique {α : Type} [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

/-- Rust's `usize::next_power_of_two`, including its value at zero. -/
def nextPowerOfTwo (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 2 ^ ((n - 1).log2 + 1)

/-- A polynomial as Rust's operators build it: erased to Rust's node shapes, then folded.
Folding and degrees do not depend on query indices, so no layout is needed. -/
def rustExpr (e : E) : RichExpression F := (Halo2.eraseExpr e {}).normalize

def rustDegree (e : E) : Nat := (rustExpr e).degree

private def richSelectors : RichExpression F → List Nat
  | .selector i => [i]
  | .negated a | .scaled a _ => richSelectors a
  | .sum a b | .product a b => richSelectors a ++ richSelectors b
  | _ => []

/-- What Rust's `contains_simple_selector` sees: a simple selector left after folding. -/
def _root_.Halo2.Expression.foldedSimple (e : E) : Bool :=
  e.hasSimple && (richSelectors (rustExpr e)).any fun i =>
    e.queryAtoms.any fun | .selector q => q.simple && q.index == i | _ => false

/-- Rust's operators panic on a simple selector on either side of `+` or `-`, or on both sides of
`*` (circuit.rs:1194-1272), looking at the operands as already folded. -/
def _root_.Halo2.Expression.simpleSafe : E → Bool
  | .add a b => a.simpleSafe && b.simpleSafe && !a.foldedSimple && !b.foldedSimple
  | .mul a b => a.simpleSafe && b.simpleSafe && !(a.foldedSimple && b.foldedSimple)
  | _ => true

/-- `Constraints::with_selector`: Rust's `q * poly`, which folds a literal body;
`without_selector`: the body. -/
def GateSpec.polyDegree (g : GateSpec) (p : E) : Nat :=
  if g.raw then rustDegree p else
  (RichExpression.foldMul (.selector g.selector.index) (rustExpr p)).degree

/-- Rust's `unwrap_or(1)` makes a batch of no tuples degree 1 (logup.rs:231). -/
def BatchedLookup.inputDegree (l : BatchedLookup) : Nat :=
  if l.inputs.isEmpty then 1 else
  l.inputs.foldl (fun d row => row.foldl (fun d e => max d (rustDegree e)) d) 0

def BatchedLookup.chunkCapacity (l : BatchedLookup) (degree : Nat) : Nat :=
  nextPowerOfTwo (degree - 1) / l.inputDegree

def BatchedLookup.degree (l : BatchedLookup) (degree : Nat) : Nat :=
  let helper := l.chunkCapacity degree * l.inputDegree + 1
  let table := l.table.foldl (fun d e => max d (rustDegree e)) 0
  let accumulator := 2 + rustDegree l.selector + table
  nextPowerOfTwo (max helper accumulator - 1) + 1

def BatchedLookup.numChunks (l : BatchedLookup) (degree : Nat) : Nat :=
  let chunk := l.chunkCapacity degree
  (l.inputs.size + chunk - 1) / chunk

def CS.degree (s : CS) : Nat :=
  let trashDegree := s.trashcans.foldl
    (fun d g => g.constraints.foldl (fun d (_, e) => max d (rustDegree e)) (max d 2))
    (max 3 (s.minimumDegree.getD 0))
  let withoutLookup := s.gates.foldl
    (fun d g => g.constraints.foldl (fun d (_, p) => max d (g.polyDegree p)) d) trashDegree
  s.lookups.foldl (fun d l => max d (l.degree withoutLookup)) withoutLookup

/-- Midnight's blinding-row count, including advice queries, additive arguments,
LogUp helper chunks and the protocol's three extra margins. -/
def CS.blindingFactors (s : CS) : Nat :=
  let adviceMax := (Array.range s.numAdvice).foldl
    (fun acc c => max acc ((s.adviceQueries.filter (·.1 == c)).size)) 3
  adviceMax + s.trashcans.size + (s.lookups.map (·.numChunks s.degree)).foldl (· + ·) 0 + 3

def CS.finalize (s : CS) : CS :=
  if s.selectorFixedStart.isSome then s else
  let replace := Expression.replaceSelectors s.numFixed
  { s with
    numFixed := s.numFixed + s.numSelectors
    numSelectors := 0
    selectorFixedStart := some s.numFixed
    fixedQueries := s.fixedQueries ++
      (Array.range s.numSelectors).map fun i => (s.numFixed + i, 0)
    -- Keep raw gate specs for Clean semantics; export substitutes selectors.
    lookups := s.lookups.map fun l => { l with
      selector := replace l.selector
      inputs := l.inputs.map (·.map replace)
      table := l.table.map replace } }

private def unique {α : Type} [BEq α] (xs : Array α) : Bool :=
  (xs.foldl insertUnique #[]).size == xs.size

private def rotationFitsRust (r : Int) : Bool :=
  decide (-2147483648 ≤ r ∧ r ≤ 2147483647)

private def CS.sourceSelectorCount (s : CS) : Nat :=
  match s.selectorFixedStart with
  | none => s.numSelectors
  | some start => s.numFixed - start

private def CS.registered (s : CS) : Halo2.Query → Bool
  | .selector q => q.index < s.sourceSelectorCount
  | .advice c r => c.index < s.numAdvice && s.adviceQueries.contains (c.index, r)
  | .fixed c r => c.index < s.numFixed && s.fixedQueries.contains (c.index, r)
  | .instance c r => c.index < s.numInstance && s.instanceQueries.contains (c.index, r)

private def CS.registersExpr (s : CS) : E → Bool
  | .var q => s.registered q
  | .const _ => true
  | .add a b | .mul a b => s.registersExpr a && s.registersExpr b

/-- Rust's `<str as Debug>` body of a string (rustc 1.90.0, midnight-zk's toolchain): the ASCII
escapes, and `\u{..}` for control characters, DEL and the non-ASCII characters of
`debugEscapedRanges`. -/
def debugEscape (name : String) : String :=
  name.foldl (init := "") fun out c =>
    out ++ match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\t' => "\\t" | '\r' => "\\r" | '\n' => "\\n"
      | '\x00' => "\\0"
      | c => if c.toNat < 32 || c.toNat == 127 || debugEscaped c.toNat then
          "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}" else c.toString

/-- Check the supported configuration fragment before using total serialization
or degree helpers. Reject missing registrations instead of inventing query order.
Both source configurations and the mixed raw-gate/finalized-lookup representation
returned by `finalize` are accepted. Unblinded advice is refused by the frontend
(`Frontend.unblindedAdviceColumn`): its blinding differs and the key cannot show it. This is executable input validation, not a circuit/protocol soundness theorem. -/
def CS.validate (s : CS) : Except String Unit := do
  unless s.errors.isEmpty do
    throw (String.intercalate "; " s.errors.toList)
  if let some start := s.selectorFixedStart then
    unless start ≤ s.numFixed && s.numSelectors == 0 do
      throw "invalid finalized selector metadata"
    unless (Array.range s.sourceSelectorCount).all
        (fun i => s.fixedQueries.contains (start + i, 0)) do
      throw "missing finalized selector query"
  for (name, count, queries) in [
      ("advice", s.numAdvice, s.adviceQueries),
      ("fixed", s.numFixed, s.fixedQueries),
      ("instance", s.numInstance, s.instanceQueries)] do
    unless unique queries && queries.all (fun (c, r) => c < count && rotationFitsRust r) do
      throw s!"invalid or duplicate {name} query registration"
  unless unique s.permutation do
    throw "duplicate permutation column"
  unless unique s.constantColumns && s.constantColumns.all (fun column =>
      column < s.numFixed && s.permutation.contains ⟨.fixed, column⟩) do
    throw "invalid, duplicate or equality-disabled constant column"
  for c in s.permutation do
    let q := match c.kind with
      | .advice => Halo2.Query.advice ⟨c.index⟩ 0
      | .fixed => Halo2.Query.fixed ⟨c.index⟩ 0
      | .instance => Halo2.Query.instance ⟨c.index⟩ 0
    unless s.registered q do
      throw "permutation column is out of bounds or lacks its zero-rotation query"
  for g in s.gates ++ s.trashcans do
    unless g.selectorUses.all (·.index < s.sourceSelectorCount) && g.valid &&
        g.queries.all s.registered do
      throw s!"gate {g.name}: invalid selector, queries, or constraint declarations"
    unless g.polynomials.all (·.simpleSafe) do
      throw s!"gate {g.name}: Rust's operators panic on this use of a simple selector"
  unless s.trashcans.all (fun g => !g.raw) do
    throw "additive gates take with_selector bodies"
  -- Finalization asserts no simple selector in a folded trash body (circuit.rs:1990-1993, 2031-2036).
  unless s.trashcans.all (fun g => g.constraints.all fun (_, p) => !p.foldedSimple) do
    throw "additive gate: a simple selector in its body"
  unless s.trashcans.all (fun g => !g.selector.simple) do
    throw "additive gates require complex selectors"
  unless s.trashcans.all (fun g => !g.constraints.isEmpty) do
    throw "additive gates require nonempty constraint bodies"
  let gateSelectors := ((s.gates ++ s.trashcans).toList.flatMap (·.selectorUses)).toArray
  let lookupSelectors := s.lookups.toList.flatMap fun l =>
    match s.selectorFixedStart, l.selector with
    | none, _ => l.selectorAtoms
    | some start, .var (.fixed c _) => [⟨c.index - start, false⟩]
    | some _, _ => []
  let selectors := gateSelectors ++ lookupSelectors.toArray
  unless selectors.all (fun q => selectors.all fun r => q.index != r.index || q.simple == r.simple) do
    throw "inconsistent selector kinds"
  for l in s.lookups do
    let validSelector := match s.selectorFixedStart, l.selector with
      | none, .var (.selector q) => !q.simple && q.index < s.numSelectors
      | some start, .var (.fixed c r) => start ≤ c.index && c.index < s.numFixed && r == 0
      | _, .const c => c == 1
      | _, _ => false
    unless validSelector && s.registersExpr l.selector do
      throw s!"lookup {l.name}: invalid selector"
    -- Rust asserts no simple selector in each folded input and table (circuit.rs:1759-1767).
    let expr := fun (e : E) => e.simpleSafe && !e.foldedSimple && s.registersExpr e
    unless !l.table.isEmpty && l.table.all expr &&
        l.inputs.all (fun row => row.size == l.table.size && row.all expr) do
      throw s!"lookup {l.name}: invalid shape, simple selector or expression queries"
    unless l.inputDegree > 0 && l.chunkCapacity s.degree > 0 do
      throw s!"lookup {l.name}: unsupported zero input degree or chunk capacity"

/-- The configure-recorded query layouts, as the start state of upstream's query walk.
No layout is extended here: Midnight registers every query at configure time. -/
def CS.queryState (s : CS) : QueryState :=
  ⟨s.adviceQueries, s.fixedQueries, s.instanceQueries⟩

def CS.outputExpr (s : CS) (e : E) : E :=
  match s.selectorFixedStart with
  | some start => e.replaceSelectors start
  | none => e

/-- Upstream's VK-boundary erasure of one polynomial into Rust's node shapes, with query
indices resolved against the recorded layouts. -/
def CS.rich (s : CS) (e : E) : RichExpression F :=
  Halo2.eraseExpr (s.outputExpr e) s.queryState

/-- The configured kind of a selector; `CS.WellFormed.selectorKinds` makes it unique. An unused
selector has its kind as created. -/
def CS.selectorSimple (s : CS) (index : Nat) : Bool :=
  match ((s.gates ++ s.trashcans).toList.flatMap (·.selectorUses) ++
      s.lookups.toList.flatMap (·.selectorAtoms)).find? (·.index == index) with
  | some q => q.simple
  | none => s.selectorKinds[index]?.getD false

private def layoutEntry (layout : Array (Nat × Int)) (index : Nat) : Nat × Int :=
  layout[index]?.getD (0, 0)

private def debugList (items : Array String) : String :=
  "[" ++ String.intercalate ", " items.toList ++ "]"

def scalarDebug (x : F) : String :=
  let digits := Nat.toDigits 16 x.val
  "Fq(0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits) ++ ")"

private def kindDebug : Halo2.ColumnKind → String
  | .advice => "Advice"
  | .fixed => "Fixed"
  | .instance => "Instance"

private def columnDebug (k : Halo2.ColumnKind) (index : Nat) : String :=
  "Column { index: " ++ toString index ++ ", column_type: " ++ kindDebug k ++ " }"

private def queryNodeDebug (kind : String) (layout : Array (Nat × Int)) (index : Nat) : String :=
  let (column, rotation) := layoutEntry layout index
  kind ++ " { query_index: " ++ toString index ++ ", column_index: " ++ toString column ++
    ", rotation: Rotation(" ++ toString rotation ++ ") }"

/-- Exact Rust `Debug` of one erased polynomial. -/
def CS.richDebug (s : CS) : RichExpression F → String
  | .constant c => "Constant(" ++ scalarDebug c ++ ")"
  | .selector index => s!"Selector(Selector({index}, {s.selectorSimple index}))"
  | .advice index => queryNodeDebug "Advice" s.adviceQueries index
  | .fixed index => queryNodeDebug "Fixed" s.fixedQueries index
  | .instance index => queryNodeDebug "Instance" s.instanceQueries index
  | .negated a => "Negated(" ++ s.richDebug a ++ ")"
  | .sum a b => "Sum(" ++ s.richDebug a ++ ", " ++ s.richDebug b ++ ")"
  | .product a b => "Product(" ++ s.richDebug a ++ ", " ++ s.richDebug b ++ ")"
  | .scaled a c => "Scaled(" ++ s.richDebug a ++ ", " ++ scalarDebug c ++ ")"

/-- Rust's `Debug` of a lookup or trash expression, which finalization has rebuilt through
Rust's operators. -/
def CS.exprDebug (s : CS) (e : E) : String := s.richDebug (s.rich e).normalize

/-- Rust's `Debug` of a gate polynomial: `q * poly` with Rust's operators (a `without_selector`
body as it is), then rebuilt. -/
def CS.gateDebug (s : CS) (g : GateSpec) (p : E) : String :=
  if g.raw then s.exprDebug p else
  s.richDebug (RichExpression.foldMul (s.rich (.var (.selector g.selector))) (s.rich p).normalize)

private def queryDebug (kind : Halo2.ColumnKind) (query : Nat × Int) : String :=
  "(" ++ columnDebug kind query.1 ++ ", Rotation(" ++ toString query.2 ++ "))"

/-- Exact non-pretty Rust `Debug` serialization of the pinned CS. Names of gates
and constraints are intentionally absent: `PinnedGates` flattens their polynomials.
`batched_lookup_any` prefixes each lookup name with its ordinal. -/
def CS.pinnedDebug (s : CS) : String :=
  let expr := s.exprDebug
  let gates := s.gates.flatMap fun g => g.constraints.map fun (_, p) => s.gateDebug g p
  let lookups := s.lookups.mapIdx fun i l =>
    "BatchedArgument { name: \"lookup #" ++ toString (i + 1) ++ ": " ++ debugEscape l.name ++
      "\", selector: " ++ expr l.selector ++
      ", input_expressions: " ++ debugList (l.inputs.map fun batch => debugList (batch.map expr)) ++
      ", table_expressions: " ++ debugList (l.table.map expr) ++ " }"
  let trash := s.trashcans.mapIdx fun i g =>
    "Argument { argument_index: " ++ toString i ++ ", selector: " ++
      expr (.var (.selector g.selector)) ++ ", constraint_expressions: " ++
      debugList (g.constraints.map fun (_, p) => expr p) ++ " }"
  "PinnedConstraintSystem { num_fixed_columns: " ++ toString s.numFixed ++
    ", num_advice_columns: " ++ toString s.numAdvice ++
    ", num_instance_columns: " ++ toString s.numInstance ++
    ", num_selectors: " ++ toString s.numSelectors ++
    ", gates: " ++ debugList gates ++
    ", advice_queries: " ++ debugList (s.adviceQueries.map (queryDebug .advice)) ++
    ", instance_queries: " ++ debugList (s.instanceQueries.map (queryDebug .instance)) ++
    ", fixed_queries: " ++ debugList (s.fixedQueries.map (queryDebug .fixed)) ++
    ", permutation: Argument { columns: " ++
      debugList (s.permutation.map fun c => columnDebug c.kind c.index) ++ " }" ++
    ", lookups: " ++ debugList lookups ++
    ", trashcans: " ++ debugList trash ++ ", constants: " ++
      debugList (s.constantColumns.map (columnDebug .fixed)) ++ ", minimum_degree: " ++
      (match s.minimumDegree with | some d => s!"Some({d})" | none => "None") ++ " }"

/-! Rust's expression operators spelled in `E`, so that every tree a chip builds with them is
expressible. Erasure reads `mul (const (-1)) e` as `Negated`, `mul e (const c)` as `Scaled`
and `mul e (mul (const c) (const 1))` as `Product(e, Constant(c))`; a leading `1 *` folds away
and keeps an operand out of those readings. `+` is `.add`; a literal is `.const`. -/
namespace Rust

/-- `-a`, which never folds. -/
def neg (a : E) : E := .mul (.const (-1)) a

/-- `a * c` for a scalar `c` (`Mul<F>`): `Scaled`, which never folds. -/
def scale (a : E) (c : F) : E := .mul (.mul (.const 1) a) (.const c)

/-- `a * b`. Both operands sit under `1 *`: a bare right operand `-Constant(1)` would otherwise
read as the marker for `Constant(-1)`. -/
def mul (a b : E) : E := .mul (.mul (.const 1) a) (.mul (.const 1) b)

/-- `a - b`: `-b` when `a` is zero, `a` when `b` is, else `a + (-b)`. Rust panics on a simple
selector before it folds (circuit.rs:1235), so then the `Sum` stays for `validate` to reject. -/
def sub (a b : E) : E :=
  if a.foldedSimple || b.foldedSimple then .add a (neg b)
  else if rustExpr a = .constant 0 then neg b
  else if rustExpr b = .constant 0 then a
  else .add a (neg b)

end Rust

end Midnight.Keygen
