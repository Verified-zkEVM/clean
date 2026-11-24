import MidnightExport.Export
import Midnight.Chips.Canonical

/-! The lowering replay harness's Lean half (`scripts/lowering-replay`). It exports what a
circuit is before lowering: the constraint system with each gate's closure query order, and
the Clean operation stream per region at region-relative offsets. Rust replays both through
the real `ConstraintSystem` and `Layouter` APIs and does its own placement, constant
allocation and copy recording. Lean's own lowering (region starts, fixed matrix, selector
rows, copies, key) of `Canonical.rustOps`, Rust's reading of the stream, is exported next to it
for the comparison. -/

namespace Midnight.Export.Replay
open Lean Halo2 Midnight.Keygen Midnight.Chips

/-- An expression as a chip writes it with Rust's operators. `toE` is its `Rust` spelling; the
replay sends the spelling itself, so Rust's own operators fold it and decide its simple-selector
panics, and the pinned comparison checks Lean's erasure and folding against them. -/
inductive Spelling where
  | atom (e : E)
  | const (c : F)
  | add (a b : Spelling)
  | sub (a b : Spelling)
  | mul (a b : Spelling)
  | neg (a : Spelling)
  | scale (a : Spelling) (c : F)

def Spelling.toE : Spelling → E
  | .atom e => e
  | .const c => .const c
  | .add a b => .add a.toE b.toE
  | .sub a b => Rust.sub a.toE b.toE
  | .mul a b => Rust.mul a.toE b.toE
  | .neg a => Rust.neg a.toE
  | .scale a c => Rust.scale a.toE c

/-- The atoms a spelling names, including those its `Rust` spelling folds out of `toE`. -/
def Spelling.atoms : Spelling → List Query
  | .atom e => e.queryAtoms
  | .const _ => []
  | .add a b | .sub a b | .mul a b => a.atoms ++ b.atoms
  | .neg a | .scale a _ => a.atoms

/-- One replay fixture: a configured source CS, its operation stream and the domain. Expressions
equal to some `spellings` entry's `toE` are sent as that spelling, each entry at least once. -/
structure Fixture where
  source : CS
  ops : Operations F
  k : Nat
  architecture : Architecture := SHA256.architecture
  spellings : List Spelling := []

private def kindName : ColumnKind → String
  | .advice => "advice"
  | .fixed => "fixed"
  | .instance => "instance"

private def scalar (x : F) : Json := toString (scalarNat x)

def queryJson : Query → Json
  | .selector s => Json.arr #["sel", s.index]
  | .advice c r => Json.arr #["advice", c.index, r]
  | .fixed c r => Json.arr #["fixed", c.index, r]
  | .instance c r => Json.arr #["instance", c.index, r]

def cellJson (c : Cell) : Json :=
  Json.arr #[c.regionIndex, c.rowOffset, kindName c.column.kind, c.column.index]

def regionOpJson : RegionOperation F → Json
  | .assignAdvice column row _ => Json.arr #["advice", column.index, row]
  | .assignFixed column row value => Json.arr #["fixed", column.index, row, scalar value]
  | .enableGate gate row => Json.arr #["gate", gate.selector.index, row, gate.name]
  | .enableLookup _ enabled row => Json.arr #["lookup", toJson (enabled.map (·.index)), row]
  | .constrainEqual left right => Json.arr #["equal", cellJson left, cellJson right]
  | .constrainConstant cell value => Json.arr #["constant", cellJson cell, scalar value]
  | .constrainInstance cell column row => Json.arr #["instance", cellJson cell, column.index, row]

def opJson : Operation F → Json
  | .region name body => Json.mkObj [("region", name), ("ops", Json.arr (body.map regionOpJson).toArray)]
  | .constrainInstance cell column row =>
      Json.mkObj [("instance", Json.arr #[cellJson cell, column.index, row])]
  | .loadTable table values =>
      Json.mkObj [("table", table.inner.index), ("values", Json.arr (values.map scalar).toArray)]

def spellingJson (s : CS) : Spelling → Except String Json
  | .atom e => exprJson s (s.rich e)
  | .const c => pure (Json.arr #["const", scalar c])
  | .add a b => return Json.arr #["add", ← spellingJson s a, ← spellingJson s b]
  | .sub a b => return Json.arr #["sub", ← spellingJson s a, ← spellingJson s b]
  | .mul a b => return Json.arr #["mul", ← spellingJson s a, ← spellingJson s b]
  | .neg a => return Json.arr #["neg", ← spellingJson s a]
  | .scale a c => return Json.arr #["scale", ← spellingJson s a, scalar c]

/-- An expression as sent: the tree the builder returned (before `pruneFolded`), as its spelling if
`spellings` has one, else as Lean's erased tree. -/
def expressionJson (s : CS) (spellings : List Spelling) (e : E) : Except String Json :=
  let e := ((s.prunedFrom.find? (·.1 == e)).map (·.2)).getD e
  match spellings.find? (·.toE == e) with
  | some spelled => spellingJson s spelled
  | none => exprJson s (s.rich e)

/-- The queries each gate's closure made, `walked` for gates and not for trash batches: the first
unused record of its name and queries, so of same-named twins each gets its own. The rest of its
`queries` Rust's `query_cells` registers. -/
def gateClosures (s : CS) (gates : Array GateSpec) (walked : Bool) : Array (Array Query) := Id.run do
  let mut unused := s.gateClosures.filter (·.2.2.2 == walked)
  let mut out := #[]
  for g in gates do
    match unused.findIdx? fun (name, queries, _) => name == g.name && queries == g.queries with
    | some j =>
      out := out.push (unused[j]?.map (·.2.2.1) |>.getD g.queries)
      unused := unused.eraseIdxIfInBounds j
    | none => out := out.push g.queries
  return out

/-- A gate or additive gate as its Rust closure: the queries in call order, then the
constraint polynomials, without the selector that `Constraints` applies unless `raw`
(`without_selector`). -/
def gateJson (s : CS) (spellings : List Spelling) (g : GateSpec) (closure : Array Query) :
    Except String Json := do
  return Json.mkObj [("name", g.name), ("selector", g.selector.index), ("raw", g.raw),
    ("queries", Json.arr (closure.map queryJson)),
    ("constraints", Json.arr (← g.constraints.mapM fun (name, p) =>
      return Json.mkObj [("name", name), ("poly", ← expressionJson s spellings p)]))]

private def sameLookup (a b : BatchedLookup) : Bool :=
  a.name == b.name && decide (a.selector = b.selector) && decide (a.inputs = b.inputs) &&
    decide (a.table = b.table)

/-- Each lookup's recorded closure, matched by value, each record used once. A lookup no builder
made queries nothing in its closure and is `any` unless its table is bare fixed columns. -/
def lookupClosures (s : CS) : Array (Array Query × Bool) := Id.run do
  let mut unused := s.lookupClosures
  let mut out := #[]
  for l in s.lookups do
    match (unused.findIdx? (sameLookup l ·.1)).bind fun j => unused[j]?.map (j, ·) with
    | some (j, _, closure) =>
      out := out.push closure
      unused := unused.eraseIdxIfInBounds j
    | none => out := out.push (#[], !l.table.all fun e => (tableColumn? e).isSome)
  return out

/-- Indices into `CS.lookupClosures` of each lookup's value-equal records. Value equality cannot
tell twins apart after a hand edit, so `schedule.py` chooses among them. -/
def lookupCandidates (s : CS) : Array (Array Nat) :=
  s.lookups.map fun l => (s.lookupClosures.zipIdx.filter (sameLookup l ·.1.1)).map (·.2)

/-- A lookup as its Rust closure: the queries in call order, then the batch. `any` is
`batched_lookup_any`, whose table expressions the closure builds. -/
def lookupJson (s : CS) (spellings : List Spelling) (l : BatchedLookup) (closure : Array Query × Bool)
    (candidates : Array Nat) : Except String Json := do
  let expr := expressionJson s spellings
  return Json.mkObj [("name", l.name), ("any", closure.2), ("candidates", toJson candidates),
    ("queries", Json.arr (closure.1.map queryJson)),
    ("selector", ← expr l.selector),
    ("inputs", Json.arr (← l.inputs.mapM fun row => return Json.arr (← row.mapM expr))),
    ("table", Json.arr (← l.table.mapM expr))]

/-- `s` with every query its expressions use registered, so each erases to a node naming its column
and rotation: Rust builds walked atoms from those alone, and a query only in a factor Rust folds away
is never registered (`WalkedFoldedAway`), nor one `Rust.sub` drops from a spelling. Only
expressions are exported against it. -/
def withAtoms (s : CS) (spellings : List Spelling) : CS :=
  let atoms := ((s.gates ++ s.trashcans).toList.flatMap (·.constraints.toList.map (·.2)) ++
    s.lookups.toList.flatMap (fun l => l.selector :: l.table.toList ++ l.inputs.toList.flatMap Array.toList) ++
    s.prunedFrom.toList.map (·.2)).flatMap Halo2.Expression.queryAtoms ++ spellings.flatMap (·.atoms)
  let add := fun (xs : Array (Nat × Int)) (x : Nat × Int) => if xs.contains x then xs else xs.push x
  atoms.foldl (init := s) fun s q => match q with
    | .advice c r => { s with adviceQueries := add s.adviceQueries (c.index, r) }
    | .fixed c r => { s with fixedQueries := add s.fixedQueries (c.index, r) }
    | .instance c r => { s with instanceQueries := add s.instanceQueries (c.index, r) }
    | .selector _ => s

def csJson (s : CS) (spellings : List Spelling := []) : Except String Json := do
  let pairs := fun (xs : Array (Nat × Int)) => Json.arr (xs.map fun (c, r) => Json.arr #[c, r])
  let sx := withAtoms s spellings
  return Json.mkObj [
    ("num_advice", s.numAdvice), ("num_fixed", s.numFixed), ("num_instance", s.numInstance),
    ("selectors", toJson ((Array.range s.numSelectors).map s.selectorSimple)),
    ("advice_queries", pairs s.adviceQueries), ("fixed_queries", pairs s.fixedQueries),
    ("instance_queries", pairs s.instanceQueries),
    ("permutation", Json.arr (s.permutation.map fun c => Json.arr #[kindName c.kind, c.index])),
    ("constants", toJson s.constantColumns), ("minimum_degree", toJson s.minimumDegree),
    -- An empty gate is `additiveGate`'s entry, which the trash closure makes.
    ("gates", Json.arr (← (do
      let gates := s.gates.filter (!·.constraints.isEmpty)
      (gates.zip (gateClosures s gates true)).mapM fun (g, c) => gateJson sx spellings g c))),
    ("trashcans", Json.arr (← (s.trashcans.zip (gateClosures s s.trashcans false)).mapM
      fun (g, c) => gateJson sx spellings g c)),
    ("lookups", Json.arr (← ((s.lookups.zip (lookupClosures s)).zip (lookupCandidates s)).mapM
      fun ((l, c), k) => lookupJson sx spellings l c k)),
    ("lookup_closures", Json.arr (s.lookupClosures.map fun (_, queries, any) =>
      Json.mkObj [("queries", Json.arr (queries.map queryJson)), ("any", any)])),
    ("rejected_lookups", Json.arr (← s.rejectedLookups.mapM fun (name, sel, columns, any) => do
      let expr := fun e => exprJson s (s.rich e)
      return Json.mkObj [("name", name), ("any", any), ("selector", ← expr sel),
        ("columns", Json.arr (← columns.mapM fun (xs, t) =>
          return Json.arr #[Json.arr (← xs.mapM expr), ← expr t]))]))]

section Admission

instance (counts : ConfigureCounts) (start usable : Nat) :
    DecidablePred (OperationsLawful.InstructionValid counts start usable) := fun op => by
  cases op <;> dsimp [OperationsLawful.InstructionValid] <;> infer_instance

instance (counts : ConfigureCounts) (usable : Nat) :
    DecidablePred (OperationsLawful.TableValid counts usable) := fun op => by
  cases op <;> dsimp [OperationsLawful.TableValid] <;> infer_instance

/-- `OperationsLawful.ActivationClosed`. Its `∈ body` is not decidable (advice carries witness
programs), so membership is matched on the region's enable operations, indexed by row. -/
def activationClosed (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (body : RegionOperations F) : Bool :=
  let enables : Std.HashMap Nat (List (RegionOperation F)) := body.foldl (fun m op =>
    match op with
    | .enableGate _ row | .enableLookup _ _ row => m.insert row (op :: m.getD row [])
    | _ => m) {}
  (OperationsLawful.localActivations body).all fun (active, row) =>
    let here := enables.getD row []
    gates.all (fun gate => gate.constraints.isEmpty || gate.selector.index != active ||
      here.any fun | .enableGate g _ => decide (g = gate) | _ => false) &&
    lookups.all (fun lookup => lookup.masterSelector.index != active ||
      here.any fun | .enableLookup l _ _ => decide (l = lookup) | _ => false)

/-- `CopyLawful.ConstantsPlaced` on Rust's `usize` constants pass. -/
def constantsPlaced (plan : Usize.Plan) (usable : Nat) : Bool :=
  plan.placed && plan.constants.all (·.2.2 < usable)

/-- `CopyLawful.CopyValid`, rows mod 2^64. -/
def copyValid (permutation : List AnyColumn) (starts : List Nat) (usable : Nat) :
    DeclaredCopy F → Bool
  | (.cell cell, .constant _) => endpoint (.cell cell)
  | (left, right) => endpoint left && endpoint right
where
  endpoint : CopyEndpoint F → Bool
    | .cell c => permutation.contains c.column && c.regionIndex < starts.length &&
        Usize.wrap (Halo2.Layout.place starts c.regionIndex + c.rowOffset) < usable
    | .instance column row => permutation.contains column.toAny && row < usable
    | .constant _ => true

/-- `OperationsLawful.InstructionValid`, rows mod 2^64. -/
def instructionValid (counts : ConfigureCounts) (start usable : Nat) : RegionOperation F → Bool
  | .assignAdvice column _ _ => column.index < counts.numAdviceColumns
  | .assignFixed column row _ => column.index < counts.numFixedColumns && Usize.wrap (start + row) < usable
  | .enableGate gate row => gate.selector.index < counts.numSelectors && Usize.wrap (start + row) < usable
  | .enableLookup lookup enabled row =>
      decide (enabled = [lookup.masterSelector.toSelector]) &&
      lookup.masterSelector.index < counts.numSelectors && Usize.wrap (start + row) < usable
  | _ => true

/-- The certificate's `copies` and `operations` fields over the decided configuration, its row
bounds read on Rust's `usize` lowering (`Usize`): they differ only where Rust's arithmetic wraps,
which the certificate's `Nat` bounds reject. -/
def certificateRejections (fx : Fixture) (c : CS.Checked) (planner : Layout.Planner) : List String :=
  let delta := c.toCleanDelta
  let usable := (CertifiedCircuit.layoutConfig fx.source fx.k).usableRows
  let plan := (Usize.plan planner fx.source.constantColumn fx.ops).toOption.getD ⟨[], [], true⟩
  let starts := plan.starts
  let permutation := (CertifiedCircuit.permutationColumns fx.source).map Halo2.Layout.ColRef.toAny
  let regions := (indexedRegions fx.ops 0).1
  let check := fun (ok : Bool) (message : String) => if ok then [] else [message]
  check (CopyLawful.plannerLaidOut planner fx.ops)
    "copies: an endpoint names a region not yet laid out (Rust: index out of bounds on `regions`)" ++
  check (CopyLawful.registered fx.ops delta.gates delta.lookups
      (CertifiedCircuit.fixedColumns fx.source) permutation)
    "copies: an enabled gate or lookup, fixed column or copied column is not configured (KeygenRegistered)" ++
  check (constantsPlaced plan usable)
    "copies: a deferred constant without a constants column or position (Rust: NotEnoughColumnsForConstants) or past the usable rows" ++
  check ((operationDeclaredCopies fx.ops).all (copyValid permutation starts usable))
    "copies: an endpoint is outside the equality columns, the regions or the usable rows" ++
  check (regions.all fun (region, body) => region < starts.length &&
      body.all fun op => instructionValid fx.source.counts (starts.getD region 0) usable op)
    "operations: an assignment or enable is out of bounds, or a lookup enable is not exactly its master selector" ++
  check (regions.all fun (_, body) => activationClosed delta.gates delta.lookups body)
    "operations: an enabled selector's gate or lookup is not enabled at that row (ActivationClosed)" ++
  check (fx.ops.all fun op => decide (OperationsLawful.TableValid fx.source.counts usable op))
    "operations: a table is out of bounds or leaves no default row (TableValid)" ++
  check (decide (OperationsLawful.tableColumns fx.ops).Nodup)
    "operations: a table column is loaded twice (Rust: UsedColumn)" ++
  check (regions.all fun (region, body) => OperationsLawful.instanceCopiesLocal region body)
    "operations: an in-region instance copy is not of an advice cell its region assigns"

/-- Lean's admission: configuration validation, the decided certificate fields (for
`Canonical.rustOps` of the stream) and the layout bounds the certificate proves. Empty when Lean
admits. -/
def rejections (fx : Fixture) (planner : Layout.Planner := .simple) :
    List String :=
  let errs := fun (e : Except String Unit) => match e with | .ok _ => [] | .error m => [m]
  errs fx.source.validate ++
  errs (checkLayout fx.source fx.ops fx.k planner) ++
  match Canonical.checked? fx.source with
  | none => ["configuration: not WellFormed"]
  | some c => certificateRejections { fx with ops := Canonical.rustOps fx.source fx.ops } c planner

end Admission

def derivedJson (fx : Fixture) (l : Layout.DerivedLayout) : Json :=
  let fixed := Id.run do
    let mut cells : Array Json := #[]
    for column in [0:fx.source.numFixed] do
      for (value, row) in (l.fixed[column]?.getD #[]).zipIdx do
        if value != 0 then cells := cells.push (Json.arr #[column, row, toString value])
    return cells
  Json.mkObj [("region_starts", toJson l.regionStarts), ("fixed", Json.arr fixed),
    ("selector_rows", toJson l.selectorRows),
    ("copies", Json.arr (l.copies.toArray.map fun (a, b, c, d) => Json.arr #[a, b, c, d]))]

/-- Writes `replay.json` (the pre-lowering circuit) and `lean.json` (Lean's lowering, its
admission verdict and, when the configuration validates, its key on the Filecoin setup). `v1`
lowers with Rust's V1 planner, and Rust replays under it. -/
def main (fx : Fixture) (args : List String) : IO UInt32 := do
  let (out, assets, planner) ← match args with
    | [out, assets] => pure (out, assets, Layout.Planner.simple)
    | [out, assets, "v1"] => pure (out, assets, v1 fx.source)
    | _ => throw (IO.userError "usage: OUT_DIR ASSETS_DIR [v1]")
  let out : System.FilePath := out
  let start ← IO.monoMsNow
  let expressions := (fx.source.gates ++ fx.source.trashcans).toList.flatMap (·.constraints.toList.map (·.2)) ++
    fx.source.lookups.toList.flatMap (fun l => l.selector :: l.table.toList ++ l.inputs.toList.flatMap Array.toList) ++
    fx.source.prunedFrom.toList.map (·.2)
  unless fx.spellings.all (fun sp => expressions.any (sp.toE == ·)) &&
      (fx.spellings.map (·.toE)).eraseDups.length == fx.spellings.length do
    throw (IO.userError "a spelling matches no expression of the configuration, or two spell one")
  IO.FS.writeFile (out / "replay.json") (Json.mkObj [
    ("schema", "midnight-lowering-replay-v1"), ("k", fx.k),
    ("planner", match planner with | .simple => "simple" | .v1 _ => "v1"),
    ("architecture", architectureJson fx.architecture), ("public_inputs", (publicInputCount fx.ops).toNat),
    ("cs", ← IO.ofExcept (csJson fx.source fx.spellings)),
    ("ops", Json.arr (fx.ops.map opJson).toArray)]).compress
  let l := layout fx.source fx.ops fx.k planner
  let rejected := rejections fx planner
  let laid ← IO.monoMsNow
  let srsName := s!"bls_filecoin_2p{if fx.k ≤ 13 then 13 else 19}"
  let key ← match fx.source.validate with
    | .error m => pure (Except.error m)
    | .ok _ => do
      let srs ← readSrs ((assets : System.FilePath) / srsName) fx.k
      pure (deriveVK fx.architecture fx.k planner fx.ops fx.source l.fixed l.copies srs)
  let derived ← IO.monoMsNow
  let keyField := match key with
    | .ok key => ("key", keyJson key fx.source.finalize)
    | .error m => ("key_error", Json.str m)
  IO.FS.writeFile (out / "lean.json") (Json.pretty (Json.mkObj [
    ("schema", "midnight-lowering-lean-v1"), ("k", fx.k), ("srs", srsName),
    ("admitted", rejected.isEmpty), ("rejections", toJson rejected),
    ("derived", derivedJson fx l), keyField,
    ("ms", Json.mkObj [("layout", laid - start), ("derive", derived - laid)])]))
  IO.println s!"lean: admitted {rejected.isEmpty}, layout {laid - start} ms, key {derived - laid} ms"
  return 0

end Midnight.Export.Replay
