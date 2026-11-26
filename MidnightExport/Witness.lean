import MidnightExport.Export
import Clean.Circuit.WitnessExport
import Midnight.Math.Witness.Fast
import Midnight.Math.Witness.Operations
import Midnight.SHA256.WitnessInitial
import Std.Data.TreeMap

/-! The witness program of a SHA-256 contract circuit, for a prover without Lean
(`scripts/vk-export --witgen`, Rust's `examples/prove.rs`): `witgen.json` holds the contract's
flattened assignments (`Operations.assignments`) at the key's placement. The export first runs the
contract's `dependencies` check (`Fast.ordered`): it admits only programs over the message hint and
earlier assignments, which is all a prover needs to interpret.

For each message it also evaluates them in Lean into `prove/HEX/witness.json`, a cross-check for
Rust's interpreter. Written cells are kept in a tree: `Execute.run`'s closure chain reads in
linear time. -/

namespace Midnight.Export.Witness
open Lean Halo2 Midnight.Keygen Midnight.Chips Midnight.Math.Witness

attribute [local instance] lexOrd

abbrev Cells := Std.TreeMap (Nat × Nat × Int) F

/-- `Fast.ordered` admits reads of earlier assignments only, so no other cell is read. -/
def environment (cells : Cells) (usableRows : Nat) (hint : ProverHint F) : ProverEnvironment F where
  get column row := cells.getD (Fast.key (column, row)) 0
  usableRows := usableRows
  hint := hint

/-- `Execute.run`, returning the written cells. -/
def run (place : RegionIndex → Nat) (usableRows : Nat) (hint : ProverHint F)
    (assignments : List (Execute.Assignment F)) : Cells :=
  assignments.foldl (init := ∅) fun cells a =>
    cells.insert (Fast.key a.destination) (a.program.eval ⟨place, environment cells usableRows hint⟩)[0]

mutual

private def fExprToJson [ToJson F] (enc : AssignedCell F → Json) : FExpr F → Json
  | .expr e => Json.mkObj [("type", "expr"), ("expr", enc e)]
  | .const c => Json.mkObj [("type", "const"), ("value", Lean.toJson c)]
  | .localVar i => Json.mkObj [("type", "localVar"), ("index", Lean.toJson i)]
  | .add x y => Json.mkObj [("type", "add"), ("lhs", fExprToJson enc x), ("rhs", fExprToJson enc y)]
  | .mul x y => Json.mkObj [("type", "mul"), ("lhs", fExprToJson enc x), ("rhs", fExprToJson enc y)]
  | .inv x => Json.mkObj [("type", "inv"), ("arg", fExprToJson enc x)]
  | .ofU64 n => Json.mkObj [("type", "ofU64"), ("arg", u64ExprToJson enc n)]
  | .ite c t e => Json.mkObj [("type", "ite"),
      ("cond", bExprToJson enc c), ("then", fExprToJson enc t), ("else", fExprToJson enc e)]
  | .listGet xs i => Json.mkObj [("type", "listGet"),
      ("items", Json.arr (fExprListToJson enc xs).toArray), ("index", u64ExprToJson enc i)]
  | .dataGet key n row col => Json.mkObj [("type", "dataGet"),
      ("table", Lean.toJson key), ("width", Lean.toJson n),
      ("row", u64ExprToJson enc row), ("col", Lean.toJson col.val)]
  | .hintGet key n row col => Json.mkObj [("type", "hintGet"),
      ("table", Lean.toJson key), ("width", Lean.toJson n),
      ("row", u64ExprToJson enc row), ("col", Lean.toJson col.val)]

private def fExprListToJson [ToJson F] (enc : AssignedCell F → Json) : List (FExpr F) → List Json
  | [] => []
  | x :: xs => fExprToJson enc x :: fExprListToJson enc xs

private def u64ExprToJson [ToJson F] (enc : AssignedCell F → Json) : U64Expr F → Json
  | .const n => Json.mkObj [("type", "const"), ("value", Lean.toJson n.toNat)]
  | .val x => Json.mkObj [("type", "val"), ("arg", fExprToJson enc x)]
  | .idx => Json.mkObj [("type", "idx")]
  | .localVar i => Json.mkObj [("type", "localVar"), ("index", Lean.toJson i)]
  | .add x y => Json.mkObj [("type", "add"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .mul x y => Json.mkObj [("type", "mul"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .div x y => Json.mkObj [("type", "div"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .mod x y => Json.mkObj [("type", "mod"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .land x y => Json.mkObj [("type", "and"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .lor x y => Json.mkObj [("type", "or"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .lxor x y => Json.mkObj [("type", "xor"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .shiftL x y => Json.mkObj [("type", "shiftLeft"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .shiftR x y => Json.mkObj [("type", "shiftRight"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .ite c t e => Json.mkObj [("type", "ite"),
      ("cond", bExprToJson enc c), ("then", u64ExprToJson enc t), ("else", u64ExprToJson enc e)]

private def bExprToJson [ToJson F] (enc : AssignedCell F → Json) : BExpr F → Json
  | .true => Json.mkObj [("type", "true")]
  | .false => Json.mkObj [("type", "false")]
  | .feq x y => Json.mkObj [("type", "eq"), ("lhs", fExprToJson enc x), ("rhs", fExprToJson enc y)]
  | .neq x y => Json.mkObj [("type", "u64Eq"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .lt x y => Json.mkObj [("type", "u64Lt"), ("lhs", u64ExprToJson enc x), ("rhs", u64ExprToJson enc y)]
  | .flt x y => Json.mkObj [("type", "lt"), ("lhs", fExprToJson enc x), ("rhs", fExprToJson enc y)]
  | .bit x i => Json.mkObj [("type", "bit"), ("arg", fExprToJson enc x), ("bit", Lean.toJson i)]
  | .not b => Json.mkObj [("type", "not"), ("arg", bExprToJson enc b)]
  | .and x y => Json.mkObj [("type", "and"), ("lhs", bExprToJson enc x), ("rhs", bExprToJson enc y)]

end

/-- An assignment as `[kind, column, row, program]`, in upstream Clean's expression schema with
cells at absolute rows and constants as decimal strings. -/
def assignmentJson (place : RegionIndex → Nat) (a : Execute.Assignment F) : Except String Json := do
  let .ir [] (.lit es) := a.program | throw "witness program outside the admitted fragment"
  let some e := es.toList.head? | throw "empty witness program"
  letI : ToJson F := ⟨fun c => toString (scalarNat c)⟩
  let cell (c : AssignedCell F) :=
    let (kind, column, row) := Fast.key (Execute.address place c)
    Json.mkObj [("kind", kind), ("column", column), ("row", row)]
  let (kind, column, row) := Fast.key a.destination
  return Json.arr #[kind, column, row, fExprToJson cell e]

def parseMessage (hex : String) : Except String SHA256.Spec.Message := do
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw s!"message {hex}: not lowercase hex"
  let cs := hex.toList
  unless cs.length = 48 do throw s!"message {hex}: not 24 bytes"
  let bytes ← (List.range 24).mapM fun i => return 16 * (← digit cs[2 * i]!) + (← digit cs[2 * i + 1]!)
  return Vector.ofFn fun i => bytes[i.val]!

/-- `OUT/witgen.json`, then `OUT/prove/HEX/witness.json` for each message HEX (every advice
assignment as `[column, absolute row, value]`, in order). `contract` is the contract's own
placement when it uses this planner, so `contract_placement` says whether the witness is the
contract's `generated`. -/
def main (source : CS) (k : Nat) (ops : Operations F) (planner : Layout.Planner) (contract : Option (List Nat))
    (args : List String) : IO UInt32 := do
  let out :: hexes := args | throw (IO.userError "usage: OUT_DIR HEX...")
  let out : System.FilePath := out
  let messages ← hexes.mapM fun hex => return (hex, ← IO.ofExcept (parseMessage hex))
  let start ← IO.monoMsNow
  let starts := (layout source ops k planner).regionStarts
  let place : RegionIndex → Nat := fun region => starts.toArray[region]!
  let assignments := Math.Witness.Operations.assignments place ops 0
  unless Fast.ordered place ∅ assignments do throw (IO.userError "witness assignments are not dependency-ordered")
  -- Rust's stream may add an instance read before an otherwise unassigned instance-copied cell.
  unless (Math.Witness.Operations.assignments place (Canonical.rustOps source ops) 0).map (·.destination) ==
      assignments.map (·.destination) do
    throw (IO.userError "the key's stream assigns cells the contract's does not")
  let usableRows := 2 ^ k - source.blindingFactors - 1
  for (column, row) in assignments.map (·.destination) do
    if column.kind == .advice && (column.index ≥ source.numAdvice || row < 0 || row.toNat ≥ usableRows) then
      throw (IO.userError s!"advice cell {column.index} {row} outside {source.numAdvice} columns, {usableRows} rows")
  let placement := if contract == some starts then "same" else "differs"
  let program ← IO.ofExcept (assignments.toArray.mapM (assignmentJson place))
  IO.FS.writeFile (out / "witgen.json") (Json.mkObj [
    ("schema", "midnight-vk-export-witgen-v1"), ("region_starts", toJson starts), ("contract_placement", placement),
    ("hint", Json.mkObj [("key", SHA256.Semantics.Preimage.hintKey), ("width", 24)]),
    ("assignments", Json.arr program)]).compress
  let planned ← IO.monoMsNow
  IO.println s!"witgen: {assignments.length} assignments, contract placement {placement}, exported in {planned - start} ms"
  for (hex, message) in messages do
    let t0 ← IO.monoMsNow
    let digest := SHA256.Spec.digest message
    let cells := run place usableRows (SHA256.WitnessInitial.hintFor message) assignments
    let advice := assignments.filterMap fun a =>
      let (column, row) := a.destination
      if column.kind == .advice then
        some (Json.arr #[column.index, row, toString (scalarNat (cells.getD (Fast.key (column, row)) 0))])
      else none
    let t1 ← IO.monoMsNow
    let dir := out / "prove" / hex
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "witness.json") (Json.mkObj [
      ("schema", "midnight-vk-export-witness-v1"), ("message", toJson message.toArray), ("digest", toJson digest.toArray),
      ("region_starts", toJson starts), ("contract_placement", placement), ("advice", Json.arr advice.toArray),
      ("ms", Json.mkObj [("witness", t1 - t0)])]).compress
    IO.println s!"witness {hex}: {advice.length} advice cells in {t1 - t0} ms"
  return 0

end Midnight.Export.Witness
