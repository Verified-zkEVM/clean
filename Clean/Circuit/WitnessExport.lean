import Clean.Circuit.Json
import Clean.Circuit.Formal

/-!
# Witness-generation export (witgen IR plan, phase 6)

Two pieces:

1. **Exportability checking** — `#assert_exportable c` fails (with the locations of the
   offending operations) if any witness generator reachable from `c` is a `.native`
   closure. Since the witness IR is plain data, this is a *runtime* check (an `#eval`
   under the hood): no expression-level normalization is involved, so it is immune to
   the `whnf`-timeout problems that sank the PR #401 spike.

2. **Serialization** — `ToJson`-style encoders for the witness IR, mirroring the
   constraint export conventions in `Clean/Circuit/Json.lean` (tagged `{"type": ...}`
   objects, field elements as their `ℕ` values). `Operations.witgenJson?` produces the
   payload a Rust witgen interpreter consumes: the flat operation list with each
   witness op carrying its IR program. Serialization is `Except`-valued and fails on
   `.native` witnesses.

Trust note: a wrong Rust witgen is a completeness bug, not a soundness bug — the
serialized IR is differentially tested against the Lean reference interpreter
(`Circuit.witgen`, phase 3), not verified.
-/

open Lean

namespace Witgen

variable {F : Type}

/-! ## Exportability -/

/-- A witness program is exportable iff it is structured IR (`.native` closures are
the migration escape hatch and cannot be serialized). -/
def WitgenIR.exportable {m : ℕ} : WitgenIR F m → Bool
  | .native _ => false
  | .ir _ _ _ => true

/-- Indices (into the flat operation list) of witness operations that are not
exportable. Empty iff all reachable witness generators are structured IR. -/
def unexportableWitnesses (ops : List (FlatOperation F)) : List ℕ :=
  (ops.zipIdx.filter fun (op, _) =>
    match op with
    | .witness _ code => !code.exportable
    | _ => false).map (·.2)

/-! ## Serialization -/

variable [ToJson F]

mutual

def FExpr.toJson : FExpr F → Json
  | .expr e => Json.mkObj [("type", "expr"), ("expr", Lean.toJson e)]
  | .envGet i => Json.mkObj [("type", "envGet"), ("index", i.toJson)]
  | .const c => Json.mkObj [("type", "const"), ("value", Lean.toJson c)]
  | .localVar i => Json.mkObj [("type", "localVar"), ("index", Lean.toJson i)]
  | .add x y => Json.mkObj [("type", "add"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .mul x y => Json.mkObj [("type", "mul"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .inv x => Json.mkObj [("type", "inv"), ("arg", x.toJson)]
  | .ofNat n => Json.mkObj [("type", "ofNat"), ("arg", n.toJson)]
  | .ite c t e => Json.mkObj [("type", "ite"),
      ("cond", c.toJson), ("then", t.toJson), ("else", e.toJson)]
  | .arrGet xs i => Json.mkObj [("type", "arrGet"),
      ("array", Lean.toJson xs), ("index", i.toJson)]
  | .dataGet key n row col => Json.mkObj [("type", "dataGet"),
      ("table", Lean.toJson key), ("width", Lean.toJson n),
      ("row", row.toJson), ("col", Lean.toJson col.val)]
  | .hintGet key n row col => Json.mkObj [("type", "hintGet"),
      ("table", Lean.toJson key), ("width", Lean.toJson n),
      ("row", row.toJson), ("col", Lean.toJson col.val)]

def NExpr.toJson : NExpr F → Json
  | .const n => Json.mkObj [("type", "const"), ("value", Lean.toJson n)]
  | .val x => Json.mkObj [("type", "val"), ("arg", x.toJson)]
  | .idx => Json.mkObj [("type", "idx")]
  | .localVar i => Json.mkObj [("type", "localVar"), ("index", Lean.toJson i)]
  | .add x y => Json.mkObj [("type", "add"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .mul x y => Json.mkObj [("type", "mul"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .div x y => Json.mkObj [("type", "div"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .mod x y => Json.mkObj [("type", "mod"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .land x y => Json.mkObj [("type", "and"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .lor x y => Json.mkObj [("type", "or"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .lxor x y => Json.mkObj [("type", "xor"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .shiftL x y => Json.mkObj [("type", "shiftLeft"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .shiftR x y => Json.mkObj [("type", "shiftRight"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .ite c t e => Json.mkObj [("type", "ite"),
      ("cond", c.toJson), ("then", t.toJson), ("else", e.toJson)]

def BExpr.toJson : BExpr F → Json
  | .feq x y => Json.mkObj [("type", "eq"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .lt x y => Json.mkObj [("type", "lt"), ("lhs", x.toJson), ("rhs", y.toJson)]
  | .not b => Json.mkObj [("type", "not"), ("arg", b.toJson)]

end

instance : ToJson (FExpr F) := ⟨FExpr.toJson⟩
instance : ToJson (NExpr F) := ⟨NExpr.toJson⟩
instance : ToJson (BExpr F) := ⟨BExpr.toJson⟩

def VExpr.toJson : VExpr F → Json
  | .lit es => Json.mkObj [("type", "elements"), ("elements", Lean.toJson es)]
  | .mapRange n body => Json.mkObj [("type", "mapRange"),
      ("n", Lean.toJson n), ("body", body.toJson)]
  | .append a b => Json.mkObj [("type", "append"),
      ("left", a.toJson), ("right", b.toJson)]

instance : ToJson (VExpr F) := ⟨VExpr.toJson⟩

def Step.toJson : Step F → Json
  | .letF e => Json.mkObj [("sort", "field"), ("value", Lean.toJson e)]
  | .letN e => Json.mkObj [("sort", "nat"), ("value", Lean.toJson e)]

instance : ToJson (Step F) := ⟨Step.toJson⟩

/-- Serialize a witness program; fails on `.native`. -/
def WitgenIR.toJson? {m : ℕ} : WitgenIR F m → Except String Json
  | .native _ => .error "witness program contains a native (closure) witness"
  | .ir steps out _ => .ok <| Json.mkObj [
      ("steps", Lean.toJson steps),
      ("output", out.toJson)]

end Witgen

/-! ## Operation-level export -/

variable {F : Type} [FiniteField F] [ToJson F] {α : Type}

/-- Serialize a flat operation including its witness program (unlike the basic
`ToJson (FlatOperation F)` instance, which drops it). Fails on native witnesses. -/
def FlatOperation.witgenJson? : FlatOperation F → Except String Json
  | .witness m code => do
    let codeJson ← code.toJson?
    return Json.mkObj [("witness", toJson m), ("code", codeJson)]
  | op => .ok (toJson op)

/--
Serialize the operations of a circuit for an external witgen implementation:
the flattened operation list, each witness op carrying its IR program.
-/
def Operations.witgenJson? (ops : Operations F) : Except String Json := do
  let flat := ops.toFlat
  match Witgen.unexportableWitnesses flat with
  | [] => pure ()
  | bad => throw s!"witness operations at flat indices {bad} are native closures; port them to witness IR (or keep using the Lean reference interpreter)"
  let opsJson ← flat.mapM FlatOperation.witgenJson?
  return Json.mkObj [
    ("version", 1),
    ("localLength", toJson (FlatOperation.localLength flat)),
    ("operations", Json.arr opsJson.toArray)]

/-! ## Dispatch for the user-facing commands

`WitgenOps` resolves "the operations of `c`" for plain circuits and the formal circuit
wrappers (instantiating formal circuits with input variables at offset 0, operations
starting after the input, as in completeness statements). -/

class WitgenOps (C : Type) (F : outParam Type) [FiniteField F] where
  operations : C → Operations F

instance : WitgenOps (Circuit F α) F :=
  ⟨(·.operations 0)⟩

instance {Input Output : TypeMap} [ProvableType Input] [CircuitType Output] :
    WitgenOps (FormalCircuitBase F Input Output) F :=
  ⟨fun c => (c.main (varFromOffset Input 0)).operations (size Input)⟩

instance {Input Output : TypeMap} [ProvableType Input] [ProvableType Output] :
    WitgenOps (FormalCircuit F Input Output) F :=
  ⟨fun c => (c.main (varFromOffset Input 0)).operations (size Input)⟩

instance {Input : TypeMap} [ProvableType Input] :
    WitgenOps (FormalAssertion F Input) F :=
  ⟨fun c => (c.main (varFromOffset Input 0)).operations (size Input)⟩

instance {Input Output : TypeMap} [ProvableType Input] [ProvableType Output] :
    WitgenOps (GeneralFormalCircuit F Input Output) F :=
  ⟨fun c => (c.main (varFromOffset Input 0)).operations (size Input)⟩

namespace WitgenExport

/-- Runtime check behind `#assert_exportable`. -/
def check {C : Type} {F : Type} [FiniteField F] [WitgenOps C F] (c : C) : IO Unit := do
  let flat := (WitgenOps.operations (F := F) c).toFlat
  match Witgen.unexportableWitnesses flat with
  | [] => IO.println s!"exportable ✓ ({FlatOperation.localLength flat} witness cells)"
  | bad =>
    throw (IO.userError s!"not exportable: witness operations at flat indices {bad} are native closures")

/-- Runtime serializer behind `#witgen_json`. -/
def jsonString {C : Type} {F : Type} [FiniteField F] [ToJson F] [WitgenOps C F]
    (c : C) : IO String := do
  match (WitgenOps.operations (F := F) c).witgenJson? with
  | .ok j => return j.pretty
  | .error e => throw (IO.userError e)

end WitgenExport

/-- Fails if any witness generator reachable from the given circuit (or formal circuit)
is a `.native` closure; succeeds with the witness cell count otherwise. -/
macro "#assert_exportable " c:term : command =>
  `(#eval WitgenExport.check $c)

/-- Pretty-print the witgen export JSON of the given circuit (or formal circuit). -/
macro "#witgen_json " c:term : command =>
  `(#eval do IO.println (← WitgenExport.jsonString $c))
