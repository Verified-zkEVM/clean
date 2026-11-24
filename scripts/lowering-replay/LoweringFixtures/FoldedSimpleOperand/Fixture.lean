import LoweringFixtures.Common

/-! Simple-selector operands that Rust's `*` folds to `Constant(0)` before the next operator checks
for simple selectors (circuit.rs:1194-1272): `x - qs * 0`, `(qs * 0) + y` in `with_selector` bodies
and `(qs * 0) * (qs * x)` beside `qs * y` in an owned `without_selector` gate. Rust keys all three,
and so does Lean: `simpleSafe` and `Rust.sub` read the folded operands, so `x - qs * 0` is `x`. Sent
as spellings, so Rust's operators make those decisions. -/
namespace LoweringFixtures.FoldedSimpleOperand
open Halo2 Midnight Midnight.Keygen Export.Replay

def x : Spelling := .atom (.var (.advice ⟨0⟩ 0))
def y : Spelling := .atom (.var (.advice ⟨1⟩ 0))
def y1 : Spelling := .atom (.var (.advice ⟨1⟩ 1))
def qs : Spelling := .atom (querySelector ⟨0, true⟩)
def qsZero : Spelling := .mul qs (.const 0)

def sub : Spelling := .sub x qsZero
def zero : Spelling := .mul qsZero (.mul qs x)
def own : Spelling := .mul qs y1
def add : Spelling := .add qsZero y

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let _ ← selector
  let qc ← selector false
  gate "sub" qc do
    let _ ← advice a
    return #[("", sub.toE)]
  gateWithoutSelector "mul" do
    let _ ← advice a
    let _ ← advice b 1
    return #[("zero", zero.toE), ("own", own.toE)]
  gate "add" qc do
    let _ ← advice b
    return #[("", add.toE)]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
    .enableGate (cleanGate (spec 0)) 0, .enableGate (cleanGate (spec 2)) 0, .enableGate (cleanGate (spec 1)) 0]]
  spellings := [sub, zero, own, add]

#guard source.gates.map (·.rows) == #[false, false, true]

end LoweringFixtures.FoldedSimpleOperand
