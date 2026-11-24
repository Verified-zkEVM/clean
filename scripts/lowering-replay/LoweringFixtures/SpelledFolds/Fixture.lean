import LoweringFixtures.Common

/-! Rust's operators on every folding operand, sent as spellings so Rust builds them: `-` and `+`
with zero on either side, `-(-0)`, `*` by 0 and 1 on either side, `-Constant(1)` against
`Constant(-1)`, `* F` by 0 and 1 (never folded), a simple selector folded away before `-` and `+`,
a body folding to `Constant(0)` (so `q * 0`) and nesting; in owned and `rows` gates, a raw gate,
`None` and `Some` lookups and a trash argument. -/
namespace LoweringFixtures.SpelledFolds
open Halo2 Midnight Midnight.Keygen Export.Replay

def a : Spelling := .atom (.var (.advice ⟨0⟩ 0))
def b : Spelling := .atom (.var (.advice ⟨1⟩ 0))
def b1 : Spelling := .atom (.var (.advice ⟨1⟩ 1))
def f : Spelling := .atom (.var (.fixed ⟨0⟩ 0))
def qs : Spelling := .atom (querySelector ⟨0, true⟩)
def qc : Spelling := .atom (querySelector ⟨1, false⟩)

def bodies : List (String × Spelling) := [
  ("sub zero", .sub a (.const 0)),
  ("zero sub", .sub (.const 0) b),
  ("sub", .sub a b),
  ("sub negated zero", .sub a (.neg (.const 0))),
  ("zero plus", .add (.const 0) b1),
  ("plus zero", .add b1 (.const 0)),
  ("one times", .mul (.const 1) f),
  ("times one", .mul f (.const 1)),
  ("times zero in sum", .add b (.mul a (.const 0))),
  ("zero times in sum", .add (.mul (.const 0) a) b1),
  ("times negated one", .mul a (.neg (.const 1))),
  ("times minus one", .mul a (.const (-1))),
  ("scale zero", .scale a 0),
  ("scale one", .scale b 1),
  ("selector folded before sub", .sub (.mul qs (.const 0)) b1),
  ("selector folded before add", .add b1 (.mul (.const 0) qs)),
  ("nested", .sub (.mul (.sub a (.const 0)) (.add (.const 0) b1)) (.scale (.neg f) 3)),
  ("zero body", .mul (.sub a a) (.const 0)),
  ("constant body", .mul (.const 2) (.const 3))]

def raw : Spelling := .mul qs (.sub (.add a (.const 0)) (.mul b (.const 1)))
def trash : List Spelling := [.add (.mul b1 (.const 0)) a, .add (.neg (.const 0)) (.scale a 0)]
def anyInput : Spelling := .sub (.add a (.const 0)) (.const 0)
def anyTable : Spelling := .add f (.mul b (.const 0))
def someInput : Spelling := .mul (.scale b 5) (.const 1)
def someTable : Spelling := .sub (.const 0) (.neg f)

def configure : ConfigM Unit := do
  let ca ← adviceColumn
  let cb ← adviceColumn
  let cf ← fixedColumn
  let _ ← selector
  let q ← selector false
  gate "bodies" q do
    let _ ← advice ca
    let _ ← advice cb
    let _ ← advice cb 1
    let _ ← fixed cf
    return (bodies.map fun (name, s) => (name, s.toE)).toArray
  gateWithoutSelector "raw" do
    let _ ← advice ca
    let _ ← advice cb
    return #[("raw", raw.toE)]
  lookupAny "none" none do
    let _ ← advice ca
    let _ ← advice cb
    let _ ← fixed cf
    return #[(anyInput.toE, anyTable.toE)]
  lookupAny "some" q do
    let _ ← advice cb
    let _ ← fixed cf
    return #[(someInput.toE, someTable.toE)]
  additiveGate "trash" q do
    let _ ← advice ca
    let _ ← advice cb 1
    return (trash.map fun s => ("", s.toE)).toArray

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
    .assignFixed ⟨0⟩ 0 7, .enableGate (cleanGate (spec 0)) 0, .enableGate (cleanGate (spec 1)) 1]]
  spellings := bodies.map (·.2) ++ raw :: trash ++ [anyInput, anyTable, someInput, someTable]

end LoweringFixtures.SpelledFolds
