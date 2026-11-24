import LoweringFixtures.Common

/-! `q * x - Constant(0)` and `Constant(0) - q * x` with simple `q`, sent as spellings so Rust's own
`-` panics before it folds the zero operand (circuit.rs:1235); `Rust.sub` keeps the `Sum` and
`validate` rejects it. -/
namespace LoweringFixtures.SimpleSubZero
open Halo2 Midnight Midnight.Keygen Export.Replay

def x : E := .var (.advice ⟨0⟩ 0)
def q : E := querySelector ⟨0, true⟩

def right : Spelling := .sub (.mul (.atom q) (.atom x)) (.const 0)
def left : Spelling := .sub (.const 0) (.mul (.atom q) (.atom x))

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _ ← selector
  gateWithoutSelector "sub zero" do
    let _ ← advice a
    return #[("right", right.toE), ("left", left.toE)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]
  spellings := [right, left]

#guard source.gates.all fun g => g.constraints.all fun (_, p) => !p.simpleSafe
#guard !source.validate.isOk

end LoweringFixtures.SimpleSubZero
