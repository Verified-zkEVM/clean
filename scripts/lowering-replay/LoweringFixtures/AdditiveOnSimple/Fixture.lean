import LoweringFixtures.Common

/-! An additive gate on a simple selector that also owns an ordinary gate: Rust's finalization
asserts the trash selector is not simple (circuit.rs:2032), Lean's `validate` rejects it. -/
namespace LoweringFixtures.AdditiveOnSimple
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let qs ← selector
  gate "bool" qs do
    let x ← advice a
    return #[("bool", Rust.mul x x - x)]
  additiveGate "trash on simple" qs do
    let x ← advice a 1
    return #[("x", x)]

def source : CS := (configure.run {}).2

def empty : GateSpec := ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate (source.gates[0]?.getD empty)) 0,
    .enableGate (cleanGate (source.trashcans[0]?.getD empty)) 0]]

#guard !source.validate.isOk

end LoweringFixtures.AdditiveOnSimple
