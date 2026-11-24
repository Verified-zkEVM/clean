import LoweringFixtures.Common

/-! A simple selector inside an additive body: Rust's finalization asserts trash expressions hold
no simple selector (circuit.rs:1990-1993), and `validate` rejects it. -/
namespace LoweringFixtures.AdditiveSimpleBody
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector false
  let qs ← selector
  additiveGate "simple inside" q do
    let x ← advice a
    return #[("x", Rust.mul (querySelector qs) x)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness,
    .enableGate (cleanGate (source.trashcans[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩)) 0]]

#guard !source.validate.isOk

end LoweringFixtures.AdditiveSimpleBody
