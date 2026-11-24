import LoweringFixtures.Common

/-! A trash body using a query another closure registered, `x * a.rot(1)`: Rust's trash bodies are
not walked, and a kept expression already has its index, so Rust keys it. Lean adds the atom to the
gate's queries without registering anything. -/
namespace LoweringFixtures.AdditiveKeptQuery
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let q ← selector false
  let q2 ← selector false
  gate "keeper" q do
    let y ← advice a 1
    return #[("", y)]
  additiveGate "kept trash" q2 do
    let x ← advice b
    return #[("", Rust.mul x (.var (.advice ⟨a⟩ 1)))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 0 witness,
    .enableGate (cleanGate (source.trashcans[0]?.getD ⟨"", ⟨1, false⟩, #[], #[], false, false⟩)) 0]]

#guard source.adviceQueries == #[(0, 1), (1, 0)]

end LoweringFixtures.AdditiveKeptQuery
