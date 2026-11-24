import LoweringFixtures.Common

/-! Two gates named "twin" with equal query lists: the first queries `x, y, z` in
its closure and returns `z + y + x`; the second queries only `x` and uses `y`, `z` index-free. Rust
allows the shared name and registers `x, y, z` in the first closure's order. -/
namespace LoweringFixtures.WalkedTwinGates
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  let q ← selector false
  gate "twin" q do
    let x ← advice a
    let y ← advice b
    let z ← advice c
    return #[("", .add (.add z y) x)]
  gate "twin" q do
    let x ← advice a
    return #[("", Rust.mul (.add (.var (.advice ⟨b⟩ 0)) (.var (.advice ⟨c⟩ 0))) x)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨2⟩ 0 witness]]

#guard source.adviceQueries == #[(0, 0), (1, 0), (2, 0)]
#guard (source.gates.map (·.queries)) == #[#[.advice ⟨0⟩ 0, .advice ⟨1⟩ 0, .advice ⟨2⟩ 0],
  #[.advice ⟨0⟩ 0, .advice ⟨1⟩ 0, .advice ⟨2⟩ 0]]

end LoweringFixtures.WalkedTwinGates
