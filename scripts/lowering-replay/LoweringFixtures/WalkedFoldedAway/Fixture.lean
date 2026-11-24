import LoweringFixtures.Common

/-! `x + Constant(0) * a.rot(5)`: Rust's `*` folds the query away before `create_gate` walks the
body, so it is never registered, and Rust keys the gate. `gate` prunes the factor (`pruneFolded`), so
Lean derives the same key; the replay sends Rust the unpruned tree. -/
namespace LoweringFixtures.WalkedFoldedAway
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector
  gate "dropped" q do
    let x ← advice a
    return #[("", .add x (Rust.mul (.const 0) (.var (.advice ⟨a⟩ 5))))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard source.adviceQueries == #[(0, 0)]

end LoweringFixtures.WalkedFoldedAway
