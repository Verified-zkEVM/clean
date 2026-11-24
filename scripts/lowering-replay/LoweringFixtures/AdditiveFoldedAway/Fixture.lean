import LoweringFixtures.Common

/-! A trash body `x + 0 * a.rot(5)` with `a.rot(5)` an index-free `query_cell`. Rust's `*` folds the
factor before anything reads it, so the unwalked trash body never needs its index and Rust keys the
gate; `additiveGate` prunes the factor as `gate` does. -/
namespace LoweringFixtures.AdditiveFoldedAway
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector false
  additiveGate "folded trash" q do
    let x ← advice a
    return #[("", .add x (Rust.mul (.const 0) (.var (.advice ⟨a⟩ 5))))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard source.adviceQueries == #[(0, 0)]

end LoweringFixtures.AdditiveFoldedAway
