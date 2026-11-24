import LoweringFixtures.Common

/-! A folded-away factor carrying a selector, `x + 0 * (q2 * a.rot(5))`: Rust folds it before the
walk and keys the gate. `pruneFolded` erases the factor's query and keeps `q2`, so Lean keys it. -/
namespace LoweringFixtures.WalkedFoldedSelector
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector false
  let q2 ← selector false
  gate "dropped" q do
    let x ← advice a
    return #[("", .add x (Rust.mul (.const 0) (Rust.mul (querySelector q2) (.var (.advice ⟨a⟩ 5)))))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard source.adviceQueries == #[(0, 0)]

end LoweringFixtures.WalkedFoldedSelector
