import LoweringFixtures.Common

/-! The folded-away case in a lookup: input `y + 0 * a.rot(6)` with `a.rot(6)`
never registered. Rust folds it away before the walk and keys the lookup; `pushLookup` prunes it. -/
namespace LoweringFixtures.WalkedFoldedAwayLookup
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  batchedLookup "folded input" q do
    let y ← advice a
    return #[(#[.add y (Rust.mul (.const 0) (.var (.advice ⟨a⟩ 6)))], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1], .region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard source.adviceQueries == #[(0, 0)]

end LoweringFixtures.WalkedFoldedAwayLookup
