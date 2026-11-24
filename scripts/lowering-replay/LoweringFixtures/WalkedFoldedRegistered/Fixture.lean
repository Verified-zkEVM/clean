import LoweringFixtures.Common

/-! A query only under a folded-away factor that some other closure registers: `x + 0 * a.rot(5)`
before a gate querying `a.rot(5)`, and `x + 0 * b.rot(1)` after one that did; a lookup input
`y + 0 * a.rot(6)` registered later. Rust's walk skips each, the registrations come from the other
closures, so Rust keys it; Lean should derive the same key. -/
namespace LoweringFixtures.WalkedFoldedRegistered
open Halo2 Midnight Midnight.Keygen

def adv (c : Nat) (r : Int) : E := .var (.advice ⟨c⟩ r)

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  gate "early" q do
    let y ← advice b 1
    return #[("", Rust.mul y y)]
  gate "folded" q do
    let x ← advice a
    return #[("later", .add x (Rust.mul (.const 0) (adv a 5))), ("earlier", .add x (Rust.mul (adv b 1) (.const 0)))]
  batchedLookup "folded input" q do
    let y ← advice b
    return #[(#[.add y (Rust.mul (.const 0) (adv a 6))], t)]
  gate "late" q do
    let z ← advice a 5
    let w ← advice a 6
    return #[("", Rust.mul z w)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" ((List.range 8).flatMap fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness])]

#guard source.adviceQueries == #[(1, 1), (0, 0), (1, 0), (0, 5), (0, 6)]

end LoweringFixtures.WalkedFoldedRegistered
