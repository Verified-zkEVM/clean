import LoweringFixtures.Common

/-! A lookup closure that queries `b` before `a` but returns `a`'s input first. A Rust chip
writing the same closure registers advice queries [b, a], as Lean does. -/
namespace LoweringFixtures.LookupClosureOrder
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t0 ← fixedColumn
  let t1 ← fixedColumn
  let ql ← selector false
  batchedLookup "swap" ql do
    let y ← advice b
    let x ← advice a
    return #[(#[x], t0), (#[y], t1)]

def source : CS := (configure.run {}).2

def swap : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1], .loadTable ⟨⟨1⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .enableLookup (cleanLookup swap) [⟨0, false⟩] 0]]

end LoweringFixtures.LookupClosureOrder
