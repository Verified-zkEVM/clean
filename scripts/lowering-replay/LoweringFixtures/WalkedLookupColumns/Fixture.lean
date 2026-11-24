import LoweringFixtures.Common

/-! Lookups whose atoms no closure made, over several columns and parallel tuples.
`batched_lookup_any` walks column by column, each column's parallel inputs then its table
(circuit.rs:1757-1771); `batched_lookup` queries its table columns in the closure first. A query
repeated across columns is registered once, at its first visit. -/
namespace LoweringFixtures.WalkedLookupColumns
open Halo2 Midnight Midnight.Keygen

def adv (c : Nat) (r : Int) : E := .var (.advice ⟨c⟩ r)
def fix (c : Nat) (r : Int) : E := .var (.fixed ⟨c⟩ r)

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _ ← adviceColumn
  let _ ← fixedColumn
  let t0 ← fixedColumn
  let t1 ← fixedColumn
  let q ← selector false
  batchedLookupAny "grid" q do
    let x ← advice a 9
    return #[(#[adv 1 3, Rust.mul x (adv 0 2)], fix 0 4),
      (#[adv 0 2, adv 1 (-3)], Rust.sub (fix 0 1) (adv 1 3))]
  batchedLookup "tables" none do
    return #[(#[adv 1 5, adv 0 7], t1), (#[Rust.scale (adv 1 6) 2, adv 1 5], t0)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 6
  ops := [.loadTable ⟨⟨1⟩⟩ [0, 1], .loadTable ⟨⟨2⟩⟩ [0, 1],
    .region "r" ((List.range 12).flatMap fun r => [.assignAdvice ⟨0⟩ r witness, .assignAdvice ⟨1⟩ r witness])]

#guard source.adviceQueries == #[(0, 9), (1, 3), (0, 2), (1, -3), (1, 5), (0, 7), (1, 6)]
#guard source.fixedQueries == #[(0, 4), (0, 1), (2, 0), (1, 0)]

end LoweringFixtures.WalkedLookupColumns
