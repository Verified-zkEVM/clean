import LoweringFixtures.Common

/-! Region indices with tables interleaved (tables are not regions): layouter instance copies
right after a table, naming the last region at offsets past its height, and unassigned copy and
constant endpoints of earlier regions that fall in later regions' rows. -/
namespace LoweringFixtures.CopyTableInterleaved
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let c ← fixedColumn
  let t ← fixedColumn
  let u ← fixedColumn
  let i ← instanceColumn
  let q1 ← selector false
  let q2 ← selector false
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.fixed, f⟩
  enableEquality ⟨.instance, i⟩
  batchedLookup "t" q1 do
    let x ← advice a
    return #[(#[x], t)]
  batchedLookup "u" q2 do
    let x ← advice a
    return #[(#[x], u)]
  enableConstant c

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .loadTable ⟨⟨2⟩⟩ [1, 2],
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ 1 3],
    .loadTable ⟨⟨3⟩⟩ [4],
    .constrainInstance (cell 0 4 .advice 0) ⟨0⟩ 0,
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .constrainEqual (cell 0 3 .advice 0) (cell 1 5 .advice 0),
      .constrainConstant (cell 0 6 .advice 0) 9,
      .constrainEqual (cell 1 1 .fixed 0) (cell 0 0 .fixed 0)],
    .constrainInstance (cell 1 7 .advice 0) ⟨0⟩ 1,
    .region "r2" [.assignFixed ⟨0⟩ 0 5, .constrainEqual (cell 2 0 .fixed 0) (cell 0 1 .fixed 0),
      .constrainConstant (cell 1 9 .fixed 0) 2, .constrainConstant (cell 2 4 .instance 0) 2],
    .constrainInstance (cell 2 3 .fixed 0) ⟨0⟩ 2]

end LoweringFixtures.CopyTableInterleaved
