import LoweringFixtures.Common

/-! Deferred constants interleaved with everything that shares their rows or their copy stream:
`assignAdviceFromConstant`, `assign_fixed` on the constants column inside a region that also queues
constants and in a later region (which the constants push down), a constant on a cell of an earlier
region, a constant on an equality-enabled fixed cell, equality and in-region instance copies before
the region's constants copies, a layouter instance copy between regions, and a region placed below
the constants' rows. -/
namespace LoweringFixtures.ConstantsInterleaved
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← fixedColumn
  let f ← fixedColumn
  let inst ← instanceColumn
  let q ← selector
  enableEquality ⟨.advice, a⟩
  enableConstant c
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.advice, b⟩
  enableEquality ⟨.fixed, f⟩
  gate "diff" q do
    let x ← advice a
    let y ← advice b
    return #[("diff", Rust.sub x y)]

def source : CS := (configure.run {}).2

def diffGate : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fromConstant (region row : Nat) (column : Nat) (value : F) : RegionOperations F :=
  (assignAdviceFromConstant ⟨column⟩ row value).operations region

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" (fromConstant 0 0 0 3 ++ [.assignAdvice ⟨1⟩ 0 witness,
      .constrainEqual (cell 0 0 .advice 1) (cell 0 0 .advice 0),
      .constrainConstant (cell 0 0 .advice 1) 3, .assignFixed ⟨0⟩ 1 11]),
    .constrainInstance (cell 0 0 .advice 0) ⟨0⟩ 0,
    .region "r1" ([.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 0 0 .advice 1) 3,
      .assignFixed ⟨1⟩ 0 4, .constrainConstant (cell 1 0 .fixed 1) 4,
      .assignAdvice ⟨1⟩ 0 witness, .constrainInstance (cell 1 0 .advice 1) ⟨0⟩ 1] ++
      fromConstant 1 1 0 0),
    .region "r2" ([.assignFixed ⟨0⟩ 0 13] ++ fromConstant 2 0 0 7),
    .region "r3" [.assignAdvice ⟨1⟩ 0 witness, .enableGate (cleanGate diffGate) 0,
      .constrainConstant (cell 3 0 .advice 1) 8]]

def layout : Chips.Layout.DerivedLayout := Export.layout source fixture.ops fixture.k

-- r0 at 0 (its constants at c rows 2, 3), r1 at 2 (c rows 4, 5, 6), r2 at c's next row 7
-- (c row 8), r3 at b's next row 4 (c row 9). Permutation columns are [a, c, inst, b, f].
#guard layout.regionStarts == [0, 2, 7, 4]
#guard (layout.fixed[0]!).toList.take 11 == [0, 11, 3, 3, 3, 4, 0, 13, 7, 8, 0]
#guard layout.copies == [(3, 0, 0, 0), (1, 2, 0, 0), (1, 3, 3, 0), (0, 0, 2, 0), (3, 2, 2, 1),
  (1, 4, 3, 0), (1, 5, 4, 2), (1, 6, 0, 3), (1, 8, 0, 7), (1, 9, 3, 4)]

end LoweringFixtures.ConstantsInterleaved
