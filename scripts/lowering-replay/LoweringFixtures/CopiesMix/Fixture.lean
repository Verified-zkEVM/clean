import LoweringFixtures.Common

/-! Copies and instance copies the corpus did not combine: layouter instance copies whose cell is
an instance or fixed cell in region coordinates, instance-to-instance copies across two instance
columns (the second enabled first), two region cells naming one absolute cell, equal-size cycle
merges in both orientations, and a constant merged into a cycle through an instance cell. -/
namespace LoweringFixtures.CopiesMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let f ← fixedColumn
  let c ← fixedColumn
  let i0 ← instanceColumn
  let i1 ← instanceColumn
  enableEquality ⟨.instance, i1⟩
  enableEquality ⟨.advice, b⟩
  enableConstant c
  enableEquality ⟨.fixed, f⟩
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, i0⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .constrainInstance (cell 0 0 .advice 0) ⟨1⟩ 0,
      .constrainEqual (cell 0 0 .advice 0) (cell 0 0 .advice 1),
      .constrainConstant (cell 0 1 .advice 1) 5],
    .constrainInstance (cell 0 0 .instance 1) ⟨0⟩ 2,
    .constrainInstance (cell 0 3 .fixed 0) ⟨1⟩ 3,
    .region "empty" [],
    .region "r2" [.assignAdvice ⟨1⟩ 0 witness, .assignAdvice ⟨1⟩ 1 witness,
      .constrainEqual (cell 2 1 .advice 1) (cell 1 3 .advice 0),
      .constrainEqual (cell 2 0 .advice 1) (cell 2 1 .advice 1),
      .constrainEqual (cell 0 1 .advice 1) (cell 2 0 .advice 1),
      .constrainEqual (cell 1 3 .advice 0) (cell 0 3 .advice 0),
      .constrainEqual (cell 2 0 .instance 0) (cell 0 4 .instance 1),
      .constrainConstant (cell 2 0 .instance 0) 5,
      .constrainEqual (cell 0 4 .instance 1) (cell 0 0 .advice 1)],
    .constrainInstance (cell 2 1 .advice 1) ⟨0⟩ 1,
    .region "r3" [.assignAdvice ⟨0⟩ 0 witness, .constrainInstance (cell 3 0 .advice 0) ⟨0⟩ 0,
      .constrainInstance (cell 3 0 .advice 0) ⟨1⟩ 1,
      .constrainEqual (cell 3 2 .fixed 0) (cell 3 0 .advice 0)]]

end LoweringFixtures.CopiesMix
