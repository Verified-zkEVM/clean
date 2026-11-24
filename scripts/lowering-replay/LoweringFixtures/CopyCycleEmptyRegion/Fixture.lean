import LoweringFixtures.Common

/-! Copy order through unassigned cells: one region interleaves constants, equalities and
an in-region instance copy whose cell is assigned last, all merging one cycle with unassigned
endpoints; a region that assigns nothing (start 0) copies and constrains its own cells; layouter
instance copies end at the last usable row (k = 4: 9 usable). -/
namespace LoweringFixtures.CopyCycleEmptyRegion
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← fixedColumn
  let inst ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, b⟩
  enableEquality ⟨.instance, inst⟩
  enableConstant c

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness,
      .constrainConstant (cell 0 1 .advice 0) 5,
      .constrainEqual (cell 0 0 .advice 0) (cell 0 3 .advice 1),
      .constrainInstance (cell 0 2 .advice 0) ⟨0⟩ 0,
      .constrainEqual (cell 0 3 .advice 1) (cell 0 1 .advice 0),
      .constrainConstant (cell 0 3 .advice 1) 5,
      .assignAdvice ⟨0⟩ 2 witness],
    .region "empty" [.constrainEqual (cell 1 0 .advice 1) (cell 0 2 .advice 0),
      .constrainConstant (cell 1 0 .advice 1) 6, .constrainEqual (cell 1 4 .advice 0) (cell 1 4 .advice 1)],
    .constrainInstance (cell 1 8 .advice 1) ⟨0⟩ 8,
    .constrainInstance (cell 0 1 .advice 0) ⟨0⟩ 1,
    .constrainInstance (cell 1 4 .advice 0) ⟨0⟩ 1]

end LoweringFixtures.CopyCycleEmptyRegion
