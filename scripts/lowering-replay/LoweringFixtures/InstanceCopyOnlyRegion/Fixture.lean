import LoweringFixtures.Common

/-! A region of instance copies only: two copies of one unassigned cell of `a` at row 3 and one of
`b` at row 1. `assign_advice_from_instance` assigns both, so the region spans rows 1..4 on both
columns and the next regions on `a` and `b` start at 5; their equalities and a layouter instance
copy read the copied cells. -/
namespace LoweringFixtures.InstanceCopyOnlyRegion
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let inst ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, b⟩
  enableEquality ⟨.instance, inst⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "first" [.assignAdvice ⟨0⟩ 0 witness],
    .region "only" [.constrainInstance (cell 1 3 .advice 0) ⟨0⟩ 0,
      .constrainInstance (cell 1 1 .advice 1) ⟨0⟩ 1,
      .constrainInstance (cell 1 3 .advice 0) ⟨0⟩ 2],
    .region "na" [.assignAdvice ⟨0⟩ 0 witness, .constrainEqual (cell 2 0 .advice 0) (cell 1 3 .advice 0)],
    .region "nb" [.assignAdvice ⟨1⟩ 0 witness, .constrainEqual (cell 3 0 .advice 1) (cell 1 1 .advice 1)],
    .constrainInstance (cell 1 1 .advice 1) ⟨0⟩ 3]

end LoweringFixtures.InstanceCopyOnlyRegion
