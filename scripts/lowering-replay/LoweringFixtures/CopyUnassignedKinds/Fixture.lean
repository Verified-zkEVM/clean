import LoweringFixtures.Common

/-! Copies of unassigned cells of every kind in region coordinates: instance to fixed,
an unassigned cell to itself, constants on an unassigned fixed and instance cell, and a later
region's assigned fixed cell to the earlier unassigned one. -/
namespace LoweringFixtures.CopyUnassignedKinds
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let c ← fixedColumn
  let inst ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.fixed, f⟩
  enableEquality ⟨.instance, inst⟩
  enableConstant c

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness,
      .constrainEqual (cell 0 3 .instance 0) (cell 0 5 .fixed 0),
      .constrainEqual (cell 0 2 .advice 0) (cell 0 2 .advice 0),
      .constrainConstant (cell 0 4 .fixed 0) 3,
      .constrainConstant (cell 0 1 .instance 0) 4],
    .region "r1" [.assignFixed ⟨0⟩ 1 2, .constrainEqual (cell 1 1 .fixed 0) (cell 0 5 .fixed 0)]]

end LoweringFixtures.CopyUnassignedKinds
