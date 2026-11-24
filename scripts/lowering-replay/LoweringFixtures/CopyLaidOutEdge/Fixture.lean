import LoweringFixtures.Common

/-! The laid-out boundary Rust allows: region 1 copies a region-0 cell and its own cell before
assigning it, puts a constant on its own unassigned cell, and a layouter instance copy of region 1
follows it. -/
namespace LoweringFixtures.CopyLaidOutEdge
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c ← fixedColumn
  let i ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, i⟩
  enableConstant c

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness],
    .region "r1" [.constrainEqual (cell 0 0 .advice 0) (cell 1 1 .advice 0),
      .constrainConstant (cell 1 2 .advice 0) 7, .assignAdvice ⟨0⟩ 1 witness],
    .constrainInstance (cell 1 1 .advice 0) ⟨0⟩ 0]

end LoweringFixtures.CopyLaidOutEdge
