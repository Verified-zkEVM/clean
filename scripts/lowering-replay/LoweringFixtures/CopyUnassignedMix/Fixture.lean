import LoweringFixtures.Common

/-! Copies of cells nothing assigns, which Rust's keygen records (keygen.rs:142-154) and its
prover reads as 0: equality to and between unassigned cells past the region's rows, a constant
on an unassigned cell, a layouter instance copy of one, and a region whose only operation is a
copy. -/
namespace LoweringFixtures.CopyUnassignedMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let inst ← instanceColumn
  let f ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩
  enableEquality ⟨.advice, b⟩
  enableConstant f

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .constrainEqual (cell 0 0 .advice 0) (cell 0 2 .advice 1),
      .constrainEqual (cell 0 3 .advice 0) (cell 0 4 .advice 1),
      .constrainConstant (cell 0 5 .advice 1) 7],
    .constrainInstance (cell 0 6 .advice 0) ⟨0⟩ 1,
    .region "copy only" [.constrainEqual (cell 1 1 .advice 1) (cell 0 0 .advice 0)],
    .region "r2" [.assignAdvice ⟨1⟩ 0 witness, .constrainEqual (cell 2 0 .advice 1) (cell 0 4 .advice 1)]]

end LoweringFixtures.CopyUnassignedMix
