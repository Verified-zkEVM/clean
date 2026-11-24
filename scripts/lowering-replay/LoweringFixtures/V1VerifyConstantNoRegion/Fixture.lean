import LoweringFixtures.Common

/-! A constant whose cell names region 2 of two. V1 queues it and panics at `plan.regions[2]` after
synthesis (v1.rs:132), with a free position for it; Simple panics when it flushes the region. -/
namespace LoweringFixtures.V1VerifyConstantNoRegion
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant f

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 2 0 .advice 0) 3]]

end LoweringFixtures.V1VerifyConstantNoRegion
