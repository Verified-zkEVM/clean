import LoweringFixtures.Common

/-! A constant on an assigned advice cell past the usable rows (k = 4: 9 usable). The
assignment is keyed, but the constants pass copies the cell and keygen's `copy` fails. -/
namespace LoweringFixtures.ConstantPastUsable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant c

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 12 witness,
    .constrainConstant (cell 0 12 .advice 0) 5]]

end LoweringFixtures.ConstantPastUsable
