import LoweringFixtures.Common

/-! A deferred constant without `enable_constant`: Rust's Simple planner fails with
`NotEnoughColumnsForConstants`; Lean's `ConstantsPlaced` rejects. -/
namespace LoweringFixtures.ConstantsNoColumn
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.fixed, c⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r0" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 0 0 .advice 0) 5]]

-- The standalone exporter checks placement directly, without the replay admission checks.
#guard !(Export.checkLayout source fixture.ops fixture.k).isOk
#guard !(Export.checkLayout source fixture.ops fixture.k (Export.v1 source)).isOk

end LoweringFixtures.ConstantsNoColumn
