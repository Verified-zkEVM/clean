import LoweringFixtures.Common

/-! A layouter instance copy of a cell whose region comes later. Rust's `constrain_instance`
indexes `regions` with it and panics; Lean must reject. -/
namespace LoweringFixtures.InstanceCopyFutureRegion
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let inst ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, inst⟩

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .constrainInstance (cell 0 0 .advice 0) ⟨0⟩ 0,
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.InstanceCopyFutureRegion
