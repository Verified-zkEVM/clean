import LoweringFixtures.Common

/-! A region's constant on a cell of a later region. Rust's constants pass after the region
indexes `regions` with the cell's region and panics; Lean must reject. -/
namespace LoweringFixtures.ConstantFutureRegion
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
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 1 0 .advice 0) 5],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.ConstantFutureRegion
