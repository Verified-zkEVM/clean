import LoweringFixtures.Common

/-! A deferred constant on an advice column without equality, after a valid
`assignAdviceFromConstant`: Rust's constants copy fails with `ColumnNotInPermutation`, Lean's
`KeygenRegistered` rejects. -/
namespace LoweringFixtures.ConstantsNoEquality
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let _b ← adviceColumn
  let c ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant c

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" ((assignAdviceFromConstant ⟨0⟩ 0 (2 : F)).operations 0 ++
      [.assignAdvice ⟨1⟩ 0 witness, .constrainConstant (cell 0 0 .advice 1) 3])]

end LoweringFixtures.ConstantsNoEquality
