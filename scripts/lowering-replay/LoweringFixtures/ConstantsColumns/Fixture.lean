import LoweringFixtures.Common

/-! Several constants columns: `constants` is [c1, c0] (c1 enabled first, c0 already
equality-enabled, c1 enabled twice), and Rust's Simple planner puts every constant in
`constants[0]` = c1. c0 is written only by regions; c1 by a region and the constants, which
share its first-empty row. One constant is `-1`. -/
namespace LoweringFixtures.ConstantsColumns
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let c0 ← fixedColumn
  let c1 ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.fixed, c0⟩
  enableConstant c1
  enableConstant c0
  enableConstant c1

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .constrainConstant (cell 0 0 .advice 0) 21, .constrainConstant (cell 0 1 .advice 0) 22,
      .assignFixed ⟨0⟩ 0 5],
    .region "r1" [.assignFixed ⟨1⟩ 0 9, .assignAdvice ⟨0⟩ 0 witness,
      .constrainConstant (cell 1 0 .advice 0) 23],
    .region "r2" [.assignFixed ⟨0⟩ 0 6, .assignAdvice ⟨0⟩ 0 witness,
      .constrainConstant (cell 2 0 .advice 0) (-1)]]

def layout : Chips.Layout.DerivedLayout := Export.layout source fixture.ops fixture.k

#guard source.constantColumns == #[1, 0]
#guard layout.regionStarts == [0, 2, 3]
#guard (layout.fixed[0]!).toList.take 5 == [5, 0, 0, 6, 0]
#guard (layout.fixed[1]!).toList.take 4 == [21, 22, 9, 23]
#guard (layout.fixed[1]!)[4]! == scalarNat (-1)
-- Permutation columns are [a, c0, c1].
#guard layout.copies == [(2, 0, 0, 0), (2, 1, 0, 1), (2, 3, 0, 2), (2, 4, 0, 3)]

end LoweringFixtures.ConstantsColumns
