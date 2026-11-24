import LoweringFixtures.Common

/-! V1 constants in the gaps of region allocations: f0 is allocated at rows 0 and 4-5 by regions
2 and 1, f1 at rows 0-2 by region 3, so with `first_unassigned_row` = 6 the five constants take f0
rows 1-3, then f1 rows 3-4 (`constants` = [f0, f1]). Regions 0 and 2 constrain cells of region
1 before it is synthesized, which only V1 keys. -/
namespace LoweringFixtures.V1ConstantsGaps
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f0 ← fixedColumn
  let f1 ← fixedColumn
  enableEquality ⟨.advice, a⟩
  enableConstant f0
  enableConstant f1

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" ((List.range 4).map (.assignAdvice ⟨0⟩ · witness) ++
      [.constrainConstant (cell 0 3 .advice 0) 1, .constrainConstant (cell 1 1 .advice 0) 2]),
    .region "r1" [.assignAdvice ⟨0⟩ 1 witness, .assignFixed ⟨0⟩ 0 8, .constrainConstant (cell 0 0 .advice 0) 3],
    .region "r2" [.assignFixed ⟨0⟩ 0 9, .constrainConstant (cell 1 1 .advice 0) 4],
    .region "r3" [.assignFixed ⟨1⟩ 2 7, .constrainConstant (cell 0 1 .advice 0) 5]]

def layout : Chips.Layout.DerivedLayout :=
  Export.layout source fixture.ops fixture.k (Export.v1 source)

#guard layout.regionStarts == [0, 4, 0, 0]
#guard (layout.fixed[0]!).toList.take 6 == [9, 1, 2, 3, 8, 0]
#guard (layout.fixed[1]!).toList.take 5 == [0, 0, 7, 4, 5]

end LoweringFixtures.V1ConstantsGaps
