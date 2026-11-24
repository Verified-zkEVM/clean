import LoweringFixtures.Common

/-! V1's constants (v1.rs:89-138): queued in stream order and placed after synthesis on the free
rows below `first_unassigned_row` of each constants column in turn, `constants` = [f1, f0]. f1 is
allocated at rows 0-1 by a fixed region, so the six constants take f1 rows 2-5, then f0 rows 0-1;
their copies come after every equality and instance copy. Simple puts them all on f1. -/
namespace LoweringFixtures.V1Constants
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f0 ← fixedColumn
  let f1 ← fixedColumn
  let i ← instanceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.instance, i⟩
  enableConstant f1
  enableConstant f0

def source : CS := (configure.run {}).2

/-- `V1ConstantsShort` appends `extra` to the last region. -/
def ops (extra : RegionOperations F := []) : Operations F := [
  .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨0⟩ 2 witness,
    .constrainConstant (cell 0 0 .advice 0) 5, .constrainConstant (cell 0 2 .advice 0) 6,
    .constrainEqual (cell 0 1 .advice 0) (cell 0 2 .advice 0)],
  .region "r1" [.assignFixed ⟨1⟩ 0 11, .assignFixed ⟨1⟩ 1 12],
  .constrainInstance (cell 0 1 .advice 0) ⟨0⟩ 0,
  .region "r2" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 2 0 .advice 0) 7,
    .constrainConstant (cell 0 1 .advice 0) 10],
  .region "r3" (([.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
    .constrainConstant (cell 3 0 .advice 0) 8, .constrainConstant (cell 3 1 .advice 0) (-1),
    .constrainInstance (cell 3 1 .advice 0) ⟨0⟩ 1] : RegionOperations F) ++ extra)]

def fixture : Export.Replay.Fixture := { source, ops := ops, k := 5 }

def layout : Chips.Layout.DerivedLayout :=
  Export.layout source fixture.ops fixture.k (Export.v1 source)

-- Permutation columns are [A0, I0, F1, F0].
#guard layout.regionStarts == [0, 0, 5, 3]
#guard (layout.fixed[1]!).toList.take 6 == [11, 12, 5, 6, 7, 10]
#guard (layout.fixed[0]!).toList.take 3 == [8, scalarNat (-1), 0]
#guard layout.copies == [(0, 1, 0, 2), (0, 1, 1, 0), (0, 4, 1, 1),
  (2, 2, 0, 0), (2, 3, 0, 2), (2, 4, 0, 5), (2, 5, 0, 1), (3, 0, 0, 3), (3, 1, 0, 4)]

end LoweringFixtures.V1Constants
