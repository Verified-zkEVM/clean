import LoweringFixtures.Common

/-! Constants on a lookup table column. Tables allocate no rows, so V1 puts the constants on t rows
0-2 after synthesis, over the table's cells and fill (keygen keeps the last write): t = 5, 9, 7,
then the fill 5. Simple writes each region's constants before the later load, which overwrites
them. -/
namespace LoweringFixtures.V1ConstantsTable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  enableEquality ⟨.advice, a⟩
  batchedLookup "t" ql do
    let x ← advice a
    return #[(#[x], t)]
  enableConstant t

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" ((List.range 6).map (.assignAdvice ⟨0⟩ · witness) ++
      [.enableLookup (cleanLookup lk) [⟨0, false⟩] 0, .constrainConstant (cell 0 0 .advice 0) 5,
        .constrainConstant (cell 0 1 .advice 0) 9]),
    .loadTable ⟨⟨0⟩⟩ [5, 6],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 1 0 .advice 0) 7]]

def layout : Chips.Layout.DerivedLayout :=
  Export.layout source fixture.ops fixture.k (Export.v1 source)

#guard layout.regionStarts == [0, 6]
#guard (layout.fixed[0]!).toList.take 4 == [5, 9, 7, 5]
#guard ((Export.layout source fixture.ops fixture.k).fixed[0]!).toList.take 4 == [5, 6, 7, 5]

end LoweringFixtures.V1ConstantsTable
