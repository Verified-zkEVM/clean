import LoweringFixtures.Common

/-! Constants and region writes on a table column in its default fill: r0's write at row 3
and its constants at rows 4, 5 lie under the later load's fill, r1's constant (row 6) and r2's
write (row 7) come after it. -/
namespace LoweringFixtures.ConstantsTableFill
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
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ 3 8,
      .constrainConstant (cell 0 0 .advice 0) 5, .constrainConstant (cell 0 0 .advice 0) 6],
    .loadTable ⟨⟨0⟩⟩ [1, 2],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 1 0 .advice 0) 9,
      .enableLookup (cleanLookup lk) [⟨0, false⟩] 0],
    .region "r2" [.assignFixed ⟨0⟩ 0 7]]

#guard (Export.layout source fixture.ops fixture.k).regionStarts = [0, 4, 7]
#guard (Export.layout source fixture.ops fixture.k).fixed[0]!.toList.take 10 = [1, 2, 1, 1, 1, 1, 9, 7, 1, 1]

end LoweringFixtures.ConstantsTableFill
