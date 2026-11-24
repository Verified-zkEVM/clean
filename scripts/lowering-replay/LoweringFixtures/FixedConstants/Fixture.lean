import LoweringFixtures.Common

/-! Deferred constants: r0 has two advice rows and two constants, r1 assigns the constants column at
its row 0, r2 has one advice row and one constant. Rust allocates constants from the same
first-empty row as region placement, giving starts [0, 2, 2], constants-column rows 0..3 = 5, 6, 7,
9 and the copies (F0,0→A0,0), (F0,1→A0,1), (F0,3→A0,2). -/
namespace LoweringFixtures.FixedConstants
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
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .constrainConstant (cell 0 0 .advice 0) 5, .constrainConstant (cell 0 1 .advice 0) 6],
    .region "r1" [.assignFixed ⟨0⟩ 0 7],
    .region "r2" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 2 0 .advice 0) 9]]

def layout : Chips.Layout.DerivedLayout := Export.layout source fixture.ops fixture.k

-- Permutation columns are [A0, F0].
#guard layout.regionStarts == [0, 2, 2]
#guard (layout.fixed[0]!).toList.take 5 == [5, 6, 7, 9, 0]
#guard layout.copies == [(1, 0, 0, 0), (1, 1, 0, 1), (1, 3, 0, 2)]

end LoweringFixtures.FixedConstants
