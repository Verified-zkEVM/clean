import LoweringFixtures.Common

/-! Deferred constants on a lookup table column that disagree with the table: the first
region's constants are overwritten by the later load, the second region's `assign_fixed` and
constant overwrite the load, in Rust's order (region writes, then its constants). -/
namespace LoweringFixtures.ConstantsTableConflict
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
  k := 4
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 0 0 .advice 0) 5,
      .assignAdvice ⟨0⟩ 1 witness, .constrainConstant (cell 0 1 .advice 0) 6],
    .loadTable ⟨⟨0⟩⟩ [1, 2, 3],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 1 0 .advice 0) 9,
      .assignFixed ⟨0⟩ 0 7, .enableLookup (cleanLookup lk) [⟨0, false⟩] 0]]

-- t: the load over r0's constants (rows 0, 1), r1's write at row 2, its constant at row 3.
#guard (Export.layout source fixture.ops fixture.k).regionStarts = [0, 2]
#guard (Export.layout source fixture.ops fixture.k).fixed[0]!.toList.take 6 = [1, 2, 7, 9, 1, 1]

end LoweringFixtures.ConstantsTableConflict
