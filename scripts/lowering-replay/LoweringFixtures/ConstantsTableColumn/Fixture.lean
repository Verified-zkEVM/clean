import LoweringFixtures.Common

/-! Deferred constants on a lookup table column: `enableConstant` on the table column, constants
queued before and after the table load, all agreeing with the table's default fill, and lookups
enabled on the constrained cells. -/
namespace LoweringFixtures.ConstantsTableColumn
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
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .enableLookup (cleanLookup lk) [⟨0, false⟩] 0,
      .constrainConstant (cell 0 0 .advice 0) 5, .assignAdvice ⟨0⟩ 1 witness,
      .constrainConstant (cell 0 1 .advice 0) 5],
    .loadTable ⟨⟨0⟩⟩ [5],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .constrainConstant (cell 1 0 .advice 0) 5,
      .enableLookup (cleanLookup lk) [⟨0, false⟩] 0, .constrainConstant (cell 0 0 .advice 0) 5]]

end LoweringFixtures.ConstantsTableColumn
