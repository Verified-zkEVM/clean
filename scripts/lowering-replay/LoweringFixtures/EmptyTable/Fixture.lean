import LoweringFixtures.Common

/-! Empty `assign_table`s: one on the lookup's table column before its real load, which
Rust allows because an empty load marks no column used, and one on a column never loaded. -/
namespace LoweringFixtures.EmptyTable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let _ ← fixedColumn
  let ql ← selector false
  batchedLookup "range" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness,
      .enableLookup (cleanLookup (source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩)) [⟨0, false⟩] 0],
    .loadTable ⟨⟨0⟩⟩ [0, 1, 2], .loadTable ⟨⟨1⟩⟩ []]

#guard Chips.OperationsLawful.tableColumns fixture.ops == [0]

end LoweringFixtures.EmptyTable
