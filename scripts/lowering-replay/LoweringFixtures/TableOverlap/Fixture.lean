import LoweringFixtures.Common

/-! Region fixed writes into a loaded lookup table column, agreeing with the table: before the
load on a loaded row and in the default-fill range, after it in the default-fill range. The
table load does not occupy the column for placement, but the first region does: starts [0, 6]. -/
namespace LoweringFixtures.TableOverlap
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "t" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "before" [.assignFixed ⟨0⟩ 5 2, .assignFixed ⟨0⟩ 1 7, .assignAdvice ⟨0⟩ 0 witness,
      .enableLookup (cleanLookup lk) [⟨0, false⟩] 0],
    .loadTable ⟨⟨0⟩⟩ [2, 7, 9],
    .region "after" [.assignFixed ⟨0⟩ 2 2, .assignAdvice ⟨0⟩ 0 witness,
      .enableLookup (cleanLookup lk) [⟨0, false⟩] 0]]

end LoweringFixtures.TableOverlap
