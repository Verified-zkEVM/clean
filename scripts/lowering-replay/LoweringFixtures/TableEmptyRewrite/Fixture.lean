import LoweringFixtures.Common

/-! Last writer around an empty and a real load of one table column: r0 and r1 write it,
an empty load writes and marks nothing, the real load and its fill overwrite both, r2 rewrites a
fill cell to 0, r3 writes after the fill. -/
namespace LoweringFixtures.TableEmptyRewrite
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "t" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" [.assignFixed ⟨0⟩ 0 7, .assignFixed ⟨0⟩ 2 8],
    .loadTable ⟨⟨0⟩⟩ [],
    .region "r1" [.assignFixed ⟨0⟩ 0 9],
    .loadTable ⟨⟨0⟩⟩ [1, 2],
    .region "r2" [.assignFixed ⟨0⟩ 1 6, .assignFixed ⟨0⟩ 1 0],
    .region "r3" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ 0 3]]

#guard (Export.layout source fixture.ops fixture.k).regionStarts = [0, 3, 4, 6]
#guard (Export.layout source fixture.ops fixture.k).fixed[0]!.toList.take 8 = [1, 2, 1, 1, 1, 0, 3, 1]

end LoweringFixtures.TableEmptyRewrite
