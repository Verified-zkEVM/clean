import LoweringFixtures.Common

/-! Conflicting fixed writes, which Rust's keygen resolves by the last `assign_fixed`: a
cell rewritten in one region, rewritten to 0, region writes into a table column before its load
(the table wins) and after it (the region wins), on loaded rows and in the default fill. -/
namespace LoweringFixtures.FixedWriteOrder
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let t ← fixedColumn
  let q ← selector
  let ql ← selector false
  gate "g" q do
    let x ← advice a
    let c ← fixed f
    return #[("g", x - c)]
  batchedLookup "t" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def g : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩
def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [
    .region "r0" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ 0 1, .enableGate (cleanGate g) 0,
      .assignFixed ⟨0⟩ 0 2, .assignFixed ⟨1⟩ 4 8, .assignFixed ⟨1⟩ 0 6],
    .loadTable ⟨⟨1⟩⟩ [3, 4],
    .region "r1" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ 0 5, .assignFixed ⟨1⟩ 5 9,
      .assignFixed ⟨1⟩ 1 1, .enableLookup (cleanLookup lk) [⟨1, false⟩] 0, .assignFixed ⟨0⟩ 0 3],
    .region "r2" [.assignFixed ⟨0⟩ 0 7, .assignFixed ⟨0⟩ 0 0]]

-- Last writers: f at r0 = 2, at r1 = 3, at r2 = 0; t rows 0, 4 from the table, rows 6, 10 from r1.
#guard (Export.layout source fixture.ops fixture.k).fixed[0]!.toList.take 12 =
  [2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0]
#guard (Export.layout source fixture.ops fixture.k).fixed[1]!.toList.take 12 =
  [3, 4, 3, 3, 3, 3, 1, 3, 3, 3, 9, 3]

end LoweringFixtures.FixedWriteOrder
