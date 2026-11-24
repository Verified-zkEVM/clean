import LoweringFixtures.Common

/-! Lookup names get Rust's ordinal prefix in the pinned system, even a name that
already looks prefixed, and ASCII names are escaped as Rust's `Debug` escapes them. -/
namespace LoweringFixtures.LookupNames
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "lookup #5: spoof" ql do
    let x ← advice a
    return #[(#[x], t)]
  batchedLookup "plain" ql do
    let x ← advice a 1
    return #[(#[x], t)]
  batchedLookup "q\"b\\s\tt\rr\nn\x00z\x01\x1b\x7f'" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def lookup (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 1 witness,
      .enableLookup (cleanLookup (lookup 0)) [⟨0, false⟩] 0, .enableLookup (cleanLookup (lookup 1)) [⟨0, false⟩] 0,
      .enableLookup (cleanLookup (lookup 2)) [⟨0, false⟩] 0]]

#guard (source.pinnedDebug.splitOn "name: \"lookup #1: lookup #5: spoof\"").length == 2
#guard (source.pinnedDebug.splitOn "name: \"lookup #2: plain\"").length == 2
#guard (source.pinnedDebug.splitOn
  "name: \"lookup #3: q\\\"b\\\\s\\tt\\rr\\nn\\0z\\u{1}\\u{1b}\\u{7f}'\"").length == 2

end LoweringFixtures.LookupNames
