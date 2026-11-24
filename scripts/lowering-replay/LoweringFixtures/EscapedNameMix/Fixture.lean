import LoweringFixtures.Common

/-! Lookup names with less common ASCII escapes: backspace, vertical tab, form feed and unit
separator as `\u{..}`, a trailing backslash, text that looks like an escape, doubled DEL and tabs,
and every printable punctuation mark, on a two-wide two-parallel batch and single lookups sharing a
table. -/
namespace LoweringFixtures.EscapedNameMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let t ← fixedColumn
  let t2 ← fixedColumn
  let ql ← selector false
  batchedLookup "\x08\x0b\x0c\x1f end\\" ql do
    let x ← advice a
    let y ← advice b
    return #[(#[x, y], t), (#[y, x], t2)]
  batchedLookup "{}\"#: lookup #0 \\u{41}" ql do
    let x ← advice a 1
    return #[(#[x], t)]
  batchedLookup "\x7f\x7f\t\t" ql do
    let y ← advice b 1
    return #[(#[y], t2)]
  batchedLookup "~ !$%&()*+,-./:;<=>?@[]^_`|'" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def lookup (i : Nat) : BatchedLookup := source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1, 2], .loadTable ⟨⟨1⟩⟩ [3],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 1 witness,
      .enableLookup (cleanLookup (lookup 0) 0) [⟨0, false⟩] 0,
      .enableLookup (cleanLookup (lookup 0) 1) [⟨0, false⟩] 0,
      .enableLookup (cleanLookup (lookup 1)) [⟨0, false⟩] 0,
      .enableLookup (cleanLookup (lookup 2)) [⟨0, false⟩] 0,
      .enableLookup (cleanLookup (lookup 3)) [⟨0, false⟩] 0]]

#guard (source.pinnedDebug.splitOn
  "name: \"lookup #1: \\u{8}\\u{b}\\u{c}\\u{1f} end\\\\\"").length == 2
#guard (source.pinnedDebug.splitOn "name: \"lookup #2: {}\\\"#: lookup #0 \\\\u{41}\"").length == 2
#guard (source.pinnedDebug.splitOn "name: \"lookup #3: \\u{7f}\\u{7f}\\t\\t\"").length == 2

end LoweringFixtures.EscapedNameMix
