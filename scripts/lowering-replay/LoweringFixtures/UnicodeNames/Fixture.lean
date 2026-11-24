import LoweringFixtures.Common

/-! Lookup names `<str as Debug>` escapes in part: a combining accent after a letter
and alone, NBSP, soft hyphen, zero-width space, BOM, a private-use and an unassigned code point, a
C1 control and U+10FFFF, beside printable CJK, emoji and Greek. -/
namespace LoweringFixtures.UnicodeNames
open Halo2 Midnight Midnight.Keygen

def chars (codes : List Nat) : String := String.ofList (codes.map Char.ofNat)

def names : List String := [
  chars [0x61, 0x301, 0x20, 0x301], chars [0xa0, 0xad, 0x200b, 0xfeff], chars [0xe000, 0x378, 0x85],
  chars [0x65e5, 0x672c, 0x1f980, 0x3a9, 0x10ffff]]

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  for name in names do
    batchedLookup name ql do
      let x ← advice a
      return #[(#[x], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" (.assignAdvice ⟨0⟩ 0 witness :: (List.range 4).map fun i =>
      .enableLookup (cleanLookup (source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩)) [⟨0, false⟩] 0)]

#guard names.map debugEscape == ["a\\u{301} \\u{301}", "\\u{a0}\\u{ad}\\u{200b}\\u{feff}",
  "\\u{e000}\\u{378}\\u{85}", chars [0x65e5, 0x672c, 0x1f980, 0x3a9] ++ "\\u{10ffff}"]

end LoweringFixtures.UnicodeNames
