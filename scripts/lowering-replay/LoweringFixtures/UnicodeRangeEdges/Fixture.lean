import LoweringFixtures.Common

/-! Every boundary of `debugEscapedRanges` (lo-1, lo, hi, hi+1) and a sweep of code points across
the whole range, as lookup names, so Rust's own `<str as Debug>` checks each edge of Lean's table.
Surrogates are skipped; one batch has no tuples. -/
namespace LoweringFixtures.UnicodeRangeEdges
open Halo2 Midnight Midnight.Keygen

def valid (n : Nat) : Bool := 0x80 ≤ n && n ≤ 0x10ffff && !(0xd800 ≤ n && n ≤ 0xdfff)

def edges : List Nat :=
  (debugEscapedRanges.toList.flatMap fun (lo, hi) => [lo - 1, lo, hi, hi + 1]).filter valid

def sweep : List Nat :=
  ((List.range 2200).map (0x80 + 97 * ·) ++ (List.range 260).map (0x30000 + 4099 * ·)).filter valid

def chunks (xs : List Nat) (size : Nat) : List String :=
  (List.range ((xs.length + size - 1) / size)).map fun i =>
    String.ofList (((xs.drop (i * size)).take size).map Char.ofNat)

def names : List String := chunks edges 600 ++ chunks sweep 800

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  for name in names do
    batchedLookup name ql do
      let x ← advice a
      return #[(#[x], t)]
  batchedLookup (String.ofList [Char.ofNat 0x301, 'q', Char.ofNat 0x200d]) ql do return #[(#[], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" (.assignAdvice ⟨0⟩ 0 witness :: (List.range names.length).map fun i =>
      .enableLookup (cleanLookup (source.lookups[i]?.getD ⟨"", .const 0, #[], #[]⟩)) [⟨0, false⟩] 0)]

#guard source.validate.isOk && edges.length > 3000 && names.length == source.lookups.size - 1

end LoweringFixtures.UnicodeRangeEdges
