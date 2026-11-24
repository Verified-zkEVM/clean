import LoweringFixtures.Common

/-! A non-ASCII lookup name, which `<str as Debug>` prints as it is. -/
namespace LoweringFixtures.LookupNameUnicode
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "é" ql do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness,
      .enableLookup (cleanLookup (source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩)) [⟨0, false⟩] 0]]

end LoweringFixtures.LookupNameUnicode
