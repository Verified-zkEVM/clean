import LoweringFixtures.Common

/-! A lookup whose only input is a constant (degree 0). -/
namespace LoweringFixtures.ConstantLookupInput
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let _ ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "const" ql do
    return #[(#[.const 1], t)]

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableLookup (cleanLookup lk) [⟨0, false⟩] 0]]

end LoweringFixtures.ConstantLookupInput
