import LoweringFixtures.Common

/-! A lookup input of degree 5 raises the system's degree to 5, where a LogUp chunk holds
`4 / 5 = 0` inputs: Rust divides by zero, Lean's `validate` rejects it. -/
namespace LoweringFixtures.ZeroCapacity
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let ql ← selector false
  batchedLookup "quintic" ql do
    let x ← advice a
    return #[(#[x * x * x * x * x], t)]

def source : CS := (configure.run {}).2

def lk : BatchedLookup := source.lookups[0]?.getD ⟨"", .const 0, #[], #[]⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableLookup (cleanLookup lk) [⟨0, false⟩] 0]]

#guard source.degree == 5 && lk.chunkCapacity source.degree == 0

end LoweringFixtures.ZeroCapacity
