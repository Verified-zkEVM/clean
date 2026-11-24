import LoweringFixtures.Common

/-! A complex selector owned by a gate and a lookup, enabled by `enableGate` alone. Rust's
`q.enable` switches both on; `Canonical.ops` states the lookup there too. -/
namespace LoweringFixtures.SharedSelector
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let t ← fixedColumn
  let q ← selector false
  gate "bool" q do
    let x ← advice a
    return #[("bool", x * x - x)]
  batchedLookup "range" q do
    let x ← advice a
    return #[(#[x], t)]

def source : CS := (configure.run {}).2

def bool : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, false⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.loadTable ⟨⟨0⟩⟩ [0, 1],
    .region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate bool) 0]]

end LoweringFixtures.SharedSelector
