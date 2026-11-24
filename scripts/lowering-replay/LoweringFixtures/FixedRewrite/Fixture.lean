import LoweringFixtures.Common

/-! One region writing a fixed cell twice with different values; Rust and Lean keep the last
write. -/
namespace LoweringFixtures.FixedRewrite
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let f ← fixedColumn
  let q ← selector
  gate "g" q do
    let x ← advice a
    let c ← fixed f
    return #[("g", x - c)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 5
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignFixed ⟨0⟩ 0 1,
    .enableGate (cleanGate (source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩)) 0,
    .assignFixed ⟨0⟩ 0 2]]

end LoweringFixtures.FixedRewrite
