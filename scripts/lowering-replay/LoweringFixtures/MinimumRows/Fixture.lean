import LoweringFixtures.Common

/-! Ten advice rotations give 13 blinding factors, so `2^4 = 16` rows is exactly Rust's
minimum: both key it. -/
namespace LoweringFixtures.MinimumRows
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector
  gate "wide" q do
    let xs ← (List.range 10).mapM fun r => advice a r
    return #[("sum", xs.tail.foldl (· + ·) (xs.head?.getD (.const 0)))]

def source : CS := (configure.run {}).2

def wide : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate wide) 0]]

#guard source.blindingFactors + 3 == 16

end LoweringFixtures.MinimumRows
