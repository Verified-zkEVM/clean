import LoweringFixtures.Common

/-! `2^3 = 8` rows, below the minimum `blinding_factors + 3 = 9`: Rust's keygen fails with
`NotEnoughRowsAvailable`, and Lean rejects the domain. -/
namespace LoweringFixtures.SmallDomain
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let _ ← adviceColumn

def fixture : Export.Replay.Fixture where
  source := (configure.run {}).2
  k := 3
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

#guard fixture.source.blindingFactors + 3 == 9

end LoweringFixtures.SmallDomain
