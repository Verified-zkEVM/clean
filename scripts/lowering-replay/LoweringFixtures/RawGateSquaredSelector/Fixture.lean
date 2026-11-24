import LoweringFixtures.Common

/-! A `without_selector` body `(q * q) * x` on a complex selector: Rust keys it and, `q` being
0/1, enforces `x = 0` where `q` is on; it is owned with degree 2. -/
namespace LoweringFixtures.RawGateSquaredSelector
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector false
  gateWithoutSelector "squared" do
    let x ← advice a
    return #[("", Rust.mul (Rust.mul (querySelector q) (querySelector q)) x)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.RawGateSquaredSelector
