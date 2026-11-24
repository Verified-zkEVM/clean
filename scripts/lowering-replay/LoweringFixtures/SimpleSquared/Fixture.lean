import LoweringFixtures.Common

/-! `(q * q) * x` on a simple selector: Rust panics ("attempted to multiply two expressions
containing simple selectors"), and `validate` rejects it (`simpleSafe`). -/
namespace LoweringFixtures.SimpleSquared
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let q ← selector
  gateWithoutSelector "squared" do
    let x ← advice a
    return #[("", Rust.mul (Rust.mul (querySelector q) (querySelector q)) x)]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.SimpleSquared
