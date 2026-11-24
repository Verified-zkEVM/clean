import LoweringFixtures.Common

/-! `Constant(0) + q * x` with simple `q` beside a valid complex `rows` gate: Rust's `+` folds a zero
operand only after its simple-selector check, so it panics (circuit.rs:1197) although the sum
folds to `q * x`. -/
namespace LoweringFixtures.SimpleZeroSum
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let qs ← selector
  let qc ← selector false
  gateWithoutSelector "ok" do
    let x ← advice a
    return #[("", .add (Rust.mul (querySelector qc) x) x)]
  gateWithoutSelector "zero sum" do
    let x ← advice a
    return #[("", .add (.const 0) (Rust.mul (querySelector qs) x))]

def source : CS := (configure.run {}).2

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness]]

end LoweringFixtures.SimpleZeroSum
