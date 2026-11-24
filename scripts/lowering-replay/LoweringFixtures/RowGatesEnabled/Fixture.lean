import LoweringFixtures.Common

/-! `rows` gates whose selectors are enabled: `with_selector(q1, [q2 * x])` on a simple `q1`
enabled through its handle, `q2 * x + q3 * y` over two complex selectors that owned gates enable,
`(q2 * q2) * y` owned with degree 2, and a selector-free constraint beside a selected one. -/
namespace LoweringFixtures.RowGatesEnabled
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let q1 ← selector
  let q2 ← selector false
  let q3 ← selector false
  gate "inner" q1 do
    let x ← advice a
    return #[("", Rust.mul (querySelector q2) x)]
  gateWithoutSelector "two" do
    let x ← advice a
    let y ← advice b (-1)
    return #[("", .add (Rust.mul (querySelector q2) x) (Rust.mul (querySelector q3) y))]
  gate "own" q2 do
    let x ← advice a
    let y ← advice b
    return #[("", Rust.sub x y)]
  gateWithoutSelector "squared" do
    let y ← advice b
    return #[("", Rust.mul (Rust.mul (querySelector q2) (querySelector q2)) y)]
  gate "three" q3 do
    let x ← advice a 1
    return #[("", Rust.mul x x)]
  gateWithoutSelector "half" do
    let x ← advice a
    let y ← advice b
    return #[("selected", Rust.mul (querySelector q3) x), ("unselected", Rust.sub (Rust.mul x y) x)]

def source : CS := (configure.run {}).2

def spec (i : Nat) : GateSpec := source.gates[i]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [.region "r" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .enableGate (cleanGate (spec 0)) 0, .enableGate (cleanGate (spec 2)) 0,
      .enableGate (cleanGate (spec 3)) 0, .assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨1⟩ 1 witness,
      .enableGate (cleanGate (spec 4)) 1, .enableGate (cleanGate (spec 2)) 1,
      .enableGate (cleanGate (spec 3)) 1, .assignAdvice ⟨0⟩ 2 witness]]

#guard source.gates.map (·.rows) == #[true, true, false, false, false, true]

end LoweringFixtures.RowGatesEnabled
