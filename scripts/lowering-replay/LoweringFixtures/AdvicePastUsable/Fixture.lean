import LoweringFixtures.Common

/-! Advice assignments at and past the usable rows with no copy on them (k = 4: 9 usable). Keygen's
`Assembly::assign_advice` checks nothing (keygen.rs "We only care about fixed columns here") and the
Simple planner places regions without bounds, so Rust keys this: `past` writes row 9, `beyond` starts
at 10 and ends at row 17, past 2^k. `gate` sits on another column at row 0. -/
namespace LoweringFixtures.AdvicePastUsable
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let qs ← selector
  let _ := a
  gate "s" qs do
    let y ← advice b
    return #[("s", Rust.mul y y)]

def source : CS := (configure.run {}).2

def s : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "past" [.assignAdvice ⟨0⟩ 9 witness],
    .region "beyond" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 7 witness],
    .region "gate" [.assignAdvice ⟨1⟩ 0 witness, .enableGate (cleanGate s) 0]]

end LoweringFixtures.AdvicePastUsable
