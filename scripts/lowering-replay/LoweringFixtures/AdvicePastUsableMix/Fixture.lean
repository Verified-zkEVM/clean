import LoweringFixtures.Common

/-! Advice past the usable rows inside a region that also enables a gate and is copied from
(k = 4: 9 usable). `tall` ends at row 12, so `after` starts at 13 on `a`; the copy reads `a(0)`
and `c(3)`, both usable. Rust keys it; Lean must too. -/
namespace LoweringFixtures.AdvicePastUsableMix
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, c⟩
  let qs ← selector
  let _ := c
  gate "s" qs do
    let y ← advice b
    return #[("s", Rust.mul y y)]

def source : CS := (configure.run {}).2

def s : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "tall" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨1⟩ 0 witness,
      .enableGate (cleanGate s) 0, .assignAdvice ⟨0⟩ 12 witness],
    .region "side" [.assignAdvice ⟨2⟩ 0 witness, .assignAdvice ⟨2⟩ 3 witness,
      .constrainEqual (cell 0 0 .advice 0) (cell 1 3 .advice 2)],
    .region "after" [.assignAdvice ⟨0⟩ 1 witness, .assignAdvice ⟨2⟩ 0 witness]]

#guard (Export.layout source fixture.ops fixture.k).regionStarts == [0, 0, 13]

end LoweringFixtures.AdvicePastUsableMix
