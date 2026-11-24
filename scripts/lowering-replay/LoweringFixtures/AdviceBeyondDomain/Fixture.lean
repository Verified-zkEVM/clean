import LoweringFixtures.Common

/-! Advice past the whole domain (k = 4: 16 rows, 9 usable): `far` assigns `a(40)`, so `beyond`
starts at 41; `low`, on a fresh column, starts at 0 and copies usable cells of `far` and itself. Keygen's `assign_advice`
checks nothing, so Rust keys it. -/
namespace LoweringFixtures.AdviceBeyondDomain
open Halo2 Midnight Midnight.Keygen

def configure : ConfigM Unit := do
  let a ← adviceColumn
  let b ← adviceColumn
  let c ← adviceColumn
  enableEquality ⟨.advice, a⟩
  enableEquality ⟨.advice, c⟩
  let q ← selector
  gate "s" q do
    let y ← advice b
    return #[("s", Rust.mul y y)]

def source : CS := (configure.run {}).2

def s : GateSpec := source.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture where
  source := source
  k := 4
  ops := [
    .region "far" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 40 witness,
      .enableGate (cleanGate s) 0, .assignAdvice ⟨1⟩ 0 witness],
    .region "beyond" [.assignAdvice ⟨0⟩ 0 witness, .assignAdvice ⟨0⟩ 3 witness],
    .region "low" [.assignAdvice ⟨2⟩ 0 witness, .assignAdvice ⟨2⟩ 2 witness,
      .constrainEqual (cell 0 0 .advice 0) (cell 2 2 .advice 2)]]

#guard (Export.layout source fixture.ops fixture.k).regionStarts == [0, 41, 0]

end LoweringFixtures.AdviceBeyondDomain
