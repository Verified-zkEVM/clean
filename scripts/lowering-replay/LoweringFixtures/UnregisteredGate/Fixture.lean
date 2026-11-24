import LoweringFixtures.Ops.Fixture

/-! `Ops` with a region enabling a gate the configuration does not have, on the configured
gate's selector. Rust enables the selector, so the configured gate holds there, as
`Canonical.ops` restates it. -/
namespace LoweringFixtures.UnregisteredGate
open Halo2 Midnight Midnight.Keygen

def other : GateSpec :=
  let s := ((gate "other" ⟨0, true⟩ do
    let x ← advice 0
    return #[("other", x)]).run {}).2
  s.gates[0]?.getD ⟨"", ⟨0, true⟩, #[], #[], false, false⟩

def fixture : Export.Replay.Fixture :=
  { Ops.fixture with ops := Ops.ops ++ [.region "other" [
      .assignAdvice ⟨0⟩ 0 witness, .enableGate (cleanGate other) 0]] }

end LoweringFixtures.UnregisteredGate
