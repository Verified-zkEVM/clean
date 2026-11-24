import LoweringFixtures.Common

/-! The SHA-256 baseline. `MidnightVK` is written only by `setup_vk`, whose `MidnightCircuit`
fixes `SimpleFloorPlanner` (interface.rs:383-386), so Rust keys a V1 layout of this
configuration only through its own `Circuit` and `VerifyingKey::write`: halo2 bytes. Lean's
`keyFormat` and the harness's envelope give halo2 bytes under V1. -/
namespace LoweringFixtures.V1Envelope

def fixture : Midnight.Export.Replay.Fixture := sha

end LoweringFixtures.V1Envelope
