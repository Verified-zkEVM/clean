import LoweringFixtures.Common

/-! The zk.golf SHA-256 baseline, midnight-zk's `sha_preimage`; Rust's key must be midnight-zk's
`ShaPreImageCircuitVk`. -/
namespace LoweringFixtures.ShaBaseline

def fixture : Midnight.Export.Replay.Fixture := sha

end LoweringFixtures.ShaBaseline
