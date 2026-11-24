import LoweringFixtures.Common

/-! The SHA-256 baseline on a 2^14 domain. -/
namespace LoweringFixtures.ShaK14

def fixture : Midnight.Export.Replay.Fixture := { sha with k := 14 }

end LoweringFixtures.ShaK14
