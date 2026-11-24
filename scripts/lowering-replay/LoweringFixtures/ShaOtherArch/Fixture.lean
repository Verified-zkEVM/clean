import LoweringFixtures.Common

/-! The SHA-256 circuit declared under the default architecture, whose stdlib configuration it
is not: both key it as a plain halo2 key. -/
namespace LoweringFixtures.ShaOtherArch

def fixture : Midnight.Export.Replay.Fixture := { sha with architecture := {} }

end LoweringFixtures.ShaOtherArch
