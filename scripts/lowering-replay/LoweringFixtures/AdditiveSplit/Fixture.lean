import LoweringFixtures.AdditiveBitPair.Fixture

/-! `AdditiveBitPair` with its equations in two additive gates on one selector (two trash
arguments, two blinding rows), the second querying `product` first. -/
namespace LoweringFixtures.AdditiveSplit

def fixture : Midnight.Export.Replay.Fixture := AdditiveBitPair.fixtureOf true

end LoweringFixtures.AdditiveSplit
