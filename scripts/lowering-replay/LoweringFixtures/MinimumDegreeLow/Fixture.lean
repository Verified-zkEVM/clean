import LoweringFixtures.MinimumDegree.Fixture

/-! `MinimumDegree` with `set_minimum_degree(2)`: the degree stays the gates', the pinned CS
still prints `Some(2)`. -/
namespace LoweringFixtures.MinimumDegreeLow

def fixture : Midnight.Export.Replay.Fixture := MinimumDegree.fixtureOf 2

end LoweringFixtures.MinimumDegreeLow
