import LoweringFixtures.LookupTableSelfQuery.Fixture

/-! `LookupTableSelfQuery` with the gate querying the table column at rotation 1. -/
namespace LoweringFixtures.GateFixedRotation
open Midnight

def fixture : Export.Replay.Fixture := LookupTableSelfQuery.fixtureAt 1

end LoweringFixtures.GateFixedRotation
