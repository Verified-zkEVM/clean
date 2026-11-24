import LoweringFixtures.AdditivePoseidon.Fixture

/-! `AdditivePoseidon` with `set_minimum_degree(2)`: the degree is unchanged but the pinned CS
reads `Some(2)`, so it is no longer the stdlib configuration and both sides key halo2's format. -/
namespace LoweringFixtures.PoseidonMinimumDegree
open Midnight Midnight.Keygen

def source : CS := ((setMinimumDegree 2).run Poseidon.configured).2

def fixture : Export.Replay.Fixture := { AdditivePoseidon.fixture with source := source }

#guard source.degree == Poseidon.configured.degree &&
  source.pinnedDebug != Poseidon.configured.pinnedDebug

end LoweringFixtures.PoseidonMinimumDegree
