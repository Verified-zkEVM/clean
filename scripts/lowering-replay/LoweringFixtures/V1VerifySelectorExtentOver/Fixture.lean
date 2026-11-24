import LoweringFixtures.V1VerifySelectorExtent.Fixture

/-! `V1VerifySelectorExtent` plus a tenth constant from another empty-shape region: V1 has nine
positions (`NotEnoughColumnsForConstants`). Simple rejects both (constants name a later region). -/
namespace LoweringFixtures.V1VerifySelectorExtentOver
open Halo2 Midnight

def fixture : Export.Replay.Fixture :=
  { V1VerifySelectorExtent.fixture with ops := V1VerifySelectorExtent.ops ++
      [.region "extra" [.constrainConstant (cell 3 0 .advice 0) 11]] }

end LoweringFixtures.V1VerifySelectorExtentOver
