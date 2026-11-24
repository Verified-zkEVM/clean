import LoweringFixtures.Ops.Fixture

/-! `Ops` with an in-region instance copy of a cell of an earlier region. Rust's only
in-region instance copy, `assign_advice_from_instance`, assigns a cell of the current
region, so no Rust region records this copy here, and Lean rejects it. -/
namespace LoweringFixtures.EarlierInstance
open Halo2 Midnight

def fixture : Export.Replay.Fixture :=
  { Ops.fixture with ops := Ops.ops ++ [.region "late" [
      .assignAdvice ⟨1⟩ 0 witness, .constrainInstance (cell 0 1 .advice 0) ⟨0⟩ 2]] }

end LoweringFixtures.EarlierInstance
