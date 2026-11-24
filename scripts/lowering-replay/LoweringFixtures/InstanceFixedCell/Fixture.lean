import LoweringFixtures.Ops.Fixture

/-! `Ops` with an in-region instance copy of a fixed cell. Rust's only in-region instance copy,
`assign_advice_from_instance`, copies an advice cell, so Lean rejects it. -/
namespace LoweringFixtures.InstanceFixedCell
open Halo2 Midnight

def fixture : Export.Replay.Fixture :=
  { Ops.fixture with ops := Ops.ops ++ [.region "late" [
      .assignFixed ⟨0⟩ 0 1, .constrainInstance (cell 2 0 .fixed 0) ⟨0⟩ 2]] }

end LoweringFixtures.InstanceFixedCell
