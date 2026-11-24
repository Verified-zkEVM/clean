import LoweringFixtures.InstanceCopyOrder.Fixture

/-! `InstanceCopyOrder` plus a region whose only operation is an instance copy into an advice
cell at row 1 that nothing else assigns. `assign_advice_from_instance` assigns it, so Rust
keys a two-row region; `Canonical.ops` assigns it before the copy. -/
namespace LoweringFixtures.InstanceCopyUnassigned
open Halo2 Midnight

def fixture : Export.Replay.Fixture :=
  { InstanceCopyOrder.fixture with ops := InstanceCopyOrder.ops false ++ [
      .region "only copy" [.constrainInstance (cell 2 1 .advice 0) ⟨0⟩ 4],
      .region "after" [.assignAdvice ⟨1⟩ 0 witness, .constrainEqual (cell 3 0 .advice 1) (cell 2 1 .advice 0)]] }

-- vk-export's `layout` reads the raw stream as Rust.
#guard (Export.layout fixture.source fixture.ops fixture.k).regionStarts == [0, 3, 3, 4]

end LoweringFixtures.InstanceCopyUnassigned
