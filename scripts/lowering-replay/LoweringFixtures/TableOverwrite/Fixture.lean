import LoweringFixtures.TableOverlap.Fixture

/-! `TableOverlap` with the first region writing 8 into the default-fill range before the load.
Rust's table fill overwrites it with the default 2, as Lean's stream-ordered writes do. -/
namespace LoweringFixtures.TableOverwrite
open Halo2 Midnight Midnight.Keygen

def fixture : Export.Replay.Fixture :=
  { TableOverlap.fixture with ops := [
    .region "before" [.assignFixed ⟨0⟩ 5 8, .assignAdvice ⟨0⟩ 0 witness,
      .enableLookup (cleanLookup TableOverlap.lk) [⟨0, false⟩] 0],
    .loadTable ⟨⟨0⟩⟩ [2, 7, 9]] }

end LoweringFixtures.TableOverwrite
