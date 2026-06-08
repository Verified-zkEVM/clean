import Clean.Halo2.Debug
import Clean.Halo2.Fixtures.RustPinnedCS

namespace Halo2.Tests

/-- The exact target for the full Orchard action circuit CS is checked into the
repo and available to Lean. -/
theorem orchardActionRustFixture_loaded :
    Halo2.Fixtures.RustPinnedCS.orchardAction.length > 0 := by
  native_decide

/-- The current Lean-side pinned CS candidate matches the Rust fixture on the
basic top-level dimensions of the pinned constraint system. -/
theorem orchardActionPinnedCS_topLevelCounts :
    let cs := Halo2.Orchard.Action.orchardActionPinnedCS
    cs.numFixedColumns = 29 ∧
    cs.numAdviceColumns = 10 ∧
    cs.numInstanceColumns = 1 ∧
    cs.numSelectors = 56 ∧
    cs.fixedQueries.length = 29 ∧
    cs.instanceQueries.length = 1 ∧
    cs.permutation.columns.length = 15 := by
  native_decide

/-- The current builder renders a non-empty Halo2-style pinned CS. The final
version of this theorem should be strengthened to equality with the Rust fixture. -/
theorem orchardActionBuilder_renders_nonempty :
    (Halo2.Pinned.Debug.constraintSystem Halo2.Orchard.Action.orchardActionPinnedCS).length > 0 := by
  native_decide

end Halo2.Tests

namespace Halo2.Tests

/-- The Lean-rendered pinned CS now matches the Rust fixture through the complete
compressed top-level Orchard gate prefix. -/
theorem orchardActionPinnedCS_prefix_matches_rust :
    ((Halo2.Pinned.Debug.constraintSystem Halo2.Orchard.Action.plonkCircuitPinnedCS).take 118000 ==
      Halo2.Fixtures.RustPinnedCS.orchardAction.take 118000) = true := by
  native_decide

end Halo2.Tests
