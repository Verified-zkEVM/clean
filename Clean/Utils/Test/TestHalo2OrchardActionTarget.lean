import Clean.Halo2.Debug

namespace Halo2.Tests

/-- The exact target for the full Orchard action circuit CS is checked into the
repo and available to Lean. This test is intentionally not the final equality
claim; it guards that the large fixture is loaded while the builder is completed. -/
theorem orchardActionRustFixture_loaded :
    Halo2.Fixtures.RustPinnedCS.orchardAction.length > 0 := by
  native_decide

/-- The current builder has begun constructing the full action CS. The final
version of this theorem should be strengthened to equality with the Rust fixture. -/
theorem orchardActionBuilder_renders_nonempty :
    (Halo2.Pinned.Debug.constraintSystem Halo2.Orchard.Action.orchardActionCS).length > 0 := by
  native_decide

end Halo2.Tests
