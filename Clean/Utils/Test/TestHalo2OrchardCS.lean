import Clean.Halo2.Orchard

namespace Halo2.Tests

/-- Sanity check that the idiomatic Halo2 builder currently constructs a
non-empty CS for the Orchard value-commitment target. Exact equality with the
Rust CS dump is the work item this module is being grown toward. -/
theorem orchardValueCommitCS_nonempty :
    Halo2.Orchard.orchardValueCommitCS.gates.length > 0 := by
  native_decide

end Halo2.Tests
