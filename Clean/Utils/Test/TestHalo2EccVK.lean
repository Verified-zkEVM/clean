import Clean.Halo2.Fixtures.OrchardValueCommitVK

namespace Halo2.Tests

open Halo2

/-- Step 2 sanity check: compiling the Lean Halo2 description of the Orchard ECC
value-commitment circuit gives the pinned VK fixture generated from Rust. -/
theorem valueCommitOrchard_vk_matches_rust_fixture :
    Ecc.valueCommitOrchardVK = Fixtures.OrchardValueCommitVK.rustPinnedVK := by
  native_decide

/-- The framework computes VKs from circuit descriptions by projection. -/
theorem valueCommitOrchard_vk_is_compile :
    Ecc.valueCommitOrchard.compile = Ecc.valueCommitOrchardVK := rfl

end Halo2.Tests
