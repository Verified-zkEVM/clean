import Clean.Ironwood.Tests.TestVkLayoutAction

/-!
# VK-layout test: the pre-ironwood (fixed post-NU 6.2) Action circuit

The base-circuit counterpart of `TestVkLayoutAction`: the same mirror WITHOUT the
cross-address stage (`aProgramBase`), against the `actionBase` dump (byte-identical to
the 0.14.0 circuit — verified on the ironwood branch), loaded from
`actionBaseLayout.json` at `#eval` time. The constraint system (and so the SelMap) is
shared between the two versions.
-/

namespace Zcash.Circuits.Fixtures.Test.LayoutActionBase

open Halo2 Fixtures Fixtures.Layout
open Fixtures.Test.LayoutAction (aProgramBase)

/-! All checks live in ONE `#eval` so the shared reconstruction (ops → regions → copy
list → σ → fixed) evaluates exactly once; the fixture is loaded from
`actionBaseLayout.json` (pinned content hash — see `Fixtures/Json.lean`). -/
#eval show IO Unit from do
  let fx ← Json.loadLayoutFixture "Clean/Ironwood/Fixtures/actionBaseLayout.json"
    0x193f3922aa59191e
  let ops : Operations Fp := aProgramBase.operations
  let regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
  let starts : List ℕ := ((fx.regions.filter (·.name ≠ "generator_table")).map (·.start))
  let permCols : List ColRef := fx.permColumns
  let copyList : List (ℕ × ℕ × ℕ × ℕ) := V1.copyList permCols starts ops fx.constants
  let sigma : List (ℕ × ℕ × ℕ × ℕ) :=
    sigmaEntries (runAssembly fx.n permCols.length copyList)
  let usable : ℕ := 2042
  let fixed : List (ℕ × ℕ × ℕ) :=
    sortFixed (dedupFixed
      (tableFixed (ZMod.val : Fp → ℕ) usable ops
        ++ constantsFixed fx.constants
        ++ selectorFixed actionSelMap (activations starts regions)
        ++ regionAssignFixed (ZMod.val : Fp → ℕ) starts regions))
  Json.runChecks [
    -- keygen `Assembly` σ replay from the fixture's OWN ordered copy list
    ("σ replay from fixture copyList",
      decide (sigmaEntries (runAssembly fx.n permCols.length fx.copyList) = fx.sigma)),
    -- Region lockstep.
    ("region-name lockstep",
      decide ((fx.regions.filter (·.name ≠ "generator_table")).map (·.name)
        = (regionSlots ops).filterMap fun (isRegion, nm) => if isRegion then some nm else none)),
    -- the ordered copy list, σ, and the full fixed contents
    ("copyList", decide (copyList = fx.copyList)),
    ("σ", decide (sigma = fx.sigma)),
    ("fixed contents", decide (fixed = sortFixed fx.fixed))]

end Zcash.Circuits.Fixtures.Test.LayoutActionBase
