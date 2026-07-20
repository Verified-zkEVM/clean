import Clean.Ironwood.Tests.TestVkLayoutAction
import Clean.Ironwood.Fixtures.ActionBaseLayout

/-!
# VK-layout test: the pre-ironwood (fixed post-NU 6.2) Action circuit

The base-circuit counterpart of `TestVkLayoutAction`: the same mirror WITHOUT the
cross-address stage (`aProgramBase`), against the `actionBase` dump (byte-identical to
the 0.14.0 circuit — verified on the ironwood branch). The constraint system (and so
the SelMap) is shared between the two versions.
-/

namespace Halo2.Ironwood.Fixtures.Test.LayoutActionBase

open Halo2 Halo2.Ironwood.Fixtures Halo2.Ironwood.Fixtures.Layout
open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Fixtures.Test.LayoutAction (aProgramBase)

/-! All checks live in ONE `#guard` so the shared reconstruction (ops → regions → copy list
→ σ → fixed) evaluates exactly once: each `#guard` re-runs its whole `def` dependency chain
(defs are not memoized across commands), so the previous five separate guards materialised
the full circuit ops ~4× over. The intermediate values are bound with `let` INSIDE the guard
so the interpreter shares them across the conjuncts. Split back into per-product guards
temporarily when debugging a mismatch. -/
#guard
  let ops : Operations Fp := aProgramBase.operations
  let regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
  let starts : List ℕ :=
    ((actionBaseLayout.regions.filter (·.name ≠ "generator_table")).map (·.start))
  let permCols : List ColRef := actionBaseLayout.permColumns
  let copyList : List (ℕ × ℕ × ℕ × ℕ) :=
    V1.copyList permCols starts ops actionBaseLayout.constants
  let sigma : List (ℕ × ℕ × ℕ × ℕ) :=
    sigmaEntries (runAssembly actionBaseLayout.n permCols.length copyList)
  let usable : ℕ := 2042
  let fixed : List (ℕ × ℕ × ℕ) :=
    sortFixed (dedupFixed
      (tableFixed (ZMod.val : Fp → ℕ) usable ops
        ++ constantsFixed actionBaseLayout.constants
        ++ selectorFixed actionSelMap (activations starts regions)
        ++ regionAssignFixed (ZMod.val : Fp → ℕ) starts regions))
  -- keygen `Assembly` σ replay from the fixture's OWN ordered copy list
  decide (sigmaEntries (runAssembly actionBaseLayout.n permCols.length
      actionBaseLayout.copyList) = actionBaseLayout.sigma)
  -- Region lockstep.
  && decide ((actionBaseLayout.regions.filter (·.name ≠ "generator_table")).map (·.name)
      = (regionSlots ops).filterMap fun (isRegion, nm) => if isRegion then some nm else none)
  -- the ordered copy list, σ, and the full fixed contents
  && decide (copyList = actionBaseLayout.copyList)
  && decide (sigma = actionBaseLayout.sigma)
  && decide (fixed = sortFixed actionBaseLayout.fixed)

end Halo2.Ironwood.Fixtures.Test.LayoutActionBase
