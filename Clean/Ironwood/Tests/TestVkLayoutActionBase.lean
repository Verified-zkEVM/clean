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

def bOps : Operations Fp := aProgramBase.operations
def bRegions : List (ℕ × RegionOperations Fp) := (indexedRegions bOps 0).1

def bStarts : List ℕ :=
  ((actionBaseLayout.regions.filter (·.name ≠ "generator_table")).map (·.start))

def bPermCols : List ColRef := actionBaseLayout.permColumns

def bCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  copyListDeferred bPermCols bStarts bOps actionBaseLayout.constants
def bSigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly actionBaseLayout.n bPermCols.length bCopyList)
def bUsable : ℕ := 2042
def bFixed : List (ℕ × ℕ × ℕ) :=
  sortFixed (dedupFixed
    (tableFixed (ZMod.val : Fp → ℕ) bUsable bOps
      ++ constantsFixed actionBaseLayout.constants
      ++ selectorFixed actionSelMap (activations bStarts bRegions)
      ++ assignedFixed (ZMod.val : Fp → ℕ) bStarts bRegions))

-- keygen `Assembly` σ replay from the fixture's OWN ordered copy list.
#guard sigmaEntries (runAssembly actionBaseLayout.n bPermCols.length
  actionBaseLayout.copyList) = actionBaseLayout.sigma

-- Region lockstep.
#guard (actionBaseLayout.regions.filter (·.name ≠ "generator_table")).map (·.name)
  = (regionSlots bOps).filterMap fun (isRegion, nm) => if isRegion then some nm else none

-- the ordered copy list, σ, and the full fixed contents
#guard bCopyList = actionBaseLayout.copyList
#guard bSigma = actionBaseLayout.sigma
#guard bFixed = sortFixed actionBaseLayout.fixed

end Halo2.Ironwood.Fixtures.Test.LayoutActionBase
