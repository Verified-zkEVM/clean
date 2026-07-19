import Clean.Halo2.Fixtures.ActionLayout
import Clean.Halo2.Fixtures.ActionSelMap
import Clean.Ironwood.Action.RealBases
import Clean.Ironwood.Action.CircuitPreIronwood
import Clean.Halo2.Fixtures.Layout
import Clean.Halo2.Tests.TestVkMatchSinsemilla
import Clean.Ironwood.Action.Circuit

/-!
# VK-layout test: the full Orchard Action circuit

Reconstructs the keygen-view layout of the REAL orchard `Circuit` — region placements,
the ordered copy list, σ, and the complete fixed columns (generator table, constants,
packed selectors, `q_s2`/`fixed_y_q`, the six fixed-base window tables) — from the
ported `Action.Circuit.configure` (already CS-matched by `TestVkMatchAction`) plus a
synthesize mirror, and checks them against the `dump_layout_action` fixture.

The mirror is the `TestVkLayoutNoteCommit` pattern: identical region stream to
`Action.Circuit.synthesize`, with the six `FixedBase`-parameterized fixed-base-mul
sites expanded data-level (`*.synthesize <base>Data`) since the layout test only has
the dumped window tables, and every other child called through its bundle.
-/

namespace Halo2.Fixtures.Test.LayoutAction

open Halo2 Halo2.Fixtures Halo2.Fixtures.Layout
open Halo2.Ironwood (Fp)
open Orchard.Specs.Sinsemilla (Generators)
open Halo2.Fixtures.Test (sinsemillaS0 sinsemillaS0_onCurve)
open Halo2.Ironwood.Action.Circuit (Config configure orchardGate loadPrivate
  ANCHOR ENABLE_SPEND ENABLE_OUTPUT CV_NET_X CV_NET_Y NF_OLD RK_X RK_Y CMX)

/-! ## Dump-derived generators, domain points, config -/

/-- The generator-table x/y columns read back from the dump (fixed cols 1/2). -/
def aTblCol (c : ℕ) : Array ℕ := Id.run do
  let mut arr : Array ℕ := Array.replicate 1024 0
  for (c', r, v) in actionLayout.fixed do
    if c' = c ∧ r < 1024 then arr := arr.set! r v
  return arr

def aTblX : Array ℕ := aTblCol 1
def aTblY : Array ℕ := aTblCol 2

/-- The real proof-carrying generator family; the layout guards below cross-validate
its table (extracted into `SinsemillaGenerators.lean`) against the dump's fixed
columns. -/
def aG : Generators := Orchard.Specs.Sinsemilla.orchardGenerators

/-- `Q_MERKLE_CRH` (orchard `constants/sinsemilla.rs:56`). -/
def merkleQ : Orchard.Point Fp :=
  { x := (9991206725476878888751475603038274618448000607209514551456795194094072219296 : Fp),
    y := (24209798415301550423396126020228723009317736024280831393239261884225294625378 : Fp) }

theorem merkleQ_onCurve : merkleQ.OnCurve := by
  show merkleQ.y ^ 2 = merkleQ.x ^ 3 + Orchard.pallasB
  decide

/-- `Q_COMMIT_IVK_M_GENERATOR` (orchard `constants/sinsemilla.rs:44`). -/
def ivkQ : Orchard.Point Fp :=
  { x := (2593820817260930114322133467408868473290945477826616247349533151445648376562 : Fp),
    y := (12214744946019415453501880094709511126888074367290315326445800415816181472958 : Fp) }

theorem ivkQ_onCurve : ivkQ.OnCurve := by
  show ivkQ.y ^ 2 = ivkQ.x ^ 3 + Orchard.pallasB
  decide

/-- `Q_NOTE_COMMITMENT_M_GENERATOR` (orchard `constants/sinsemilla.rs:32`). -/
def noteQ : Orchard.Point Fp :=
  { x := (10629404576683096409262958701336170057000067777256141967953463442979689100381 : Fp),
    y := (22898949290933268079297281211505753011910178734473470279111609228438645877859 : Fp) }

theorem noteQ_onCurve : noteQ.OnCurve := by
  show noteQ.y ^ 2 = noteQ.x ^ 3 + Orchard.pallasB
  decide

/-- The REAL ported configure (CS-matched by `TestVkMatchAction`). -/
def aCfg : Config := (configure aG {}).1

/-- Keygen never evaluates witness programs (`Value::unknown()`). -/
def unk : WitgenIR Fp 1 := .native fun _ => #v[(0 : Fp)]
def unkPoint : Orchard.Point (FExpr Fp) := { x := .const 0, y := .const 0 }
def unkWindows : Vector (FExpr Fp) 85 := Vector.replicate 85 (.const (0 : Fp))

/-! ## The synthesize mirror (identical region stream to `Action.Circuit.synthesize`,
fixed-base-mul sites data-level) -/

/-- The keygen witness set (all programs `Value::unknown()`-shaped). -/
def aW : Ironwood.Action.Circuit.Witnesses :=
  { psiOld := unk, rhoOld := unk, nk := unk, vOld := unk, vNew := unk, psiNew := unk,
    magnitude := unk, sign := unk,
    cmOld := unkPoint, gdOld := unkPoint, akP := unkPoint, pkDOld := unkPoint,
    gdNew := unkPoint, pkdNew := unkPoint,
    rcvWindows := unkWindows, alphaWindows := unkWindows, rivkWindows := unkWindows,
    rcmOldWindows := unkWindows, rcmNewWindows := unkWindows,
    merkleSib := fun _ => unk, merkleSwap := fun _ _ => false }

/-- THE REAL ironwood (post-NU 6.3) circuit, at the REAL certified bases. -/
def aProgram : Circuit Fp Unit :=
  Ironwood.Action.Circuit.synthesize aG Ironwood.Action.orchardBases aW aCfg

/-- The real pre-ironwood (fixed post-NU 6.2) circuit, at the same bases. -/
def aProgramBase : Circuit Fp Unit := do
  let _ ← Ironwood.Action.CircuitPreIronwood.synthesize aG
    Ironwood.Action.orchardBases aW aCfg
  pure ()

/-! ## The reconstructed layout products (ironwood) -/

def aOps : Operations Fp := aProgram.operations
def aRegions : List (ℕ × RegionOperations Fp) := (indexedRegions aOps 0).1

/-- Region starts from the fixture placements (the single `generator_table` slot is the
three `loadTable`s' — filtered). -/
def aStarts : List ℕ :=
  ((actionLayout.regions.filter (·.name ≠ "generator_table")).map (·.start))

def aPermCols : List ColRef := actionLayout.permColumns

def aCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  copyListDeferred aPermCols aStarts aOps actionLayout.constants
def aSigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly actionLayout.n aPermCols.length aCopyList)
/-- Usable rows `n − (blindingFactors + 1)` (blinding = 5, dump META). -/
def aUsable : ℕ := 2042
def aFixed : List (ℕ × ℕ × ℕ) :=
  sortFixed (dedupFixed
    (tableFixed (ZMod.val : Fp → ℕ) aUsable aOps
      ++ constantsFixed actionLayout.constants
      ++ selectorFixed actionSelMap (activations aStarts aRegions)
      ++ assignedFixed (ZMod.val : Fp → ℕ) aStarts aRegions))

/-! ## Machinery validation -/

-- keygen `Assembly` σ replay from the fixture's OWN ordered copy list.
#guard sigmaEntries (runAssembly actionLayout.n aPermCols.length
  actionLayout.copyList) = actionLayout.sigma

-- Region lockstep: the fixture's non-table region names, in order, are this side's
-- assignRegion sequence.
#guard (actionLayout.regions.filter (·.name ≠ "generator_table")).map (·.name)
  = (regionSlots aOps).filterMap fun (isRegion, nm) => if isRegion then some nm else none

/-! ## End-to-end reconstruction vs the ported Action stack -/

-- the ordered copy list (order-sensitive — σ's cycle rotations depend on it)
#guard aCopyList = actionLayout.copyList

-- the keygen permutation σ
#guard aSigma = actionLayout.sigma

-- the full fixed contents
#guard aFixed = sortFixed actionLayout.fixed

end Halo2.Fixtures.Test.LayoutAction
