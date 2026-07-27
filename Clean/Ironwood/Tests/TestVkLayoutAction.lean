import Clean.Ironwood.Fixtures.ActionSelMap
import Clean.Ironwood.Fixtures.Json
import Clean.Ironwood.Action.RealBases
import Clean.Ironwood.Action.CircuitPreIronwood
import Clean.Ironwood.Fixtures.Layout
import Clean.Ironwood.Action.Circuit

/-!
# VK-layout test: the full Orchard Action circuit

Reconstructs the keygen-view layout of the REAL orchard `Circuit` — region placements,
the ordered copy list, σ, and the complete fixed columns (generator table, constants,
packed selectors, `q_s2`/`fixed_y_q`, the six fixed-base window tables) — from the
ported `Action.Circuit.configure` (already CS-matched by `TestVkMatchAction`) plus a
synthesize mirror, and checks them against the `dump_layout_action` fixture
(`actionLayout.json`, loaded at `#eval` time — see `Fixtures/Json.lean`).

The mirror is the `TestVkLayoutNoteCommit` pattern: identical region stream to
`Action.Circuit.synthesize`, with the six `FixedBase`-parameterized fixed-base-mul
sites expanded data-level (`*.synthesize <base>Data`) since the layout test only has
the dumped window tables, and every other child called through its bundle.
-/

namespace Zcash.Circuits.Fixtures.Test.LayoutAction

open Halo2 Fixtures Fixtures.Layout
open Specs.Sinsemilla (Generators)
open Action.Circuit (Config configure orchardGate loadPrivate
  ANCHOR ENABLE_SPEND ENABLE_OUTPUT CV_NET_X CV_NET_Y NF_OLD RK_X RK_Y CMX)

/-! ## Generators and config -/

/-- The real proof-carrying generator family; the layout guards below cross-validate
its table (extracted into `SinsemillaGenerators.lean`) against the dump's fixed
columns. -/
def aG : Generators := Specs.Sinsemilla.orchardGenerators

/-- The REAL ported configure (CS-matched by `TestVkMatchAction`). -/
def aCfg : Config := (configure aG {}).1

/-- Keygen never evaluates witness programs (`Value::unknown()`). -/
def unk : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp) := pure (.const 0)
def unkPoint : Witgen.MOver Fp (AssignedCell Fp) (Point (FExpr Fp)) :=
  pure { x := .const 0, y := .const 0 }
def unkNat : Witgen.MOver Fp (AssignedCell Fp) (NExpr Fp) := pure (.const 0)

/-! ## The synthesize mirror (identical region stream to `Action.Circuit.synthesize`,
fixed-base-mul sites data-level) -/

/-- The keygen witness set (all programs `Value::unknown()`-shaped). -/
def aW : Action.Circuit.Witnesses Fp :=
  { psiOld := unk, rhoOld := unk, nk := unk, vOld := unk, vNew := unk, psiNew := unk,
    magnitude := unk, sign := unk,
    cmOld := unkPoint, gdOld := unkPoint, akP := unkPoint, pkDOld := unkPoint,
    gdNew := unkPoint, pkdNew := unkPoint,
    rcv := unkNat, alpha := unkNat, rivk := unkNat,
    rcmOld := unkNat, rcmNew := unkNat,
    merkleSib := fun _ => .native fun _ => #v[(0 : Fp)],
    merkleSwap := fun _ _ => false }

/-- THE REAL ironwood (post-NU 6.3) circuit, at the REAL certified bases. -/
def aProgram : Circuit Fp Unit :=
  Action.Circuit.synthesize aG Action.orchardBases aW aCfg

/-- The real pre-ironwood (fixed post-NU 6.2) circuit, at the same bases. -/
def aProgramBase : Circuit Fp Unit := do
  let _ ← Action.CircuitPreIronwood.synthesize aG
    Action.orchardBases aW aCfg
  pure ()

/-! ## The reconstructed layout products vs the ported Action stack (ironwood)

All checks live in ONE `#eval` so the shared reconstruction (ops → regions → copy list →
σ → fixed) evaluates exactly once; the fixture is loaded from `actionLayout.json`
(pinned content hash — see `Fixtures/Json.lean`). Split into per-product checks
temporarily when debugging a mismatch. -/
#eval show IO Unit from do
  let fx ← Json.loadLayoutFixture "Clean/Ironwood/Fixtures/actionLayout.json"
    0x51cd2f7ce66a8c7
  let ops : Operations Fp := aProgram.operations
  let regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
  -- Region starts from the fixture placements (the single `generator_table` slot is the
  -- three `loadTable`s' — filtered).
  let starts : List ℕ := ((fx.regions.filter (·.name ≠ "generator_table")).map (·.start))
  let permCols : List ColRef := fx.permColumns
  let copyList : List (ℕ × ℕ × ℕ × ℕ) := V1.copyList permCols starts ops fx.constants
  let sigma : List (ℕ × ℕ × ℕ × ℕ) :=
    sigmaEntries (runAssembly fx.n permCols.length copyList)
  -- Usable rows `n − (blindingFactors + 1)` (blinding = 5, dump META).
  let usable : ℕ := 2042
  let fixed : List (ℕ × ℕ × ℕ) :=
    sortFixed (dedupFixed
      (tableFixed (ZMod.val : Fp → ℕ) usable ops
        ++ constantsFixed fx.constants
        ++ selectorFixed actionSelMap (activations starts regions)
        ++ regionAssignFixed (ZMod.val : Fp → ℕ) starts regions))
  let compiledFixed : List (ℕ × ℕ × ℕ) :=
    (Halo2.Layout.compileFixed usable actionSelMap
      ((Action.Circuit.configure aG {}).2.closeWithOperations ops) ops).map
        fun (column, row, value) => (column, row, ZMod.val value)
  Json.runChecks [
    -- keygen `Assembly` σ replay from the fixture's OWN ordered copy list
    ("σ replay from fixture copyList",
      decide (sigmaEntries (runAssembly fx.n permCols.length fx.copyList) = fx.sigma)),
    -- Region lockstep: the fixture's non-table region names, in order, are this side's
    -- assignRegion sequence.
    ("region-name lockstep",
      decide ((fx.regions.filter (·.name ≠ "generator_table")).map (·.name)
        = (regionSlots ops).filterMap fun (isRegion, nm) => if isRegion then some nm else none)),
    -- the ordered copy list (order-sensitive — σ's cycle rotations depend on it)
    ("copyList", decide (copyList = fx.copyList)),
    -- the keygen permutation σ
    ("σ", decide (sigma = fx.sigma)),
    -- the full fixed contents
    ("fixed contents", decide (fixed = sortFixed fx.fixed)),
    -- the field-valued semantic compiler matches the same V1 keygen layout
    ("field-valued fixed compiler",
      decide (compiledFixed = sortFixed fx.fixed))]

end Zcash.Circuits.Fixtures.Test.LayoutAction
