import Clean.Ironwood.Fixtures.Layout
import Clean.Ironwood.Fixtures.MulLayout
import Clean.Ironwood.Fixtures.MulSelMap
import Clean.Ironwood.Fixtures.MulPost
import Clean.Ironwood.Ecc.Mul

/-!
# VK-match test (Phase 2): variable-base scalar mul — LAYOUT (permutation σ + fixed values)

The layout counterpart of `TestVkMatchMul` (which checks the symbolic CS). It builds a Lean
mirror of `MulDumpCircuit::synthesize` (`halo2_gadgets/src/ecc/chip/dump.rs`) as a
`Circuit Fp Unit`, using the SAME region sequence Rust does — load the range-check table;
witness the base point (`base_x`/`base_y` on advices 0/1, row 0) and the scalar `alpha`
(advice 0, row 0) as raw equality-enabled cells; then run the ported `Mul.synthesize` on the
harness config. `Fixtures.Layout` reconstructs the four keygen-view layout products from the
resulting `Operations`.

## What this test establishes

The reconstruction **machinery** (`Fixtures/Layout.lean`) is validated GREEN against the dump:

* the keygen `Assembly` σ replay reproduces the fixture's σ from the fixture's own copy list
  (isolates the `permutation/keygen.rs` port from any layout question);
* the `loadTable` fixed extraction reproduces the full 2042-row table column
  (explicit block + row-0 default-fill, `usableRows = n − (blindingFactors + 1) = 2042`);
* the constants-column extraction reproduces the constants fixed column;
* the region-placement lockstep (`place`) reproduces the fixture's per-region start rows.

## VK-faithful layout (the end-to-end guards below are GREEN)

The end-to-end reconstruction of the copy list / σ / fixed against the ported
`Mul.synthesize` EQUALS the dump. `Ironwood.Ecc.Mul.mainRegion` lays the hi and lo halves
SIDE BY SIDE at the SAME rows (both `double_and_add` at `offHi = offLo = 1`, on the disjoint
`hi_config`/`lo_config` column sets — sharing only `x_p`/`y_p` = the base point, written with
equal values by both halves), exactly as Rust (`mul.rs:171-296`); complete rounds at 129 and
the LSB step at 135 follow, so the main region spans local rows 0..136 and the floor planner
places the overflow siblings at rows 139/139/140.

The fixture's `regions` placement line originally recorded start 0/1 for regions 3/6
(contradicting its own copyList — the init-add copies sit at absolute rows 2/3); it was
regenerated from the sibling-checkout `ecc::chip::layout_dump` harness (see the
`MulLayout.lean` header), whose ordered copy list reproduces the original dump's
byte-for-byte, pinning harness equivalence.

`#guard` equality is fine (D1).

Kept (with `TestVkMatchMul`) as the lookup/selector-compression half of the doc-test
suite — the fixed contents here include the range-check TABLE column, the constants
column, and 7 packed selector columns. See the header of `TestVkMatchAdd`.
-/

namespace Zcash.Circuits.Fixtures.Test.Layout

open Halo2
open Ecc.Add (add)
open Ecc.Mul (Config configure)
open Fixtures.Layout

/-- The harness config plus the columns `synthesize` needs for witnessing — built by the same
`configure` chain as `TestVkMatchMul.mulProgram` (`configure_mul` in `dump.rs`), returning the
advice columns and the lookup-table column too. -/
def setup : Config × (Fin 10 → Column .advice) × TableColumn :=
  let prog : Configure Fp (Config × (Fin 10 → Column .advice) × TableColumn) := do
    let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
    let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
    let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
    let a9 ← adviceColumn
    let tableIdx ← lookupTableColumn
    let constants ← fixedColumn
    enableConstant constants
    let advices : Fin 10 → Column .advice := ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    let lookupConfig ← LookupRangeCheck.configure 10 a9 tableIdx
    let addConfig ← add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)
    let cfg ← configure addConfig lookupConfig advices
    return (cfg, advices, tableIdx)
  (prog {}).1

def mulCfg : Config := setup.1
def mulAdvices : Fin 10 → Column .advice := setup.2.1
def mulTableIdx : TableColumn := setup.2.2

/-- A dummy witness (keygen never reads advice values). -/
def unknown : WitgenIR Fp 1 := .native fun _ => #v[(0 : Fp)]

/-- The Lean mirror of `MulDumpCircuit::synthesize`: table load, witness base, witness alpha,
then the ported variable-base scalar mul, on the harness columns. -/
def layoutProgram : Circuit Fp Unit := do
  -- load the 10-bit range-check table (`load_range_check_table`, dump.rs) → fixed col 0
  loadTable mulTableIdx ((List.range (2 ^ 10)).map (Nat.cast : ℕ → Fp))
  -- witness base point: base_x @ advices[0] row 0, base_y @ advices[1] row 0
  let base ← assignRegion "witness base" (do
    let x ← assignAdvice (mulAdvices 0) 0 unknown
    let y ← assignAdvice (mulAdvices 1) 0 unknown
    pure (x, y))
  -- witness alpha: advices[0] row 0
  let alpha ← assignRegion "witness alpha" (assignAdvice (mulAdvices 0) 0 unknown)
  -- the real deal
  let _ ← Ecc.Mul.synthesize mulCfg
    { alpha := alpha, base := { x := base.1, y := base.2 } }
  pure ()

/-- The reconstructed layout products, all from `layoutProgram.operations`. -/
def ops : Operations Fp := layoutProgram.operations
def starts : List ℕ := regionStarts ops mulLayout
def regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
def permCols : List ColRef := mulLayout.permColumns

def myCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  SimpleFloorPlanner.copyList permCols starts ops mulLayout.constants
def mySigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly mulLayout.n permCols.length myCopyList)
def myUsable : ℕ := usableRows mulLayout.n mulPost.adviceQueryLayout
def myFixed : List (ℕ × ℕ × ℕ) :=
  allFixed (ZMod.val : Fp → ℕ) myUsable mulSelMap ops starts regions mulLayout.constants

/-! ## Machinery validation (GREEN) -/

-- Region-placement lockstep: the reconstructed per-region start rows equal the fixture's
-- (in `assignRegion`-index order — `loadTable` consumes the fixture's `table_idx` slot).
#guard starts = (mulLayout.regions.filter (·.name ≠ "table_idx")).map (·.start)

-- Blinding-factor / usable-row computation (`n − (blindingFactors + 1)`).
#guard myUsable = 2042

-- keygen `Assembly` σ replay (`permutation/keygen.rs`), isolated from any layout question:
-- from the fixture's OWN ordered copy list it must reproduce the fixture's σ exactly.
#guard sigmaEntries (runAssembly mulLayout.n permCols.length mulLayout.copyList) = mulLayout.sigma

-- `loadTable` fixed extraction: the full 2042-row table column (explicit block + default-fill).
-- Layout-independent, so it matches the dump directly.
#guard tableFixed (ZMod.val : Fp → ℕ) myUsable ops = mulLayout.fixed.filter (·.1 = 0)

-- constants-column fixed extraction, straight from the allocation map.
#guard constantsFixed mulLayout.constants = mulLayout.fixed.filter (·.1 = 1)

/-! ## End-to-end reconstruction vs the ported `Mul.synthesize` — the Phase-2 targets

The reconstructed ordered copy list, the keygen σ, and the fixed values, from the ported
`Mul.synthesize`, all EQUAL the dump. DO NOT weaken these checks: on a divergence, the
ordered copy list pinpoints the first mismatched placement (`firstDiff` below is the
diagnostic). -/

#guard myCopyList = mulLayout.copyList
#guard mySigma = mulLayout.sigma
#guard myFixed = sortFixed mulLayout.fixed

/-- First index at which two lists differ, with both entries — the diagnostic to `#eval`
against `myCopyList`/`mulLayout.copyList` when a guard above breaks. -/
def firstDiff {α : Type} [DecidableEq α] (a b : List α) : Option (ℕ × α × α) :=
  (a.zip b).zipIdx.findSome? fun ((x, y), i) => if x = y then none else some (i, x, y)

end Zcash.Circuits.Fixtures.Test.Layout
