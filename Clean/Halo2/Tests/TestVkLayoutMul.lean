import Clean.Halo2.Fixtures.Layout
import Clean.Halo2.Fixtures.MulLayout
import Clean.Halo2.Fixtures.MulSelMap
import Clean.Halo2.Fixtures.MulPost
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

## Port finding (reported, not fixed — see the `#eval` evidence and `Fixtures/Layout.lean`)

The end-to-end reconstruction of the copy list / σ / fixed against the **ported**
`Mul.synthesize` DIVERGES from the dump, and the divergence pinpoints a genuine layout bug in
the mul port (exactly what the ordered copy list is for):

`Ironwood.Ecc.Mul.synthesize` STACKS the hi/lo/complete phases of the main region VERTICALLY
(`Mul.offHi = 2`, `offLo = offHi + hiSpan = 129`, `offComp = offLo + loSpan = 257`; "each
child owns its rows", `Mul.lean:194-233`), making the `variable-base scalar mul` region ~264
rows tall. Rust (`halo2_gadgets/src/ecc/chip/mul.rs:171-235`) lays the hi and lo halves
SIDE-BY-SIDE at the SAME rows (both `double_and_add` at `offset = 1`, on the disjoint
`hi_config`/`lo_config` columns — sharing only `x_p`/`y_p` = the base point), so its main
region is ~137 rows (matching the dump: max touched row 152, and the overflow siblings placed
at row 139). Result: the ported main region's cells sit at different absolute rows than Rust's,
so the copy structure — and hence σ and the permutation VK — differs. The first copy-list
divergence is the init complete-addition's base copies (`offInit`-relative row vs the dump's
row 2) and the `z_init` self-copy (row 2 vs 3); everything sourced from the main region shifts
downstream. Making the port VK-faithful is a non-mechanical mul-layout redesign (the
disjoint-row scheme is the port's soundness strategy), so it is reported here, not patched.

`#guard`/`#eval` equality is fine (D1).
-/

namespace Halo2.Fixtures.Test.Layout

open Ironwood (Fp)
open Ironwood.Ecc.Add (add)
open Ironwood.Ecc.Mul (Config configure)
open Halo2.Fixtures.Layout

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
    let lookupConfig ← Ironwood.LookupRangeCheck.configure 10 a9 tableIdx
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
  let _ ← Ironwood.Ecc.Mul.synthesize mulCfg
    { alpha := alpha, base := { x := base.1, y := base.2 } }
  pure ()

/-- The reconstructed layout products, all from `layoutProgram.operations`. -/
def ops : Operations Fp := layoutProgram.operations
def starts : List ℕ := regionStarts ops mulLayout
def regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
def permCols : List ColRef := mulLayout.permColumns

def myCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  copyList permCols starts regions mulLayout.constants
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

/-! ## End-to-end reconstruction vs the ported `Mul.synthesize` — PORT DIVERGENCE

These three equalities are the ultimate Phase-2 targets. They currently FAIL, and the failure
is a REAL layout bug in the mul port (vertical stacking vs Rust's side-by-side hi/lo — see the
module docstring). They are left here, disabled, as the concrete acceptance criteria for the
mul-layout fix; DO NOT re-enable by weakening — re-enable once the port is made VK-faithful.

  #guard myCopyList = mulLayout.copyList
  #guard mySigma = mulLayout.sigma
  #guard myFixed = sortFixed mulLayout.fixed

Evidence of the divergence (the ordered copy list pinpoints it — first mismatch first): -/

/-- First index at which two lists differ, with both entries. -/
def firstDiff {α : Type} [DecidableEq α] (a b : List α) : Option (ℕ × α × α) :=
  (a.zip b).zipIdx.findSome? fun ((x, y), i) => if x = y then none else some (i, x, y)

-- first ordered-copy divergence: the init add's base copies land at the wrong (stacked) row.
#eval ("first copyList divergence (idx, mine, dump): ",
  firstDiff myCopyList mulLayout.copyList)
-- main-region height: Lean (stacked) vs the dump (side-by-side).
#eval ("main-region max copy row — Lean stacked vs Rust dump: ",
  myCopyList.foldl (fun m (_, r, _, r') => Nat.max m (Nat.max r r')) 0,
  mulLayout.copyList.foldl (fun m (_, r, _, r') => Nat.max m (Nat.max r r')) 0)

end Halo2.Fixtures.Test.Layout
