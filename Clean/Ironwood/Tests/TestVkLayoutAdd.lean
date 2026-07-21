import Clean.Ironwood.Fixtures.Layout
import Clean.Ironwood.Fixtures.AddLayout
import Clean.Ironwood.Fixtures.AddSelMap
import Clean.Ironwood.Fixtures.AddPost
import Clean.Ironwood.Tests.TestVkMatchAdd

/-!
# VK-layout test: the complete-addition gadget — σ + fixed values

The layout half of the minimal doc-test pair (CS half: `TestVkMatchAdd`). Mirror of the
sibling-checkout `AddDumpCircuit` (`ecc::chip::layout_dump::dump_layout_add`): the same
9-advice configure as the CS test, synthesizing a `"witness pq"` region (the four input
coordinates as `Value::unknown()` cells on `a0..a3`, row 0) followed by one
`add::Config::assign_region` — here the ported `Add.add` bundle behind
`addFormal`.

This is the smallest possible end-to-end layout match, exercising every keygen-view
product on a two-region circuit:

* region-placement lockstep (`"witness pq"` at row 0, the add region at row 1);
* the ordered copy list — the four `p`/`q` coordinate copies from the witness cells
  into the gate window (`x_p, y_p, x_qr, y_qr` at row 1);
* the permutation σ replayed through the keygen `Assembly` port (four 2-cycles);
* the full fixed contents — here just the packed `q_add` selector column
  (`compress_selectors` output, via `addSelMap`), since this harness has no lookup
  table and no constants column. For those, see `TestVkLayoutMul`.

`#guard` equality is fine (D1).
-/

namespace Halo2.Ironwood.Fixtures.Test.LayoutAdd

open Ironwood (Fp)
open Ironwood.Ecc.Add (Config add)
open Halo2.Ironwood.Fixtures.Layout

/-- The harness config plus the columns `synthesize` needs for witnessing — the same
`configure` chain as `TestVkMatchAdd.addProgram`, returning the advice columns too. -/
def setup : Config × (Fin 9 → Column .advice) :=
  let prog : Configure Fp (Config × (Fin 9 → Column .advice)) := do
    let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
    let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
    let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
    let cfg ← add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)
    return (cfg, ![a0, a1, a2, a3, a4, a5, a6, a7, a8])
  (prog {}).1

def addCfg : Config := setup.1
def addAdvices : Fin 9 → Column .advice := setup.2

/-- A dummy witness (keygen never reads advice values). -/
def unknown : WitgenIR Fp 1 := .native fun _ => #v[(0 : Fp)]

/-- The Lean mirror of `AddDumpCircuit::synthesize`: witness `p`/`q`, then the ported
complete addition on the harness columns. -/
def layoutProgram : Circuit Fp Unit := do
  -- witness p = (a0, a1) row 0, q = (a2, a3) row 0
  let pq ← assignRegion "witness pq" (do
    let px ← assignAdvice (addAdvices 0) 0 unknown
    let py ← assignAdvice (addAdvices 1) 0 unknown
    let qx ← assignAdvice (addAdvices 2) 0 unknown
    let qy ← assignAdvice (addAdvices 3) 0 unknown
    pure (px, py, qx, qy))
  -- the real deal (chip.rs `add` region name)
  let _ ← addFormal.call addCfg
    { p := { x := pq.1, y := pq.2.1 }, q := { x := pq.2.2.1, y := pq.2.2.2 } }
  pure ()

/-- The reconstructed layout products, all from `layoutProgram.operations`. -/
def ops : Operations Fp := layoutProgram.operations
def starts : List ℕ := regionStarts ops addLayout
def regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
def permCols : List ColRef := addLayout.permColumns

def myCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  SimpleFloorPlanner.copyList permCols starts ops addLayout.constants
def mySigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly addLayout.n permCols.length myCopyList)
def myUsable : ℕ := usableRows addLayout.n addPost.adviceQueryLayout
def myFixed : List (ℕ × ℕ × ℕ) :=
  allFixed (ZMod.val : Fp → ℕ) myUsable addSelMap ops starts regions addLayout.constants

-- keygen `Assembly` σ replay from the fixture's OWN ordered copy list (isolates the
-- `permutation/keygen.rs` port from any layout question).
#guard sigmaEntries (runAssembly addLayout.n permCols.length addLayout.copyList)
  = addLayout.sigma

-- Region lockstep: names and placement rows.
#guard addLayout.regions.map (·.name)
  = (regionSlots ops).filterMap fun (isRegion, nm) => if isRegion then some nm else none
#guard starts = addLayout.regions.map (·.start)

-- the ordered copy list, σ, and the full fixed contents
#guard myCopyList = addLayout.copyList
#guard mySigma = addLayout.sigma
#guard myFixed = sortFixed addLayout.fixed

end Halo2.Ironwood.Fixtures.Test.LayoutAdd
