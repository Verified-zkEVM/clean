import Clean.Halo2.Fixtures.Layout
import Clean.Halo2.Fixtures.FullWidthLayout
import Clean.Halo2.Fixtures.FullWidthSelMap
import Clean.Halo2.Fixtures.FullWidthParams
import Clean.Ironwood.Ecc.MulFixed.FullWidth

/-!
# VK-match test (layout): full-width fixed-base mul — σ + fixed values

Mirror of the sibling-checkout `FullWidthDumpCircuit` (see the fixture headers): the
isolated full-width chain, one `[scalar]FullWidth` with `Value::unknown()` — the scalar
is witnessed inside as 85 window cells, so the Lean mirror passes dummy window hints
(keygen never evaluates witness programs). No table/lookup and no witness prelude: the
fixed-base mul's regions are the whole circuit.

`#guard` equality is fine (D1).
-/

namespace Halo2.Fixtures.Test.LayoutFullWidth

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed.FullWidth (Config configure)
open Halo2.Fixtures.Layout

/-- The harness config: the Rust `FullWidthDumpCircuit` chain (10 advices, 8 Lagrange
fixed, constants, `add_incomplete(a0..a3)`, `add(a0..a8)`, `mul_fixed(lagrange, a4, a5)`,
`full_width`). -/
def setup : Config × (Fin 10 → Column .advice) :=
  let prog : Configure Fp (Config × (Fin 10 → Column .advice)) := do
    let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
    let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
    let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
    let a9 ← adviceColumn
    let l0 ← fixedColumn; let l1 ← fixedColumn; let l2 ← fixedColumn
    let l3 ← fixedColumn; let l4 ← fixedColumn; let l5 ← fixedColumn
    let l6 ← fixedColumn; let l7 ← fixedColumn
    let constants ← fixedColumn
    enableConstant constants
    let advices : Fin 10 → Column .advice := ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    let addIncompleteConfig ← Ironwood.Ecc.AddIncomplete.add.configure (a0, a1, a2, a3)
    let addConfig ← Ironwood.Ecc.Add.add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)
    let mulFixedConfig ← Ironwood.Ecc.MulFixed.configure
      ![l0, l1, l2, l3, l4, l5, l6, l7] a4 a5 addConfig addIncompleteConfig
    let cfg ← configure mulFixedConfig
    return (cfg, advices)
  (prog {}).1

def fwCfg : Config := setup.1

/-- The Lean mirror of `FullWidthDumpCircuit::synthesize`: one full-width mul with dummy
window hints (`Value::unknown()` keygen view). -/
def layoutProgram : Circuit Fp Unit := do
  let _ ← Ironwood.Ecc.MulFixed.FullWidth.synthesize fullWidthData fwCfg
    (Vector.replicate 85 (.const (0 : Fp)))
  pure ()

def ops : Operations Fp := layoutProgram.operations
def starts : List ℕ := regionStarts ops fullWidthLayout
def regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
def permCols : List ColRef := fullWidthLayout.permColumns

def myCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  copyList permCols starts regions fullWidthLayout.constants
def mySigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly fullWidthLayout.n permCols.length myCopyList)
/-- Usable rows `n − (blindingFactors + 1)` (blinding = 5, dump META). -/
def myUsable : ℕ := 2042
def myFixed : List (ℕ × ℕ × ℕ) :=
  allFixed (ZMod.val : Fp → ℕ) myUsable fullWidthSelMap ops starts regions
    fullWidthLayout.constants

#guard starts = fullWidthLayout.regions.map (·.start)
#guard sigmaEntries (runAssembly fullWidthLayout.n permCols.length fullWidthLayout.copyList)
  = fullWidthLayout.sigma
#guard myCopyList = fullWidthLayout.copyList
#guard mySigma = fullWidthLayout.sigma
#guard myFixed = sortFixed fullWidthLayout.fixed

end Halo2.Fixtures.Test.LayoutFullWidth
