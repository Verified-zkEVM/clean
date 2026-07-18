import Clean.Halo2.Fixtures.Layout
import Clean.Halo2.Fixtures.ShortLayout
import Clean.Halo2.Fixtures.ShortSelMap
import Clean.Halo2.Fixtures.ShortParams
import Clean.Ironwood.Ecc.MulFixed.Short

/-!
# VK-match test (layout): short signed fixed-base mul — σ + fixed values

Mirror of the sibling-checkout `ShortDumpCircuit` (see the fixture headers): the isolated
short chain — witness `(magnitude, sign)` on advices 0/1 at row 0, then one
`[sign·magnitude]Short` (`Value::unknown()` keygen view).

`#guard` equality is fine (D1).
-/

namespace Halo2.Fixtures.Test.LayoutShort

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed.Short (Config configure)
open Halo2.Fixtures.Layout

/-- The harness config: the Rust `ShortDumpCircuit` chain. -/
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

def shCfg : Config := setup.1
def shAdvices : Fin 10 → Column .advice := setup.2

/-- A dummy witness (keygen never reads advice values). -/
def unknown : WitgenIR Fp 1 := .native fun _ => #v[(0 : Fp)]

/-- The Lean mirror of `ShortDumpCircuit::synthesize`. -/
def layoutProgram : Circuit Fp Unit := do
  let (m, s) ← assignRegion "witness magnitude_sign" (do
    let m ← assignAdvice (shAdvices 0) 0 unknown
    let s ← assignAdvice (shAdvices 1) 0 unknown
    pure (m, s))
  let _ ← Ironwood.Ecc.MulFixed.Short.synthesize shortData shCfg
    { magnitude := m, sign := s }
  pure ()

def ops : Operations Fp := layoutProgram.operations
def starts : List ℕ := regionStarts ops shortLayout
def regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
def permCols : List ColRef := shortLayout.permColumns

def myCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  copyList permCols starts regions shortLayout.constants
def mySigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly shortLayout.n permCols.length myCopyList)
/-- Usable rows `n − (blindingFactors + 1)` (blinding = 5, dump META). -/
def myUsable : ℕ := 2042
def myFixed : List (ℕ × ℕ × ℕ) :=
  allFixed (ZMod.val : Fp → ℕ) myUsable shortSelMap ops starts regions
    shortLayout.constants

#guard starts = shortLayout.regions.map (·.start)
#guard sigmaEntries (runAssembly shortLayout.n permCols.length shortLayout.copyList)
  = shortLayout.sigma
#guard myCopyList = shortLayout.copyList
#guard mySigma = shortLayout.sigma
#guard myFixed = sortFixed shortLayout.fixed

end Halo2.Fixtures.Test.LayoutShort
