import Clean.Ironwood.Fixtures.Layout
import Clean.Ironwood.Fixtures.PoseidonLayout
import Clean.Ironwood.Fixtures.PoseidonSelMap
import Clean.Ironwood.Poseidon.Hash

/-!
# VK-match test (layout): the Poseidon `ConstantLength<2>` hash — σ + fixed values

Mirror of the sibling-checkout `PoseidonDumpCircuit` (see the fixture headers): the
orchard-shaped configure context (10 equality-enabled advices, 8 fixed columns with
`enable_constant` on the first; `state = advices[6..9]`, `partial_sbox = advices[5]`,
`rc_a = fixed[2..5]`, `rc_b = fixed[5..8]` — cf. `orchard/src/circuit.rs:354-389`),
synthesizing a `"witness inputs"` region (two `Value::unknown()` message words at
`a0`/`a1` row 0) followed by the real `Hash::<ConstantLength<2>>::init + hash` — here
the proven `Poseidon.hash` bundle (its region sequence: initial state, add input,
permute; the squeeze is region-free).

`#guard` equality is fine (D1).

Together with `TestVkMatchAdd` this is the kept small **documentation** of the
VK-matching approach — the layout half: region starts/names, the copy list, the
replayed permutation σ, and the full fixed-column contents (table + constants +
packed selectors + assigned cells). Whole-circuit correctness is checked by the
top-level `TestVkMatchAction`/`TestVkLayoutAction`/`TestVkLayoutActionBase`.
-/

namespace Halo2.Ironwood.Fixtures.Test.LayoutPoseidon

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Fixtures.Layout
open Halo2.Ironwood.Poseidon.Hash.ConstantLength (capacity)

/-- The harness config: the Rust `PoseidonDumpCircuit` chain, also returning the advice
columns the witness prelude uses. -/
def setup : Ironwood.Poseidon.Config × (Fin 10 → Column .advice) :=
  let prog : Configure Fp (Ironwood.Poseidon.Config × (Fin 10 → Column .advice)) := do
    let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
    let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
    let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
    let a9 ← adviceColumn
    enableEquality a0.toAny; enableEquality a1.toAny; enableEquality a2.toAny
    enableEquality a3.toAny; enableEquality a4.toAny; enableEquality a5.toAny
    enableEquality a6.toAny; enableEquality a7.toAny; enableEquality a8.toAny
    enableEquality a9.toAny
    let f0 ← fixedColumn; let _f1 ← fixedColumn; let f2 ← fixedColumn
    let f3 ← fixedColumn; let f4 ← fixedColumn; let f5 ← fixedColumn
    let f6 ← fixedColumn; let f7 ← fixedColumn
    enableConstant f0
    let cfg ← Ironwood.Poseidon.configure ![a6, a7, a8] a5 ![f2, f3, f4] ![f5, f6, f7]
    return (cfg, ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9])
  (prog {}).1

def pCfg : Ironwood.Poseidon.Config := setup.1
def pAdvices : Fin 10 → Column .advice := setup.2

/-- A dummy witness (keygen never reads advice values — `Value::unknown()`). -/
def pUnknown : WitgenIR Fp 1 := .native fun _ => #v[(0 : Fp)]

/-- The Lean mirror of `PoseidonDumpCircuit::synthesize`, on the proven `hash` bundle. -/
def layoutProgram : Circuit Fp Unit := do
  let ws ← assignRegion "witness inputs" (do
    let w0 ← assignAdvice (pAdvices 0) 0 pUnknown
    let w1 ← assignAdvice (pAdvices 1) 0 pUnknown
    pure (w0, w1))
  let _ ← (Ironwood.Poseidon.hash (capacity 2)).call pCfg { x0 := ws.1, x1 := ws.2 }
  pure ()

/-- The reconstructed layout products. -/
def pOps : Operations Fp := layoutProgram.operations
def pStarts : List ℕ := regionStarts pOps poseidonLayout
def pRegions : List (ℕ × RegionOperations Fp) := (indexedRegions pOps 0).1
def pPermCols : List ColRef := poseidonLayout.permColumns

def pCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  copyList pPermCols pStarts pRegions poseidonLayout.constants
def pSigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly poseidonLayout.n pPermCols.length pCopyList)
/-- Usable rows `n − (blindingFactors + 1)` (blinding = 5, dump META). -/
def pUsable : ℕ := 2042
def pFixed : List (ℕ × ℕ × ℕ) :=
  allFixed (ZMod.val : Fp → ℕ) pUsable poseidonSelMap pOps pStarts pRegions
    poseidonLayout.constants

/-! ## Machinery validation -/

-- Region lockstep: the fixture's region names, in order, are this side's
-- assignRegion sequence.
#guard poseidonLayout.regions.map (·.name)
  = ["witness inputs", "initial state for domain ConstantLength<2>",
     "add input for domain ConstantLength<2>", "permute state"]

-- keygen `Assembly` σ replay from the fixture's OWN ordered copy list.
#guard sigmaEntries (runAssembly poseidonLayout.n pPermCols.length poseidonLayout.copyList)
  = poseidonLayout.sigma

/-! ## End-to-end reconstruction vs the ported Poseidon stack -/

#guard pStarts = poseidonLayout.regions.map (·.start)

-- the ordered copy list (order-sensitive — σ's cycle rotations depend on it)
#guard pCopyList = poseidonLayout.copyList

-- the keygen permutation σ
#guard pSigma = poseidonLayout.sigma

-- the full fixed contents: round constants, deferred init constants, packed selectors
#guard pFixed = sortFixed poseidonLayout.fixed

end Halo2.Ironwood.Fixtures.Test.LayoutPoseidon
