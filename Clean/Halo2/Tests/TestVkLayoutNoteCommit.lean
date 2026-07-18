import Clean.Halo2.Fixtures.Layout
import Clean.Halo2.Fixtures.NoteCommitLayout
import Clean.Halo2.Fixtures.NoteCommitSelMap
import Clean.Halo2.Fixtures.NoteCommitParams
import Clean.Halo2.Tests.TestVkMatchSinsemilla
import Clean.Ironwood.NoteCommit.MainBundle
import Clean.Ironwood.Ecc.WitnessPoint
import Clean.Ironwood.Ecc.Mul
import Clean.Ironwood.Ecc.MulFixed.Short
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem

/-!
# VK-match test (layout): the NoteCommit chain — σ + fixed values

Mirror of the orchard-checkout `NoteCommitDumpCircuit` (`orchard/src/circuit/layout_dump.rs`
— the `note_commit::tests` harness circuit, keygen view, truncated after
`gadgets::note_commit`; see the fixture headers for the regeneration command). The Lean
side rebuilds the same configure chain (10 advices, constants, 3 lookup-table columns,
8 Lagrange fixed, range check, Sinsemilla, the 11 NoteCommit gates, then the full
`EccChip::configure` registration sequence) and the same synthesize sequence:

- load the generator table,
- witness `g_d`/`pk_d` (non-identity points), free-witness `value`/`rho`/`psi`,
- the 43 NoteCommit regions in `Main.synth` order — `Ironwood.NoteCommit.Main.synthPieces`, the two
  y-canonicity flows, the commit block (mirrored data-level: raw
  `FullWidth.synthesize` on the dumped `NoteCommitR` params, the proven hash bundle,
  the complete addition), the four canonicity witness checks, `Ironwood.NoteCommit.Main.synthGates`.

The commit block is mirrored at the data level because `Main.synth` is parameterized by
a proof-carrying `FixedBase` (the layout test only has the dumped `NoteCommitR` window
table); the region stream is identical (`indexedRegions` recurses through subcircuit
wrappers, and the bundled blind's synthesize is definitionally
`FullWidth.synthesize R.toData`).

## The generator table / `Q`

The dumped table columns are the `SINSEMILLA_S` contents (fixed cols 1/2/3); `Q` is the
orchard NoteCommit domain point — `x` from the constants allocation (row 13), `y` from
the `fixed_y_q` load (Lagrange col 4, hash row 204).
-/

namespace Halo2.Fixtures.Test.LayoutNoteCommit

open Ironwood (Fp)
open Orchard.Specs.Sinsemilla (Generators)
open Halo2.Fixtures.Layout
open Halo2.Fixtures.Test (sinsemillaS0 sinsemillaS0_onCurve)
open Halo2.Ironwood.NoteCommit.Main (ns ns_ne_nil brWit zCell)

/-- The generator-table x/y columns read back from the dump (fixed cols 2/3, table rows). -/
def ncTblCol (c : ℕ) : Array ℕ := Id.run do
  let mut arr : Array ℕ := Array.replicate 1024 0
  for (c', r, v) in noteCommitLayout.fixed do
    if c' = c ∧ r < 1024 then arr := arr.set! r v
  return arr

def ncTblX : Array ℕ := ncTblCol 2
def ncTblY : Array ℕ := ncTblCol 3

/-- The dump-derived generator family (on-curve fallback `S(0)`, never taken on the real
data — the guards would catch it as a value mismatch). -/
def ncG : Generators where
  S m :=
    let p : Orchard.Point Fp := { x := (ncTblX[m]! : Fp), y := (ncTblY[m]! : Fp) }
    if p.y ^ 2 = p.x ^ 3 + Orchard.pallasB then p else sinsemillaS0
  S_onCurve {m} _ := by
    show Orchard.Point.OnCurve _
    dsimp only
    split
    · next h => exact h
    · exact sinsemillaS0_onCurve

/-- The orchard NoteCommit domain point `Q` (constants row 13 / the `fixed_y_q` value). -/
def ncQ : Orchard.Point Fp :=
  { x := (10629404576683096409262958701336170057000067777256141967953463442979689100381 : Fp),
    y := (22898949290933268079297281211505753011910178734473470279111609228438645877859 : Fp) }

theorem ncQ_onCurve : ncQ.OnCurve := by
  show ncQ.y ^ 2 = ncQ.x ^ 3 + Orchard.pallasB
  decide

/-- The full configure chain of `NoteCommitDumpCircuit` (= the orchard `note_commit`
test circuit): 10 advices, constants + `enable_constant`, equality on all advices, the
3 lookup-table columns, 8 Lagrange fixed, range check, Sinsemilla (`fixed_y_q` =
Lagrange col 0, `witness_pieces` = advice 2), the 11 NoteCommit gates, then
`EccChip::configure` (witness point, incomplete/complete addition, variable-base mul,
fixed-base mul + full-width/short/base-field entry points). -/
def ncSetup : Ironwood.NoteCommit.Main.Config × Ironwood.Ecc.WitnessPoint.Config × (Fin 10 → Column .advice) :=
  let prog : Configure Fp
      (Ironwood.NoteCommit.Main.Config × Ironwood.Ecc.WitnessPoint.Config × (Fin 10 → Column .advice)) := do
    let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
    let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
    let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
    let a9 ← adviceColumn
    let constants ← fixedColumn
    enableConstant constants
    enableEquality a0; enableEquality a1; enableEquality a2; enableEquality a3
    enableEquality a4; enableEquality a5; enableEquality a6; enableEquality a7
    enableEquality a8; enableEquality a9
    let t0 ← lookupTableColumn
    let t1 ← lookupTableColumn
    let t2 ← lookupTableColumn
    let l0 ← fixedColumn; let l1 ← fixedColumn; let l2 ← fixedColumn
    let l3 ← fixedColumn; let l4 ← fixedColumn; let l5 ← fixedColumn
    let l6 ← fixedColumn; let l7 ← fixedColumn
    let advices : Fin 10 → Column .advice := ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    let lookupConfig ← Ironwood.LookupRangeCheck.configure 10 a9 t0
    let hashConfig ← Ironwood.Sinsemilla.HashPiece.configure ncG
      a0 a1 a2 a3 a4 a2 l0 { tableIdx := t0, tableX := t1, tableY := t2 }
    let gates ← Ironwood.NoteCommit.configure advices
    -- EccChip::configure (ecc/chip.rs:308-360)
    let wpCfg ← Ironwood.Ecc.WitnessPoint.configure a0 a1
    let addIncompleteConfig ← Ironwood.Ecc.AddIncomplete.add.configure (a0, a1, a2, a3)
    let addConfig ← Ironwood.Ecc.Add.add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)
    let _mulConfig ← Ironwood.Ecc.Mul.configure addConfig lookupConfig advices
    let mulFixedConfig ← Ironwood.Ecc.MulFixed.configure
      ![l0, l1, l2, l3, l4, l5, l6, l7] a4 a5 addConfig addIncompleteConfig
    let fwConfig ← Ironwood.Ecc.MulFixed.FullWidth.configure mulFixedConfig
    let _shortConfig ← Ironwood.Ecc.MulFixed.Short.configure mulFixedConfig
    let _bfConfig ← Ironwood.Ecc.MulFixed.BaseFieldElem.configure
      ![a6, a7, a8] lookupConfig mulFixedConfig
    return ({ gates, hashConfig, lookupConfig, mulConfig := fwConfig,
              addConfig }, wpCfg, advices)
  (prog {}).1

def ncCfg : Ironwood.NoteCommit.Main.Config := ncSetup.1
def ncWpCfg : Ironwood.Ecc.WitnessPoint.Config := ncSetup.2.1
def ncAdvices : Fin 10 → Column .advice := ncSetup.2.2

/-- A dummy witness (keygen never evaluates witness programs — `Value::unknown()`). -/
def ncUnknown : WitgenIR Fp 1 := .native fun _ => #v[(0 : Fp)]

def ncPointUnknown : Orchard.Point (FExpr Fp) := { x := .const 0, y := .const 0 }

/-- The Lean mirror of `NoteCommitDumpCircuit::synthesize`. -/
def ncProgram : Circuit Fp Unit := do
  -- SinsemillaChip::load (one Rust assign_table; three single-column loadTables here)
  Ironwood.Sinsemilla.load ncG ncCfg.hashConfig.generatorTable
  -- witness g_d / pk_d (non-identity points), then value/rho/psi as free advice cells
  let gd ← ((Ironwood.Ecc.WitnessPoint.pointNonId).toFormal
    "witness non-identity point").call ncWpCfg ncPointUnknown
  let pkd ← ((Ironwood.Ecc.WitnessPoint.pointNonId).toFormal
    "witness non-identity point").call ncWpCfg ncPointUnknown
  let value ← assignRegion "load private" (assignAdvice (ncAdvices 0) 0 ncUnknown)
  let rho ← assignRegion "load private" (assignAdvice (ncAdvices 0) 0 ncUnknown)
  let psi ← assignRegion "load private" (assignAdvice (ncAdvices 0) 0 ncUnknown)
  let input : Ironwood.NoteCommit.Main.Inputs (AssignedCell Fp) :=
    { gdX := gd.x, gdY := gd.y, pkdX := pkd.x, pkdY := pkd.y, value, rho, psi }
  -- the 43 NoteCommit regions, in `Main.synth` order
  let i₀ ← Ironwood.NoteCommit.Main.currentRegion
  let iHash := i₀ + 27
  let pcs ← Ironwood.NoteCommit.Main.synthPieces ncCfg input
  let b2 ← (Ironwood.NoteCommit.YCanonicityCheck.circuit
    (brWit input.gdY 0 1)).call (ncCfg.gates.y, ncCfg.lookupConfig) { y := input.gdY }
  let d1 ← (Ironwood.NoteCommit.YCanonicityCheck.circuit
    (brWit input.pkdY 0 1)).call (ncCfg.gates.y, ncCfg.lookupConfig) { y := input.pkdY }
  -- CommitDomain::commit, mirrored data-level (blind, hash, M + [r]R)
  let blindOut ← Ironwood.Ecc.MulFixed.FullWidth.synthesize noteCommitRData
    ncCfg.mulConfig (Vector.replicate 85 (.const (0 : Fp)))
  let hashOut ← (Ironwood.Sinsemilla.HashToPoint.hashCircuit ncG ns ncQ ncQ_onCurve
    ns_ne_nil).call ncCfg.hashConfig
    { pieces := #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h] }
  let cm ← (Ironwood.Ecc.Add.add.toFormal "complete point addition").call ncCfg.addConfig
    { p := hashOut.point, q := blindOut }
  -- the four canonicity witness checks
  let aZs ← Ironwood.LookupRangeCheck.witnessCheck 10 13 false ncCfg.lookupConfig
    (Ironwood.NoteCommit.GdCanonicityCheck.aPrimeWit pcs.a)
  let bZs ← Ironwood.LookupRangeCheck.witnessCheck 10 14 false ncCfg.lookupConfig
    (Ironwood.NoteCommit.PkdCanonicityCheck.b3CPrimeWit pcs.b3 pcs.c)
  let eZs ← Ironwood.LookupRangeCheck.witnessCheck 10 14 false ncCfg.lookupConfig
    (Ironwood.NoteCommit.RhoCanonicityCheck.e1FPrimeWit pcs.e1 pcs.f)
  let gZs ← Ironwood.LookupRangeCheck.witnessCheck 10 13 false ncCfg.lookupConfig
    (Ironwood.NoteCommit.PsiCanonicityCheck.g1G2PrimeWit pcs.g1 (zCell ncCfg.hashConfig iHash 6 1))
  Ironwood.NoteCommit.Main.synthGates ncCfg input pcs { b2, d1, cm, aZs, bZs, eZs, gZs } iHash
  pure ()

/-! ## The reconstructed layout products -/

def ncOps : Operations Fp := ncProgram.operations
def ncRegions : List (ℕ × RegionOperations Fp) := (indexedRegions ncOps 0).1

/-- Region starts from the fixture placements, in `assignRegion` order (the single
`generator_table` slot is the three `loadTable`s' — filtered). -/
def ncStarts : List ℕ :=
  ((noteCommitLayout.regions.filter (·.name ≠ "generator_table")).map (·.start))

def ncPermCols : List ColRef := noteCommitLayout.permColumns

def ncCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  copyList ncPermCols ncStarts ncRegions noteCommitLayout.constants
def ncSigma : List (ℕ × ℕ × ℕ × ℕ) :=
  sigmaEntries (runAssembly noteCommitLayout.n ncPermCols.length ncCopyList)
/-- Usable rows `n − (blindingFactors + 1)` (blinding = 5, dump META). -/
def ncUsable : ℕ := 2042
def ncFixed : List (ℕ × ℕ × ℕ) :=
  sortFixed (dedupFixed
    (tableFixed (ZMod.val : Fp → ℕ) ncUsable ncOps
      ++ constantsFixed noteCommitLayout.constants
      ++ selectorFixed noteCommitSelMap (activations ncStarts ncRegions)
      ++ assignedFixed (ZMod.val : Fp → ℕ) ncStarts ncRegions))

/-! ## Machinery validation -/

-- keygen `Assembly` σ replay from the fixture's OWN ordered copy list.
#guard sigmaEntries (runAssembly noteCommitLayout.n ncPermCols.length
  noteCommitLayout.copyList) = noteCommitLayout.sigma

-- Region lockstep: the fixture's non-table region names, in order, are this side's
-- assignRegion sequence.
#guard (noteCommitLayout.regions.filter (·.name ≠ "generator_table")).map (·.name)
  = (regionSlots ncOps).filterMap fun (isRegion, nm) => if isRegion then some nm else none

/-! ## End-to-end reconstruction vs the ported NoteCommit stack -/

-- the ordered copy list (order-sensitive — σ's cycle rotations depend on it)
#guard ncCopyList = noteCommitLayout.copyList

-- the keygen permutation σ
#guard ncSigma = noteCommitLayout.sigma

-- the full fixed contents: generator table, constants, packed selectors, q_s2 /
-- fixed_y_q, the NoteCommitR window table
#guard ncFixed = sortFixed noteCommitLayout.fixed

end Halo2.Fixtures.Test.LayoutNoteCommit
