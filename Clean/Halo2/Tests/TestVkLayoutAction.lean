import Clean.Halo2.Fixtures.ActionLayout
import Clean.Halo2.Fixtures.ActionSelMap
import Clean.Halo2.Fixtures.ActionParams
import Clean.Halo2.Fixtures.NoteCommitParams
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

/-- The dump-derived generator family (on-curve fallback `S(0)`, never taken on the
real data — the guards would catch it as a value mismatch). -/
def aG : Generators where
  S m :=
    let p : Orchard.Point Fp := { x := (aTblX[m]! : Fp), y := (aTblY[m]! : Fp) }
    if p.y ^ 2 = p.x ^ 3 + Orchard.pallasB then p else sinsemillaS0
  S_onCurve {m} _ := by
    show Orchard.Point.OnCurve _
    dsimp only
    split
    · next h => exact h
    · exact sinsemillaS0_onCurve

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

open Halo2.Ironwood in
/-- `CommitDomain::commit` at message length `k`, data-level blind. -/
def commitMirror (ns : List ℕ) (hns : ns ≠ []) (Q : Orchard.Point Fp) (hQ : Q.OnCurve)
    (RData : Ironwood.Ecc.MulFixed.FixedBaseData)
    (mulCfg : Ironwood.Ecc.MulFixed.FullWidth.Config)
    (hashCfg : Ironwood.Sinsemilla.HashPiece.Config)
    (addCfg : Ironwood.Ecc.Add.Config)
    (pieces : Vector (AssignedCell Fp) ns.length) :
    Circuit Fp (Var Orchard.Point Fp) := do
  let blindOut ← Ironwood.Ecc.MulFixed.FullWidth.synthesize RData mulCfg unkWindows
  let hashOut ← (Ironwood.Sinsemilla.HashToPoint.hashCircuit aG ns Q hQ hns).call
    hashCfg { pieces := pieces }
  (Ironwood.Ecc.Add.add.toFormal "complete point addition").call addCfg
    { p := hashOut.point, q := blindOut }

open Halo2.Ironwood in
/-- The mirror of the base stages (keygen witnesses, data-level bases), returning the
cells the ironwood cross-address stage reads. -/
def aProgramCore : Circuit Fp
    (Ironwood.Action.Circuit.WitnessCells × Ironwood.Action.Circuit.CheckCells ×
      Ironwood.Action.Circuit.NoteCells) := do
  Ironwood.Sinsemilla.load aG aCfg.sinsemilla1.generatorTable
  -- the eight shared witness regions
  let psiOld ← loadPrivate (aCfg.advices 0) unk
  let rhoOld ← loadPrivate (aCfg.advices 0) unk
  let cmOld ← (Ironwood.Ecc.WitnessPoint.point.toFormal "witness point").call
    aCfg.eccConfig.witnessPoint unkPoint
  let gdOld ← (Ironwood.Ecc.WitnessPoint.pointNonId.toFormal
    "witness non-identity point").call aCfg.eccConfig.witnessPoint unkPoint
  let akP ← (Ironwood.Ecc.WitnessPoint.pointNonId.toFormal
    "witness non-identity point").call aCfg.eccConfig.witnessPoint unkPoint
  let nk ← loadPrivate (aCfg.advices 0) unk
  let vOld ← loadPrivate (aCfg.advices 0) unk
  let vNew ← loadPrivate (aCfg.advices 0) unk
  -- the Merkle path, 16 layers per Sinsemilla instance
  let half ← FormalCircuit.foldCall
    (Ironwood.Sinsemilla.Merkle.CalculateRoot.layerAt aG merkleQ merkleQ_onCurve 0
      (fun _ => unk) (fun _ _ => false))
    Ironwood.Sinsemilla.Merkle.CalculateRoot.toInput
    (aCfg.merkle1.condSwap, aCfg.merkle1, aCfg.lookupConfig) { node := cmOld.x } 16
  let rootAcc ← FormalCircuit.foldCall
    (Ironwood.Sinsemilla.Merkle.CalculateRoot.layerAt aG merkleQ merkleQ_onCurve 16
      (fun _ => unk) (fun _ _ => false))
    Ironwood.Sinsemilla.Merkle.CalculateRoot.toInput
    (aCfg.merkle2.condSwap, aCfg.merkle2, aCfg.lookupConfig) half 16
  let root := rootAcc.node
  -- value-commit integrity (Short + FullWidth data-level, complete addition)
  let magnitude ← loadPrivate (aCfg.advices 9) unk
  let sign ← loadPrivate (aCfg.advices 9) unk
  let commitment ← Ironwood.Ecc.MulFixed.Short.synthesize valueCommitVData
    aCfg.eccConfig.mulFixedShort { magnitude := magnitude, sign := sign }
  let blind ← Ironwood.Ecc.MulFixed.FullWidth.synthesize valueCommitRData
    aCfg.eccConfig.mulFixedFull unkWindows
  let cvNet ← (Ironwood.Ecc.Add.add.toFormal "complete point addition").call
    aCfg.eccConfig.add { p := commitment, q := blind }
  constrainInstance cvNet.x aCfg.primary CV_NET_X
  constrainInstance cvNet.y aCfg.primary CV_NET_Y
  -- nullifier integrity (Poseidon + add chip + BaseFieldElem data-level + addition)
  let hash ← (Ironwood.Poseidon.hash
    (Orchard.Poseidon.Hash.ConstantLength.capacity 2)).call aCfg.poseidonConfig
    { x0 := nk, x1 := rhoOld }
  let scalar ← (Ironwood.AddChip.add.toFormal "c = a + b").call aCfg.addChipConfig
    { a := hash, b := psiOld }
  let product ← Ironwood.Ecc.MulFixed.BaseFieldElem.synthesize nullifierKData
    aCfg.eccConfig.mulFixedBaseField scalar
  let nfOldP ← (Ironwood.Ecc.Add.add.toFormal "complete point addition").call
    aCfg.eccConfig.add { p := cmOld, q := product }
  let nfOld := nfOldP.x
  constrainInstance nfOld aCfg.primary NF_OLD
  -- spend authority (FullWidth data-level + addition)
  let alphaCommitment ← Ironwood.Ecc.MulFixed.FullWidth.synthesize spendAuthGData
    aCfg.eccConfig.mulFixedFull unkWindows
  let rk ← (Ironwood.Ecc.Add.add.toFormal "complete point addition").call
    aCfg.eccConfig.add { p := alphaCommitment, q := akP }
  constrainInstance rk.x aCfg.primary RK_X
  constrainInstance rk.y aCfg.primary RK_Y
  -- diversified address integrity: CommitIvk (pieces, data-level commit, canonicity)
  let ivkInput : Ironwood.CommitIvk.Main.Inputs (AssignedCell Fp) :=
    { ak := akP.x, nk := nk }
  let iIvk ← Ironwood.NoteCommit.Main.currentRegion
  let ivkPcs ← Ironwood.CommitIvk.Main.synthPieces
    { gate := aCfg.commitIvkConfig, hashConfig := aCfg.sinsemilla1,
      lookupConfig := aCfg.lookupConfig, mulConfig := aCfg.eccConfig.mulFixedFull,
      addConfig := aCfg.eccConfig.add } ivkInput
  let ivkCm ← commitMirror Ironwood.CommitIvk.Main.ns Ironwood.CommitIvk.Main.ns_ne_nil
    ivkQ ivkQ_onCurve commitIvkRData aCfg.eccConfig.mulFixedFull aCfg.sinsemilla1
    aCfg.eccConfig.add #v[ivkPcs.a, ivkPcs.b, ivkPcs.c, ivkPcs.d]
  let _ ← (Ironwood.CommitIvk.Canonicity.circuit
      (Ironwood.NoteCommit.Main.brWit ivkInput.ak 254 1)
      (Ironwood.NoteCommit.Main.brWit ivkInput.nk 254 1)).call
    (aCfg.commitIvkConfig, aCfg.lookupConfig)
    { ak := ivkInput.ak, a := ivkPcs.a, bWhole := ivkPcs.b, b0 := ivkPcs.b0,
      b2 := ivkPcs.b2,
      z13A := Ironwood.CommitIvk.Main.zCell aCfg.sinsemilla1 (iIvk + 9) 0 13,
      nk := ivkInput.nk, c := ivkPcs.c, dWhole := ivkPcs.d, d0 := ivkPcs.d0,
      z13C := Ironwood.CommitIvk.Main.zCell aCfg.sinsemilla1 (iIvk + 9) 2 13 }
  let ivk := ivkCm.x
  -- [ivk] g_d_old + witness pk_d_old + constrain equal (variable-base mul, no base)
  let pkDOld ← (Ironwood.Action.AddressIntegrity.circuit unkPoint).call
    (aCfg.eccConfig.mul, aCfg.eccConfig.witnessPoint) { ivk := ivk, gDOld := gdOld }
  -- old note commitment (pieces / y-canonicity / data-level commit / checks / gates)
  noteCommitMirror aCfg.noteCommitOld aCfg.sinsemilla1 noteCommitRData
    { gdX := gdOld.x, gdY := gdOld.y, pkdX := pkDOld.x, pkdY := pkDOld.y,
      value := vOld, rho := rhoOld, psi := psiOld } >>= fun derivedCmOld => do
  assignRegion "constrain equal" (do
    constrainEqual derivedCmOld.x cmOld.x
    constrainEqual derivedCmOld.y cmOld.y)
  -- new note commitment
  let gdNew ← (Ironwood.Ecc.WitnessPoint.pointNonId.toFormal
    "witness non-identity point").call aCfg.eccConfig.witnessPoint unkPoint
  let pkdNew ← (Ironwood.Ecc.WitnessPoint.pointNonId.toFormal
    "witness non-identity point").call aCfg.eccConfig.witnessPoint unkPoint
  let psiNew ← loadPrivate (aCfg.advices 0) unk
  let cmNew ← noteCommitMirror aCfg.noteCommitNew aCfg.sinsemilla2 noteCommitRData
    { gdX := gdNew.x, gdY := gdNew.y, pkdX := pkdNew.x, pkdY := pkdNew.y,
      value := vNew, rho := nfOld, psi := psiNew }
  constrainInstance cmNew.x aCfg.primary CMX
  -- the final checks region
  assignRegion "Orchard circuit checks" (do
    let _ ← copyAdvice vOld (aCfg.advices 0) 0
    let _ ← copyAdvice vNew (aCfg.advices 1) 0
    let _ ← copyAdvice magnitude (aCfg.advices 2) 0
    let _ ← copyAdvice sign (aCfg.advices 3) 0
    let _ ← copyAdvice root (aCfg.advices 4) 0
    let _ ← assignAdviceFromInstance aCfg.primary ANCHOR (aCfg.advices 5) 0
    let _ ← assignAdviceFromInstance aCfg.primary ENABLE_SPEND (aCfg.advices 6) 0
    let _ ← assignAdviceFromInstance aCfg.primary ENABLE_OUTPUT (aCfg.advices 7) 0
    (orchardGate aCfg.qOrchard aCfg.advices).enable 0)
  pure ({ psiOld, rhoOld, cmOld, gdOld, akP, nk, vOld, vNew },
    { root, magnitude, sign, nfOld, pkdOld := pkDOld },
    { gdNew, pkdNew })
where
  /-- One `NoteCommit` (the `TestVkLayoutNoteCommit` mirror body, at this circuit's
  configs; 43 regions). -/
  noteCommitMirror (gates : Halo2.Ironwood.NoteCommit.Config)
      (hashCfg : Halo2.Ironwood.Sinsemilla.HashPiece.Config)
      (RData : Halo2.Ironwood.Ecc.MulFixed.FixedBaseData)
      (input : Halo2.Ironwood.NoteCommit.Main.Inputs (AssignedCell Fp)) :
      Circuit Fp (Var Orchard.Point Fp) := do
    let ncfg : Halo2.Ironwood.NoteCommit.Main.Config :=
      { gates, hashConfig := hashCfg, lookupConfig := aCfg.lookupConfig,
        mulConfig := aCfg.eccConfig.mulFixedFull, addConfig := aCfg.eccConfig.add }
    let i₀ ← Halo2.Ironwood.NoteCommit.Main.currentRegion
    let iHash := i₀ + 27
    let pcs ← Halo2.Ironwood.NoteCommit.Main.synthPieces ncfg input
    let b2 ← (Halo2.Ironwood.NoteCommit.YCanonicityCheck.circuit
      (Halo2.Ironwood.NoteCommit.Main.brWit input.gdY 0 1)).call
      (ncfg.gates.y, ncfg.lookupConfig) { y := input.gdY }
    let d1 ← (Halo2.Ironwood.NoteCommit.YCanonicityCheck.circuit
      (Halo2.Ironwood.NoteCommit.Main.brWit input.pkdY 0 1)).call
      (ncfg.gates.y, ncfg.lookupConfig) { y := input.pkdY }
    let cm ← commitMirror Halo2.Ironwood.NoteCommit.Main.ns
      Halo2.Ironwood.NoteCommit.Main.ns_ne_nil noteQ noteQ_onCurve RData
      ncfg.mulConfig ncfg.hashConfig ncfg.addConfig
      #v[pcs.a, pcs.b, pcs.c, pcs.d, pcs.e, pcs.f, pcs.g, pcs.h]
    let aZs ← Halo2.Ironwood.LookupRangeCheck.witnessCheck 10 13 false ncfg.lookupConfig
      (Halo2.Ironwood.NoteCommit.GdCanonicityCheck.aPrimeWit pcs.a)
    let bZs ← Halo2.Ironwood.LookupRangeCheck.witnessCheck 10 14 false ncfg.lookupConfig
      (Halo2.Ironwood.NoteCommit.PkdCanonicityCheck.b3CPrimeWit pcs.b3 pcs.c)
    let eZs ← Halo2.Ironwood.LookupRangeCheck.witnessCheck 10 14 false ncfg.lookupConfig
      (Halo2.Ironwood.NoteCommit.RhoCanonicityCheck.e1FPrimeWit pcs.e1 pcs.f)
    let gZs ← Halo2.Ironwood.LookupRangeCheck.witnessCheck 10 13 false ncfg.lookupConfig
      (Halo2.Ironwood.NoteCommit.PsiCanonicityCheck.g1G2PrimeWit pcs.g1
        (Halo2.Ironwood.NoteCommit.Main.zCell ncfg.hashConfig iHash 6 1))
    Halo2.Ironwood.NoteCommit.Main.synthGates ncfg input pcs
      { b2, d1, cm, aZs, bZs, eZs, gZs } iHash
    pure cm

/-- The pre-ironwood (fixed post-NU 6.2) mirror. -/
def aProgramBase : Circuit Fp Unit := do
  let _ ← aProgramCore
  pure ()

/-- The ironwood (post-NU 6.3) mirror — the base stages plus the REAL
`synthCrossAddressChecks` (shared with the main circuit, no mirror copy). -/
def aProgram : Circuit Fp Unit := do
  let (wc, cc, nc) ← aProgramCore
  Halo2.Ironwood.Action.Circuit.synthCrossAddressChecks aCfg wc cc nc

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
