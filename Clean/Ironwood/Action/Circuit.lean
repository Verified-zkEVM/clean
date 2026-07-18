import Clean.Ironwood.Ecc.Chip
import Clean.Ironwood.Poseidon.Hash
import Clean.Ironwood.Utilities.AddChip
import Clean.Ironwood.Sinsemilla.Merkle
import Clean.Ironwood.CommitIvk.MainBundle
import Clean.Ironwood.NoteCommit.MainBundle
import Clean.Ironwood.Action.DeriveNullifier
import Clean.Ironwood.Action.ValueCommit
import Clean.Ironwood.Action.SpendAuthority
import Clean.Ironwood.Action.AddressIntegrity

/-!
# The Orchard Action circuit (Ironwood): configure

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit.rs`, `impl plonk::Circuit for Circuit` —
`fn configure` (lines 271-459), VK-exact in registration order:
the ten advices, the `q_orchard` gate, the add chip, the three lookup table columns,
the `primary` instance column, equality on all advices, the eight Lagrange fixed
columns (+ constants on the first), the range check, the ECC chip, Poseidon, the two
Sinsemilla/Merkle pairs, CommitIvk, and the two NoteCommit chips.

`fn synthesize` (lines 461-828), in exact region-creation order: the generator-table
load, the eight shared witness regions, the 32-layer Merkle path (16 layers per
Sinsemilla instance), value-commit integrity, nullifier integrity, spend authority,
diversified-address integrity (CommitIvk + [ivk] g_d_old), old/new note-commitment
integrity, and the final `"Orchard circuit checks"` region (copies, the three
`assign_advice_from_instance` public inputs, `q_orchard`).
-/

namespace Halo2.Ironwood.Action.Circuit

open Halo2.Ironwood (Fp)
open Orchard.Specs.Sinsemilla (Generators)

/-- Rust `Config` (`circuit.rs:120-137`): everything `synthesize` consumes. The shared
lookup config (`range_check`) is carried explicitly (Rust reaches it through the chips). -/
structure Config where
  primary : Column .instance
  qOrchard : Selector
  advices : Fin 10 → Column .advice
  addChipConfig : AddChip.Config
  eccConfig : Ecc.EccConfig
  poseidonConfig : Poseidon.Config
  sinsemilla1 : Sinsemilla.HashPiece.Config
  merkle1 : Sinsemilla.Merkle.Config
  sinsemilla2 : Sinsemilla.HashPiece.Config
  merkle2 : Sinsemilla.Merkle.Config
  commitIvkConfig : CommitIvk.Config
  noteCommitOld : NoteCommit.Config
  noteCommitNew : NoteCommit.Config
  lookupConfig : LookupRangeCheck.Config 10

/-- The `"Orchard circuit checks"` gate (`circuit.rs:290-329`): the four top-level value
checks over `advices[0..8]` at the current row, in the source's constraint order. -/
def orchardGate (qOrchard : Selector) (advices : Fin 10 → Column .advice) : Gate Fp where
  name := "Orchard circuit checks"
  selector := qOrchard
  constraints :=
    let vOld : Expression Fp Query := queryAdvice (advices 0) 0
    let vNew : Expression Fp Query := queryAdvice (advices 1) 0
    let magnitude : Expression Fp Query := queryAdvice (advices 2) 0
    let sign : Expression Fp Query := queryAdvice (advices 3) 0
    let root : Expression Fp Query := queryAdvice (advices 4) 0
    let anchor : Expression Fp Query := queryAdvice (advices 5) 0
    let enableSpends : Expression Fp Query := queryAdvice (advices 6) 0
    let enableOutputs : Expression Fp Query := queryAdvice (advices 7) 0
    Constraints.withSelector qOrchard
      [ ("v_old - v_new = magnitude * sign", vOld - vNew - magnitude * sign),
        ("Either v_old = 0, or root = anchor", vOld * (root - anchor)),
        ("v_old = 0 or enable_spends = 1", vOld * ((1 : Fp) - enableSpends)),
        ("v_new = 0 or enable_outputs = 1", vNew * ((1 : Fp) - enableOutputs)) ]

/-- Rust `Circuit::configure` (`circuit.rs:271-459`), VK-exact registration order. -/
def configure (G : Generators) : Configure Fp Config := do
  -- circuit.rs:273-284 — the ten advice columns
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
  let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
  let a9 ← adviceColumn
  let advices : Fin 10 → Column .advice := ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  -- circuit.rs:290-329 — `q_orchard` + the top-level checks gate
  let qOrchard ← selector
  createGate (orchardGate qOrchard advices)
  -- circuit.rs:332 — the add chip (advices 7, 8 → 6)
  let addChipConfig ← AddChip.configure a7 a8 a6
  -- circuit.rs:335-340 — the Sinsemilla generator table columns
  let tableIdx ← lookupTableColumn
  let tableX ← lookupTableColumn
  let tableY ← lookupTableColumn
  let genTable : Sinsemilla.GeneratorTableConfig := { tableIdx, tableX, tableY }
  -- circuit.rs:343-344 — the public-input instance column
  let primary ← instanceColumn
  enableEquality primary
  -- circuit.rs:347-349 — equality on all advices
  enableEquality a0; enableEquality a1; enableEquality a2; enableEquality a3
  enableEquality a4; enableEquality a5; enableEquality a6; enableEquality a7
  enableEquality a8; enableEquality a9
  -- circuit.rs:356-365 — the eight Lagrange-coefficient fixed columns
  let l0 ← fixedColumn; let l1 ← fixedColumn; let l2 ← fixedColumn
  let l3 ← fixedColumn; let l4 ← fixedColumn; let l5 ← fixedColumn
  let l6 ← fixedColumn; let l7 ← fixedColumn
  let lagrangeCoeffs : Fin 8 → Column .fixed := ![l0, l1, l2, l3, l4, l5, l6, l7]
  -- circuit.rs:371 — constants on the first Lagrange column
  enableConstant l0
  -- circuit.rs:375 — the shared 10-bit range check on `advices[9]`
  let lookupConfig ← LookupRangeCheck.configure 10 a9 tableIdx
  -- circuit.rs:379-380 — the ECC chip
  let eccConfig ← Ecc.configure advices lagrangeCoeffs lookupConfig
  -- circuit.rs:383-391 — Poseidon (state `advices[6..9]`, sbox `advices[5]`,
  -- `rc_a = lagrange[2..5]`, `rc_b = lagrange[5..8]`)
  let poseidonConfig ← Poseidon.configure ![a6, a7, a8] a5 ![l2, l3, l4] ![l5, l6, l7]
  -- circuit.rs:397-410 — Sinsemilla 1 (advices[0..5], pieces `advices[6]`,
  -- `y_Q` fixed `lagrange[0]`) + Merkle 1
  let sinsemilla1 ← Sinsemilla.HashPiece.configure G a0 a1 a2 a3 a4 a6 l0 genTable
  let merkle1 ← Sinsemilla.Merkle.configure sinsemilla1
  -- circuit.rs:416-429 — Sinsemilla 2 (advices[5..], pieces `advices[7]`,
  -- `y_Q` fixed `lagrange[1]`) + Merkle 2
  let sinsemilla2 ← Sinsemilla.HashPiece.configure G a5 a6 a7 a8 a9 a7 l1 genTable
  let merkle2 ← Sinsemilla.Merkle.configure sinsemilla2
  -- circuit.rs:433 — CommitIvk
  let commitIvkConfig ← CommitIvk.configure advices
  -- circuit.rs:437-443 — the two NoteCommit chips
  let noteCommitOld ← NoteCommit.configure advices
  let noteCommitNew ← NoteCommit.configure advices
  return { primary, qOrchard, advices, addChipConfig, eccConfig, poseidonConfig,
           sinsemilla1, merkle1, sinsemilla2, merkle2, commitIvkConfig,
           noteCommitOld, noteCommitNew, lookupConfig }

/-! ## Synthesize -/

open Orchard (Point)
open Orchard.Ecc.MulFixed (FixedBase)

/-- The public-input rows of the `primary` instance column (`circuit.rs:78-86`). -/
def ANCHOR : ℕ := 0
def CV_NET_X : ℕ := 1
def CV_NET_Y : ℕ := 2
def NF_OLD : ℕ := 3
def RK_X : ℕ := 4
def RK_Y : ℕ := 5
def CMX : ℕ := 6
def ENABLE_SPEND : ℕ := 7
def ENABLE_OUTPUT : ℕ := 8

/-- The fixed bases and Sinsemilla domain points the Action circuit is instantiated at
(Rust reaches them through `OrchardFixedBases` / the domain constants). -/
structure Bases where
  nullifierK : FixedBase
  valueCommitV : Orchard.Ecc.MulFixed.Short.FixedBase
  valueCommitR : FixedBase
  spendAuthG : FixedBase
  commitIvkR : FixedBase
  noteCommitR : FixedBase
  merkleQ : Point Fp
  merkleQ_onCurve : merkleQ.OnCurve
  ivkQ : Point Fp
  ivkQ_onCurve : ivkQ.OnCurve
  noteQ : Point Fp
  noteQ_onCurve : noteQ.OnCurve

/-- The private-input witness programs (the Rust `Circuit` struct fields; scalars enter
through the fixed-base muls' window programs, per the lazy-witnessing rule). -/
structure Witnesses where
  psiOld : WitgenIR Fp 1
  rhoOld : WitgenIR Fp 1
  nk : WitgenIR Fp 1
  vOld : WitgenIR Fp 1
  vNew : WitgenIR Fp 1
  psiNew : WitgenIR Fp 1
  magnitude : WitgenIR Fp 1
  sign : WitgenIR Fp 1
  cmOld : Point (FExpr Fp)
  gdOld : Point (FExpr Fp)
  akP : Point (FExpr Fp)
  pkDOld : Point (FExpr Fp)
  gdNew : Point (FExpr Fp)
  pkdNew : Point (FExpr Fp)
  rcvWindows : Vector (FExpr Fp) 85
  alphaWindows : Vector (FExpr Fp) 85
  rivkWindows : Vector (FExpr Fp) 85
  rcmOldWindows : Vector (FExpr Fp) 85
  rcmNewWindows : Vector (FExpr Fp) 85
  merkleSib : ℕ → WitgenIR Fp 1
  merkleSwap : ℕ → Placed ProverEnvironment Fp → Bool

/-- Rust `assign_free_advice` (`circuit.rs:101-113`): the `"load private"` region, one
advice cell at row 0. -/
def loadPrivate (col : Column .advice) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp) :=
  assignRegion "load private" (assignAdvice col 0 w)

/-- Rust `Circuit::synthesize` (`circuit.rs:461-828`), in exact region-creation order.
Structure-only for now (the bundle + proofs land once the commit-arc contracts settle);
every child is a proven bundle except the region-free glue. -/
def synthesize (G : Generators) (B : Bases) (W : Witnesses) (cfg : Config) :
    Circuit Fp Unit := do
  -- circuit.rs:467 — the Sinsemilla generator table, loaded once
  Sinsemilla.load G cfg.sinsemilla1.generatorTable
  -- circuit.rs:473-532 — the shared witness regions
  let psiOld ← loadPrivate (cfg.advices 0) W.psiOld
  let rhoOld ← loadPrivate (cfg.advices 0) W.rhoOld
  let cmOld ← (Ecc.WitnessPoint.point.toFormal "witness point").call
    cfg.eccConfig.witnessPoint W.cmOld
  let gdOld ← (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point").call
    cfg.eccConfig.witnessPoint W.gdOld
  let akP ← (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point").call
    cfg.eccConfig.witnessPoint W.akP
  let nk ← loadPrivate (cfg.advices 0) W.nk
  let vOld ← loadPrivate (cfg.advices 0) W.vOld
  let vNew ← loadPrivate (cfg.advices 0) W.vNew
  -- circuit.rs:535-548 — the Merkle path (leaf = cm_old.extract_p); 16 layers per
  -- Sinsemilla instance (`merkle.rs:122-126`, `chips[i / layers_per_chip]`)
  let half ← FormalCircuit.foldCall
    (Sinsemilla.Merkle.CalculateRoot.layerAt G B.merkleQ B.merkleQ_onCurve 0
      W.merkleSib W.merkleSwap)
    Sinsemilla.Merkle.CalculateRoot.toInput (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
    { node := cmOld.x } 16
  let rootAcc ← FormalCircuit.foldCall
    (Sinsemilla.Merkle.CalculateRoot.layerAt G B.merkleQ B.merkleQ_onCurve 16
      (fun i => W.merkleSib (i + 16)) (fun i => W.merkleSwap (i + 16)))
    Sinsemilla.Merkle.CalculateRoot.toInput (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig)
    half 16
  let root := rootAcc.node
  -- circuit.rs:551-605 — value-commit integrity
  let magnitude ← loadPrivate (cfg.advices 9) W.magnitude
  let sign ← loadPrivate (cfg.advices 9) W.sign
  let cvNet ← (ValueCommit.circuit B.valueCommitV B.valueCommitR W.rcvWindows).call
    (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
    { magnitude := magnitude, sign := sign }
  constrainInstance cvNet.x cfg.primary CV_NET_X
  constrainInstance cvNet.y cfg.primary CV_NET_Y
  -- circuit.rs:608-624 — nullifier integrity
  let nfOld ← (DeriveNullifier.circuit B.nullifierK).call
    (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
     cfg.eccConfig.add)
    { nk := nk, rho := rhoOld, psi := psiOld, cm := cmOld }
  constrainInstance nfOld cfg.primary NF_OLD
  -- circuit.rs:627-644 — spend authority
  let rk ← (SpendAuthority.circuit B.spendAuthG W.alphaWindows).call
    (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) { akP := akP }
  constrainInstance rk.x cfg.primary RK_X
  constrainInstance rk.y cfg.primary RK_Y
  -- circuit.rs:647-693 — diversified address integrity
  -- (`ak = ak_P.extract_p()`; `ScalarVar::from_base` is region-free)
  let ivk ← (CommitIvk.Main.circuit G B.commitIvkR W.rivkWindows
      B.ivkQ B.ivkQ_onCurve).call
    { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { ak := akP.x, nk := nk }
  let _pkDOld ← (AddressIntegrity.circuit W.pkDOld).call
    (cfg.eccConfig.mul, cfg.eccConfig.witnessPoint) { ivk := ivk, gDOld := gdOld }
  -- circuit.rs:696-729 — old note commitment integrity
  let derivedCmOld ← (NoteCommit.Main.circuit G B.noteCommitR W.rcmOldWindows
      B.noteQ B.noteQ_onCurve).call
    { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { gdX := gdOld.x, gdY := gdOld.y, pkdX := _pkDOld.x, pkdY := _pkDOld.y,
      value := vOld, rho := rhoOld, psi := psiOld }
  assignRegion "constrain equal" (do
    constrainEqual derivedCmOld.x cmOld.x
    constrainEqual derivedCmOld.y cmOld.y)
  -- circuit.rs:731-779 — new note commitment integrity (`rho_new = nf_old`)
  let gdNew ← (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point").call
    cfg.eccConfig.witnessPoint W.gdNew
  let pkdNew ← (Ecc.WitnessPoint.pointNonId.toFormal "witness non-identity point").call
    cfg.eccConfig.witnessPoint W.pkdNew
  let psiNew ← loadPrivate (cfg.advices 0) W.psiNew
  let cmNew ← (NoteCommit.Main.circuit G B.noteCommitR W.rcmNewWindows
      B.noteQ B.noteQ_onCurve).call
    { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { gdX := gdNew.x, gdY := gdNew.y, pkdX := pkdNew.x, pkdY := pkdNew.y,
      value := vNew, rho := nfOld, psi := psiNew }
  constrainInstance cmNew.x cfg.primary CMX
  -- circuit.rs:781-826 — the final `"Orchard circuit checks"` region
  assignRegion "Orchard circuit checks" (do
    let _ ← copyAdvice vOld (cfg.advices 0) 0
    let _ ← copyAdvice vNew (cfg.advices 1) 0
    let _ ← copyAdvice magnitude (cfg.advices 2) 0
    let _ ← copyAdvice sign (cfg.advices 3) 0
    let _ ← copyAdvice root (cfg.advices 4) 0
    let _ ← assignAdviceFromInstance cfg.primary ANCHOR (cfg.advices 5) 0
    let _ ← assignAdviceFromInstance cfg.primary ENABLE_SPEND (cfg.advices 6) 0
    let _ ← assignAdviceFromInstance cfg.primary ENABLE_OUTPUT (cfg.advices 7) 0
    (orchardGate cfg.qOrchard cfg.advices).enable 0)
  pure ()

end Halo2.Ironwood.Action.Circuit
