import Clean.Halo2.CircuitTypeDeriving
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
open Halo2.Ironwood.Specs.Sinsemilla (Generators)

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

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)

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
def DISABLE_CROSS_ADDRESS : ℕ := 9

/-- The fixed bases and Sinsemilla domain points the Action circuit is instantiated at
(Rust reaches them through `OrchardFixedBases` / the domain constants). -/
structure Bases where
  nullifierK : FixedBase
  valueCommitV : Halo2.Ironwood.Ecc.MulFixed.Short.FixedBase
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

/-- Prover-only ℕ-indexed family of Merkle sibling witness programs (one per layer). -/
structure UnconstrainedSibs (F : Type) where
  programs : ℕ → WitgenIR F 1

@[reducible] instance : CircuitType UnconstrainedSibs where
  Var F := ℕ → WitgenIR F 1
  Value := unit
  ProverValue F := ℕ → F
  evalVerifier _ _ := ()
  evalProver pe f := fun i => ((f i).eval pe)[0]

instance : ProvableType (Halo2.Value UnconstrainedSibs) :=
  (inferInstance : ProvableType unit)

/-- Prover-only ℕ-indexed family of Merkle swap flags (native closures — the cond-swap
choice is a `Bool` the prover computes from its environment). -/
structure UnconstrainedSwaps (F : Type) where
  flags : ℕ → Placed ProverEnvironment F → Bool

@[reducible] instance : CircuitType UnconstrainedSwaps where
  Var F := ℕ → Placed ProverEnvironment F → Bool
  Value := unit
  ProverValue _ := ℕ → Bool
  evalVerifier _ _ := ()
  evalProver pe f := fun i => f i pe

instance : ProvableType (Halo2.Value UnconstrainedSwaps) :=
  (inferInstance : ProvableType unit)

/-- The Action circuit's private inputs as a prover-only hint block, derived per-field
(the `Unconstrained` pattern): the `Var` view is the witness programs, the verifier
value is erased, and the prover value is the evaluated data. Mirrors the Rust
`Circuit` struct's `Value<_>` fields; the fixed-base-mul scalars are nat-valued
reading programs, their 85 window witnesses derived inside the mul bundles. -/
structure PrivateInputs (F : Type) where
  psiOld : Unconstrained field F
  rhoOld : Unconstrained field F
  nk : Unconstrained field F
  vOld : Unconstrained field F
  vNew : Unconstrained field F
  psiNew : Unconstrained field F
  magnitude : Unconstrained field F
  sign : Unconstrained field F
  cmOld : Unconstrained Point F
  gdOld : Unconstrained Point F
  akP : Unconstrained Point F
  pkDOld : Unconstrained Point F
  gdNew : Unconstrained Point F
  pkdNew : Unconstrained Point F
  rcv : UnconstrainedNat F
  alpha : UnconstrainedNat F
  rivk : UnconstrainedNat F
  rcmOld : UnconstrainedNat F
  rcmNew : UnconstrainedNat F
  merkleSib : UnconstrainedSibs F
  merkleSwap : UnconstrainedSwaps F
deriving CircuitType

/-- The witness-program view of the private inputs (the Rust `Circuit` struct). -/
abbrev Witnesses (F : Type) := PrivateInputs.Var F

/-- The evaluated (prover-view) private inputs. -/
abbrev WitnessData (F : Type) := PrivateInputs.ProverValue F

/-- Rust `assign_free_advice` (`circuit.rs:101-113`): the `"load private"` region, one
advice cell at row 0. -/
def loadPrivate (col : Column .advice) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp) :=
  assignRegion "load private" (assignAdvice col 0 w)

/-- The shared witness cells (stage A's outputs). -/
structure WitnessCells where
  psiOld : AssignedCell Fp
  rhoOld : AssignedCell Fp
  cmOld : Var Point Fp
  gdOld : Var Point Fp
  akP : Var Point Fp
  nk : AssignedCell Fp
  vOld : AssignedCell Fp
  vNew : AssignedCell Fp

/-- Stage A (8 regions after the table load): the shared witness regions
(`circuit.rs:467-532`). -/
def synthWitness (G : Generators) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp WitnessCells := do
  Sinsemilla.load G cfg.sinsemilla1.generatorTable
  let psiOld ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.psiOld)
  let rhoOld ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.rhoOld)
  let cmOld ← Ecc.WitnessPoint.pointFormal.call
    cfg.eccConfig.witnessPoint W.cmOld
  let gdOld ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.gdOld
  let akP ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.akP
  let nk ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.nk)
  let vOld ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.vOld)
  let vNew ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.vNew)
  pure { psiOld, rhoOld, cmOld, gdOld, akP, nk, vOld, vNew }

/-- Stage B's outputs. -/
structure CheckCells where
  root : AssignedCell Fp
  magnitude : AssignedCell Fp
  sign : AssignedCell Fp
  nfOld : AssignedCell Fp
  pkdOld : Var Point Fp

/-- Stage B (295 regions): the Merkle path, value-commit / nullifier / spend-authority /
diversified-address integrity (`circuit.rs:535-693`). -/
def synthChecks (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config)
    (wc : WitnessCells) : Circuit Fp CheckCells := do
  -- circuit.rs:535-548 — the Merkle path (leaf = cm_old.extract_p); 16 layers per
  -- Sinsemilla instance (`merkle.rs:122-126`, `chips[i / layers_per_chip]`)
  let half ← (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
      0 16 (by norm_num) W.merkleSib W.merkleSwap).call
    (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig) { node := wc.cmOld.x }
  let root ← (Sinsemilla.Merkle.CalculateRoot.circuit G B.merkleQ B.merkleQ_onCurve
      16 16 (by norm_num) (fun i => W.merkleSib (16 + i))
      (fun i => W.merkleSwap (16 + i))).call
    (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig) { node := half }
  -- circuit.rs:551-605 — value-commit integrity
  let magnitude ← loadPrivate (cfg.advices 9) (Witgen.MOver.toIRScalar W.magnitude)
  let sign ← loadPrivate (cfg.advices 9) (Witgen.MOver.toIRScalar W.sign)
  let cvNet ← (ValueCommit.circuit B.valueCommitV B.valueCommitR).call
    (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
    { rcv := W.rcv, magnitude := magnitude, sign := sign }
  constrainInstance cvNet.x cfg.primary CV_NET_X
  constrainInstance cvNet.y cfg.primary CV_NET_Y
  -- circuit.rs:608-624 — nullifier integrity
  let nfOld ← (DeriveNullifier.circuit B.nullifierK).call
    (cfg.poseidonConfig, cfg.addChipConfig, cfg.eccConfig.mulFixedBaseField,
     cfg.eccConfig.add)
    { nk := wc.nk, rho := wc.rhoOld, psi := wc.psiOld, cm := wc.cmOld }
  constrainInstance nfOld cfg.primary NF_OLD
  -- circuit.rs:627-644 — spend authority
  let rk ← (SpendAuthority.circuit B.spendAuthG).call
    (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add) { alpha := W.alpha, akP := wc.akP }
  constrainInstance rk.x cfg.primary RK_X
  constrainInstance rk.y cfg.primary RK_Y
  -- circuit.rs:647-693 — diversified address integrity
  -- (`ak = ak_P.extract_p()`; `ScalarVar::from_base` is region-free)
  let ivk ← (CommitIvk.Main.circuit G B.commitIvkR
      B.ivkQ B.ivkQ_onCurve).call
    { gate := cfg.commitIvkConfig, hashConfig := cfg.sinsemilla1,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { ak := wc.akP.x, nk := wc.nk, rivk := W.rivk }
  let pkdOld ← (AddressIntegrity.circuit).call
    (cfg.eccConfig.mul, cfg.eccConfig.witnessPoint)
    { ivk := ivk, gDOld := wc.gdOld, pkDOld := W.pkDOld }
  pure { root, magnitude, sign, nfOld, pkdOld }

/-- Stage C's outputs: the new-note diversified-address cells (the Rust `AddressPoints`
half the cross-address stage reads; the old halves live in `WitnessCells`/`CheckCells`). -/
structure NoteCells where
  gdNew : Var Point Fp
  pkdNew : Var Point Fp

/-- Stage C (91 regions): old/new note-commitment integrity and the final
`"Orchard circuit checks"` region (`circuit.rs:696-826`). -/
def synthNotes (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config)
    (wc : WitnessCells) (cc : CheckCells) : Circuit Fp NoteCells := do
  -- circuit.rs:696-729 — old note commitment integrity
  let derivedCmOld ← (NoteCommit.Main.circuit G B.noteCommitR
      B.noteQ B.noteQ_onCurve).call
    { gates := cfg.noteCommitOld, hashConfig := cfg.sinsemilla1,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { gdX := wc.gdOld.x, gdY := wc.gdOld.y, pkdX := cc.pkdOld.x, pkdY := cc.pkdOld.y,
      value := wc.vOld, rho := wc.rhoOld, psi := wc.psiOld, rcm := W.rcmOld }
  assignRegion "constrain equal" (do
    constrainEqual derivedCmOld.x wc.cmOld.x
    constrainEqual derivedCmOld.y wc.cmOld.y)
  -- circuit.rs:731-779 — new note commitment integrity (`rho_new = nf_old`)
  let gdNew ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.gdNew
  let pkdNew ← Ecc.WitnessPoint.pointNonIdFormal.call
    cfg.eccConfig.witnessPoint W.pkdNew
  let psiNew ← loadPrivate (cfg.advices 0) (Witgen.MOver.toIRScalar W.psiNew)
  let cmNew ← (NoteCommit.Main.circuit G B.noteCommitR
      B.noteQ B.noteQ_onCurve).call
    { gates := cfg.noteCommitNew, hashConfig := cfg.sinsemilla2,
      lookupConfig := cfg.lookupConfig, mulConfig := cfg.eccConfig.mulFixedFull,
      addConfig := cfg.eccConfig.add }
    { gdX := gdNew.x, gdY := gdNew.y, pkdX := pkdNew.x, pkdY := pkdNew.y,
      value := wc.vNew, rho := cc.nfOld, psi := psiNew, rcm := W.rcmNew }
  constrainInstance cmNew.x cfg.primary CMX
  -- circuit.rs:781-826 — the final `"Orchard circuit checks"` region
  assignRegion "Orchard circuit checks" (do
    let _ ← copyAdvice wc.vOld (cfg.advices 0) 0
    let _ ← copyAdvice wc.vNew (cfg.advices 1) 0
    let _ ← copyAdvice cc.magnitude (cfg.advices 2) 0
    let _ ← copyAdvice cc.sign (cfg.advices 3) 0
    let _ ← copyAdvice cc.root (cfg.advices 4) 0
    let _ ← assignAdviceFromInstance cfg.primary ANCHOR (cfg.advices 5) 0
    let _ ← assignAdviceFromInstance cfg.primary ENABLE_SPEND (cfg.advices 6) 0
    let _ ← assignAdviceFromInstance cfg.primary ENABLE_OUTPUT (cfg.advices 7) 0
    (orchardGate cfg.qOrchard cfg.advices).enable 0)
  pure { gdNew, pkdNew }

/-- Rust `AddressPoints` (ironwood `circuit.rs`): the old/new-note diversified-address
points the cross-address stage compares — the base circuit's output. -/
structure AddressPoints (F : Type) where
  gdOld : Point F
  pkdOld : Point F
  gdNew : Point F
  pkdNew : Point F
deriving ProvableStruct

/-- Ironwood `Circuit::synthesize_cross_address_checks` (`circuit.rs:920-1035`): the
`"post-NU 6.3 cross-address checks"` region — one row per address coordinate, reusing
the `q_orchard` gate as `disableCrossAddress − 0 = disableCrossAddress · 1` (value
row), `disableCrossAddress · (old − new) = 0` (root/anchor row), with both enable
checks neutralized and the rightmost columns occupied against foreign gate rows. -/
def synthCrossAddressChecks (cfg : Config) (pts : Var AddressPoints Fp) :
    Circuit Fp Unit :=
  assignRegion "post-NU 6.3 cross-address checks"
    (RegionCircuit.forRange' 0 1 4 fun _ row => do
      let coords := [(pts.gdOld.x, pts.gdNew.x), (pts.gdOld.y, pts.gdNew.y),
                     (pts.pkdOld.x, pts.pkdNew.x), (pts.pkdOld.y, pts.pkdNew.y)]
      let (oldC, newC) := coords[row]!
      let dca ← assignAdviceFromInstance cfg.primary DISABLE_CROSS_ADDRESS
        (cfg.advices 0) row
      let z ← assignAdvice (cfg.advices 1) row (Poseidon.constWit 0)
      constrainConstant z 0
      let _ ← copyAdvice dca (cfg.advices 2) row
      let o3 ← assignAdvice (cfg.advices 3) row (Poseidon.constWit 1)
      constrainConstant o3 1
      let _ ← copyAdvice oldC (cfg.advices 4) row
      let _ ← copyAdvice newC (cfg.advices 5) row
      let o6 ← assignAdvice (cfg.advices 6) row (Poseidon.constWit 1)
      constrainConstant o6 1
      let o7 ← assignAdvice (cfg.advices 7) row (Poseidon.constWit 1)
      constrainConstant o7 1
      let _ ← copyAdvice dca (cfg.advices 8) row
      let _ ← copyAdvice dca (cfg.advices 9) row
      (orchardGate cfg.qOrchard cfg.advices).enable row)

/-- Rust `Circuit::synthesize_base` (`circuit.rs:461-828`): the staged witness /
integrity-check / note-commitment composition, returning the `AddressPoints` the
ironwood cross-address stage reads. This alone is the pre-ironwood (fixed post-NU 6.2)
circuit — see `Action/CircuitPreIronwood.lean`. -/
def synthesizeBase (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp (Var AddressPoints Fp) := do
  let wc ← synthWitness G W cfg
  let cc ← synthChecks G B W cfg wc
  let nc ← synthNotes G B W cfg wc cc
  pure { gdOld := wc.gdOld, pkdOld := cc.pkdOld, gdNew := nc.gdNew, pkdNew := nc.pkdNew }

/-- The ironwood (post-NU 6.3) `Circuit::synthesize` — THE top-level circuit this repo
targets: the base stages plus the cross-address checks region. -/
def synthesize (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config) :
    Circuit Fp Unit := do
  let pts ← synthesizeBase G B W cfg
  synthCrossAddressChecks cfg pts

end Halo2.Ironwood.Action.Circuit
