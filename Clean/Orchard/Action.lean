import Clean.Orchard.Action.Canonicity
import Clean.Orchard.Action.CanonicityTheorems
import Clean.Orchard.Action.AddressIntegrity
import Clean.Orchard.Action.CommitIvk
import Clean.Orchard.Action.CommitIvkGate
import Clean.Orchard.Action.Decompose
import Clean.Orchard.Action.DeriveNullifier
import Clean.Orchard.Action.Gate
import Clean.Orchard.Action.NoteCommit
import Clean.Orchard.Action.SpendAuthority
import Clean.Orchard.Action.ValueCommit
import Clean.Orchard.Ecc.WitnessPoint
import Clean.Orchard.Sinsemilla.Merkle

/-!
# Orchard action circuit (final assembly)

Clean port of the body of `Circuit::synthesize` in `orchard@0.14.0/src/circuit.rs`: the
final action circuit that composes the mid-level gadgets — Merkle path validity, value
commitment, nullifier derivation, spend authority, diversified-address integrity, and the
old/new note commitments — and ties their outputs to the public instance columns plus the
`q_orchard` arithmetic gate. This module also re-exports the mid-level Orchard action
components used to build it.

The `IntermediateSpec` is a faithful "constraints → meaning" postcondition: each
public-instance value equals the corresponding gadget evaluation of the private witnesses,
the calculated Merkle root is the root of `cm_old`, and the `q_orchard` arithmetic relation
holds. It is intended to be *bridged* to a polished, hand-written final `Spec` by a separate
theorem (`*_of_intermediate`); soundness/completeness are therefore factored through the
standalone `intermediate_spec_of_constraints` / `intermediate_completeness` theorems so the
bridge can compose with them.

Public instance column order (source `circuit.rs`):
`ANCHOR=0, CV_NET_X=1, CV_NET_Y=2, NF_OLD=3, RK_X=4, RK_Y=5, CMX=6, ENABLE_SPEND=7,
ENABLE_OUTPUT=8`.
-/

namespace Orchard.Action

open Ecc
open CompElliptic.Curves.Pasta
open Specs.Sinsemilla (Generators)
open Sinsemilla.Merkle (MerkleRoot depth)

/-- All fixed-base generators / Sinsemilla domains the action circuit composes. Kept as a
single bundle to avoid an unwieldy parameter list; the polished version may share or
specialise these. -/
structure Params where
  /-- Merkle CRH Sinsemilla domain. -/
  Gm : Generators
  Qm : Point Fp
  hQm : Qm.OnCurve
  /-- Note-commitment Sinsemilla domain (shared by the old and new note commitments). -/
  Gnc : Generators
  Qnc : Point Fp
  hQnc : Qnc.OnCurve
  /-- Note-commitment blinding base `NoteCommit^Orchard_R`. -/
  Rnc : MulFixed.FixedBase
  /-- `CommitIvk` Sinsemilla domain (used inside diversified-address integrity). -/
  Gci : Generators
  Qci : Point Fp
  hQci : Qci.OnCurve
  /-- `CommitIvk` blinding base. -/
  Rci : MulFixed.FixedBase
  /-- Value-commitment value base `ValueCommitV` (short) and blinding base `ValueCommitR`. -/
  V : MulFixed.Short.FixedBase
  Rvc : MulFixed.FixedBase
  /-- Nullifier base `K^Orchard`. -/
  Knf : MulFixed.FixedBase
  /-- Spend-authorisation base `SpendAuthG`. -/
  Sag : MulFixed.FixedBase

/-- Inputs of the action circuit: the prover-side private values from `Circuit::synthesize`
plus the nine public-instance cells. Values witnessed by Rust inside `synthesize` are
`Unconstrained`/`UnconstrainedNat` (witgen-IR hint carriers) here and are witnessed inside `main`, not exposed as
already-assigned cells. -/
structure Input (F : Type) where
  -- old note
  gdOld : Unconstrained Point F
  pkdOld : Unconstrained Point F
  vOld : Unconstrained field F
  rhoOld : Unconstrained field F
  psiOld : Unconstrained field F
  rcmOld : UnconstrainedNat F
  cmOld : Unconstrained Point F
  -- spend authority / key material
  alpha : UnconstrainedNat F
  akP : Unconstrained Point F
  nk : Unconstrained field F
  rivk : UnconstrainedNat F
  -- new note
  gdNew : Unconstrained Point F
  pkdNew : Unconstrained Point F
  vNew : Unconstrained field F
  psiNew : Unconstrained field F
  rcmNew : UnconstrainedNat F
  -- value commitment
  rcv : UnconstrainedNat F
  vNetMagnitude : Unconstrained field F
  vNetSign : Unconstrained field F
  -- merkle path
  path : Unconstrained (fields 32) F
  /-- The 32 Merkle position bits, packed into a natural number (bit `i` = layer `i`). -/
  pos : UnconstrainedNat F
  -- public instance cells
  anchor : F
  cvNetX : F
  cvNetY : F
  nfOld : F
  rkX : F
  rkY : F
  cmx : F
  enableSpends : F
  enableOutputs : F
deriving CircuitType

-- TODO derive this along with CircuitType
instance : Inhabited (Var Input Fp) :=
  ⟨{ gdOld := default, pkdOld := default,
     vOld := default, rhoOld := default, psiOld := default,
     rcmOld := default, cmOld := default, alpha := default,
     akP := default, nk := default, rivk := default,
     gdNew := default, pkdNew := default,
     vNew := default, psiNew := default,
     rcmNew := default, rcv := default,
     vNetMagnitude := default, vNetSign := default,
     path := unconstrained (do return default), pos := unconstrainedNat (do return 0),
     anchor := default, cvNetX := default, cvNetY := default, nfOld := default,
     rkX := default, rkY := default, cmx := default,
     enableSpends := default, enableOutputs := default }⟩

def main (P : Params) (input : Var Input Fp) : Circuit Fp (Var unit Fp) := do
  -- Witness private inputs used across multiple checks, matching the source block at the
  -- start of `Circuit::synthesize`.
  let psiOld ← witnessProgram input.psiOld
  let rhoOld ← witnessProgram input.rhoOld
  let cmOld ← WitnessPoint.circuit input.cmOld
  let gdOld ← WitnessNonIdentityPoint.circuit input.gdOld
  let akP ← WitnessNonIdentityPoint.circuit input.akP
  let nk ← witnessProgram input.nk
  let vOld ← witnessProgram input.vOld
  let vNew ← witnessProgram input.vNew
  -- Merkle path validity: leaf = cm_old.extract_p()
  let root ← Sinsemilla.Merkle.CalculateRoot.circuit P.Gm P.Qm P.hQm
    { leaf := cmOld.x, path := input.path, pos := input.pos }
  -- Value commitment integrity: cv_net constrained to (CV_NET_X, CV_NET_Y)
  let vNetMagnitude ← witnessProgram input.vNetMagnitude
  let vNetSign ← witnessProgram input.vNetSign
  let cvNet ← ValueCommit.circuit P.V P.Rvc
    { v := { magnitude := vNetMagnitude, sign := vNetSign }, rcv := input.rcv }
  cvNet === { x := input.cvNetX, y := input.cvNetY }
  -- Nullifier integrity: nf_old constrained to NF_OLD
  let nfOld ← DeriveNullifier.circuit P.Knf
    { nk, rho := rhoOld, psi := psiOld, cm := cmOld }
  nfOld === input.nfOld
  -- Spend authority: rk = [alpha] SpendAuthG + ak_P, constrained to (RK_X, RK_Y)
  let rk ← SpendAuthority.circuit P.Sag
    { akP, alpha := input.alpha }
  rk === { x := input.rkX, y := input.rkY }
  -- Diversified address integrity: pk_d_old = [ivk] g_d_old (constrained internally)
  let pkdOld ← WitnessNonIdentityPoint.circuit input.pkdOld
  let _pkdOld ← AddressIntegrity.circuit P.Gci P.Qci P.hQci P.Rci
    { ak := akP.x, nk, rivk := input.rivk,
      gDOld := gdOld, pkDOld := pkdOld }
  -- Old note commitment integrity: derived cm_old constrained equal to witnessed cm_old
  let cmOldDerived ← NoteCommit.circuit P.Gnc P.Qnc P.hQnc P.Rnc
    { gd := gdOld, pkd := pkdOld, value := vOld,
      rho := rhoOld, psi := psiOld, rcm := input.rcmOld }
  cmOldDerived === cmOld
  -- New note commitment integrity: rho_new = nf_old; cmx = cm_new.extract_p()
  let gdNew ← WitnessNonIdentityPoint.circuit input.gdNew
  let pkdNew ← WitnessNonIdentityPoint.circuit input.pkdNew
  let psiNew ← witnessProgram input.psiNew
  let cmNew ← NoteCommit.circuit P.Gnc P.Qnc P.hQnc P.Rnc
    { gd := gdNew, pkd := pkdNew, value := vNew,
      rho := nfOld, psi := psiNew, rcm := input.rcmNew }
  cmNew.x === input.cmx
  -- q_orchard arithmetic checks
  Gate.circuit
    { vOld, vNew,
      magnitude := vNetMagnitude, sign := vNetSign,
      root := root, anchor := input.anchor,
      enableSpends := input.enableSpends, enableOutputs := input.enableOutputs }

instance elaborated (P : Params) : ElaboratedCircuit Fp Input unit (main P) := by
  elaborate_circuit

/-- Placeholder spec, to be bridged to a polished final
`Spec`. Each public-instance value is the gadget evaluation of the private witnesses; the
calculated Merkle root validates `cm_old`; the `q_orchard` arithmetic relation holds. -/
def IntermediateSpec (P : Params) (input : Value Input Fp) (_ : Unit)
    (pd : ProverData Fp) : Prop :=
  -- value commitment: the public point (CV_NET_X, CV_NET_Y) is cv_net
  ∃ (vNetMagnitude vNetSign : Fp),
    ValueCommit.Spec P.V P.Rvc
      { v := { magnitude := vNetMagnitude, sign := vNetSign }, rcv := () }
      { x := input.cvNetX, y := input.cvNetY } pd ∧
  -- nullifier: the public NF_OLD is nf_old
  ∃ (cmOld : Point Fp) (nk rhoOld psiOld : Fp),
    DeriveNullifier.Spec P.Knf
      { nk, rho := rhoOld, psi := psiOld, cm := cmOld }
      input.nfOld ∧
  -- spend authority: the public (RK_X, RK_Y) is rk = [alpha] SpendAuthG + ak_P
  ∃ (akP : Point Fp),
    SpendAuthority.Spec P.Sag
      { akP, alpha := () }
      { x := input.rkX, y := input.rkY } pd ∧
  -- address integrity: the witnessed pk_d_old equals [ivk] g_d_old
  ∃ (gdOld pkdOld : Point Fp) (vOld : Fp),
    AddressIntegrity.Spec P.Gci P.Qci P.Rci
      akP.x nk gdOld pkdOld ∧
  -- old note commitment: the relation holds for the witnessed cm_old
    NoteCommit.Spec P.Gnc P.Qnc P.Rnc
      { gd := gdOld, pkd := pkdOld, value := vOld,
        rho := rhoOld, psi := psiOld, rcm := () }
      cmOld pd ∧
  -- new note commitment: its ρ is the nullifier nf_old, and the commitment is the point
  -- `(CMX, y)` for some `y` (i.e. its x-coordinate is the public CMX)
  ∃ (gdNew pkdNew : Point Fp) (vNew psiNew cmNewY : Fp),
    NoteCommit.Spec P.Gnc P.Qnc P.Rnc
      { gd := gdNew, pkd := pkdNew, value := vNew,
        rho := input.nfOld, psi := psiNew, rcm := () }
      { x := input.cmx, y := cmNewY } pd ∧
  -- merkle path + q_orchard checks. The leaf (`cm_old.x`) is bound existentially, and the
  -- calculated-root relation is stated via the gadget's own `CalculateRoot.Spec`
  -- (definitionally `MerkleRoot … 0 leaf depth root`).
  ∃ (leaf root : Fp),
    leaf = cmOld.x ∧
    Sinsemilla.Merkle.CalculateRoot.Spec P.Gm P.Qm
      { leaf := leaf, path := (), pos := () } root pd ∧
    vOld = vNew + vNetMagnitude * vNetSign ∧
    (vOld = 0 ∨ root = input.anchor) ∧
    (vOld = 0 ∨ input.enableSpends = (1 : Fp)) ∧
    (vNew = 0 ∨ input.enableOutputs = (1 : Fp))

theorem intermediateSpec_of_constraints (P : Params) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main P)
      (fun _ _ => True) (IntermediateSpec P) := by
  -- Keep `CalculateRoot.circuit` out of the lemma list to avoid the known Merkle output
  -- whnf blow-up; its soundness implication is used directly below.
  circuit_proof_start [WitnessPoint.circuit, WitnessNonIdentityPoint.circuit,
    ValueCommit.circuit, DeriveNullifier.circuit, SpendAuthority.circuit,
    AddressIntegrity.circuit, NoteCommit.circuit, Gate.circuit]
  rcases h_holds with
    ⟨hCmOldValid, hGdOldOn, hAkPOn, hMerkleImpl,
      hVC, hVCeq, hNFImpl, hNFeq, hSAImpl, hSAeq,
      hPkdOldOn, hAIImpl, hNColdImpl, hNColdEq,
      hGdNewOn, hPkdNewOn, hNCnewImpl, hNCnewXEq, hGate⟩
  have hNF := hNFImpl hCmOldValid
  rcases h_input with
    ⟨hGdOldIn, hPkdOldIn, hVOldIn, hRhoOldIn, hPsiOldIn,
      hRcmOldIn, hCmOldIn, hAlphaIn, hAkPIn, hNkIn, hRivkIn,
      hGdNewIn, hPkdNewIn, hVNewIn, hPsiNewIn, hRcmNewIn,
      hRcvIn, hVNetMagnitudeIn, hVNetSignIn, hPathIn, hPosIn,
      hAnchorIn, hCvNetXIn, hCvNetYIn, hNfOldIn, hRkXIn, hRkYIn,
      hCmxIn, hEnableSpendsIn, hEnableOutputsIn⟩
  subst input_gdOld input_pkdOld input_vOld input_rhoOld input_psiOld
    input_rcmOld input_cmOld input_alpha input_akP input_nk input_rivk input_gdNew
    input_pkdNew input_vNew input_psiNew input_rcmNew input_rcv input_vNetMagnitude
    input_vNetSign input_path input_pos
  have hSA := hSAImpl (Or.inl hAkPOn)
  have hAI := hAIImpl hGdOldOn
  have hNCold := hNColdImpl ⟨hGdOldOn, hPkdOldOn⟩
  have hNCnew := hNCnewImpl ⟨hGdNewOn, hPkdNewOn⟩
  have hMerkle := hMerkleImpl trivial
  simp only [Gate.Spec] at hGate
  let cmOld : Point Fp :=
    { x := Expression.eval env (varFromOffset Point (i₀ + 1 + 1)).x,
      y := Expression.eval env (varFromOffset Point (i₀ + 1 + 1)).y }
  let gdOld : Point Fp :=
    { x := Expression.eval env (varFromOffset Point (i₀ + 1 + 1 + 2)).x,
      y := Expression.eval env (varFromOffset Point (i₀ + 1 + 1 + 2)).y }
  let akP : Point Fp :=
    { x := Expression.eval env (varFromOffset Point (i₀ + 1 + 1 + 2 + 2)).x,
      y := Expression.eval env (varFromOffset Point (i₀ + 1 + 1 + 2 + 2)).y }
  let nk : Fp := env.get (i₀ + 1 + 1 + 2 + 2 + 2)
  let vOld : Fp := env.get (i₀ + 1 + 1 + 2 + 2 + 2 + 1)
  let vNew : Fp := env.get (i₀ + 1 + 1 + 2 + 2 + 2 + 1 + 1)
  let rhoOld : Fp := env.get (i₀ + 1)
  let psiOld : Fp := env.get i₀
  let merkleInput : Var Sinsemilla.Merkle.CalculateRoot.Input Fp :=
    { leaf := (varFromOffset Point (i₀ + 1 + 1)).x,
      path := input_var.path, pos := input_var.pos }
  let afterMerkle : ℕ :=
    i₀ + 1 + 1 + 2 + 2 + 2 + 1 + 1 + 1 +
      (Sinsemilla.Merkle.CalculateRoot.circuit P.Gm P.Qm P.hQm).localLength merkleInput
  let vNetMagnitude : Fp := env.get afterMerkle
  let vNetSign : Fp := env.get (afterMerkle + 1)
  have hVCSpec :
      ValueCommit.Spec P.V P.Rvc
        { v := { magnitude := vNetMagnitude, sign := vNetSign }, rcv := () }
        { x := input_cvNetX, y := input_cvNetY } env.data :=
    hVCeq ▸ hVC
  have hNFSpec :
      DeriveNullifier.Spec P.Knf
        { nk, rho := rhoOld, psi := psiOld, cm := cmOld }
        input_nfOld :=
    hNFeq ▸ hNF
  have hOldCore :
      ∃ (pkdOld : Point Fp),
        AddressIntegrity.Spec P.Gci P.Qci P.Rci
          akP.x nk gdOld pkdOld ∧
        NoteCommit.Spec P.Gnc P.Qnc P.Rnc
          { gd := gdOld, pkd := pkdOld, value := vOld,
            rho := rhoOld, psi := psiOld, rcm := () }
          cmOld env.data := by
    exact ⟨_, hAI, by
      change NoteCommit.Spec P.Gnc P.Qnc P.Rnc
        { gd := gdOld, pkd := _, value := vOld,
          rho := rhoOld, psi := psiOld, rcm := () }
        { x := Expression.eval env (varFromOffset Point (i₀ + 1 + 1)).x,
          y := Expression.eval env (varFromOffset Point (i₀ + 1 + 1)).y }
        env.data
      exact hNColdEq ▸ hNCold⟩
  have hNewCore :
      ∃ (gdNew pkdNew : Point Fp) (psiNew cmNewY : Fp),
        NoteCommit.Spec P.Gnc P.Qnc P.Rnc
          { gd := gdNew, pkd := pkdNew, value := vNew,
            rho := input_nfOld, psi := psiNew, rcm := () }
          { x := input_cmx, y := cmNewY } env.data := by
    exact ⟨_, _, _, _, by
      rw [← hNFeq, ← hNCnewXEq]
      exact hNCnew⟩
  rcases hOldCore with ⟨pkdOld, hAISpec, hNColdSpec⟩
  rcases hNewCore with ⟨gdNew, pkdNew, psiNew, cmNewY, hNCnewSpec⟩
  refine ⟨?_, ?_⟩
  · dsimp only [IntermediateSpec]
    refine ⟨vNetMagnitude, vNetSign, hVCSpec,
      cmOld, nk, rhoOld, psiOld, hNFSpec,
      akP, ?_, gdOld, pkdOld, vOld, hAISpec, hNColdSpec,
      gdNew, pkdNew, vNew, psiNew, cmNewY, hNCnewSpec,
      ?_⟩
    · exact hSAeq ▸ hSA
    · refine ⟨_, _, rfl, hMerkle, hGate.1, hGate.2.1, hGate.2.2.1, hGate.2.2.2⟩
  · exact Or.inl rfl

/-- Honest-prover preconditions for the *top-level* action circuit. There is no parent
circuit, so the `ProverSpec` is the default `True`; consequently completeness must establish
every constraint — including the public-instance equality edges and the `q_orchard` gate —
directly from these assumptions. They have two parts:

* **(A) gadget input well-formedness**, so each composed subcircuit's own constraints are
  satisfiable (the witnessed points are on-curve / valid, magnitudes are 64-bit, the
  Sinsemilla/Merkle hash chains succeed);
* **(B) public-instance consistency**: the honest prover sets each instance cell to the
  gadget output it computes. This is exactly the deterministic (`ProverSpec`) image of
  `IntermediateSpec`, and is what discharges the `===` edges and the gate. -/
def IntermediateProverAssumptions (P : Params) (input : ProverValue Input Fp)
    (data : ProverData Fp) (hint : ProverHint Fp) : Prop :=
  -- (A) gadget input well-formedness
  Sinsemilla.Merkle.CalculateRoot.ProverAssumptions P.Gm P.Qm
      { leaf := input.cmOld.x, path := input.path, pos := input.pos } data hint ∧
  ValueCommit.ProverAssumptions
      { v := { magnitude := input.vNetMagnitude, sign := input.vNetSign }, rcv := input.rcv }
      data hint ∧
  input.cmOld.Valid ∧
  -- `ak_P` is a non-identity point (`NonIdentityPoint::new` in the source); this also
  -- supplies SpendAuthority's weaker `Valid` precondition.
  input.akP.OnCurve ∧
  -- the spend-authority randomizer hint is the canonical natural representative of
  -- `alpha : Fq`
  (show ℕ from input.alpha) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
  AddressIntegrity.ProverAssumptions P.Gci P.Qci P.Rci
      { ak := input.akP.x, nk := input.nk, rivk := input.rivk,
        gDOld := input.gdOld, pkDOld := input.pkdOld } data hint ∧
  NoteCommit.ProverAssumptions P.Gnc P.Qnc
      { gd := input.gdOld, pkd := input.pkdOld, value := input.vOld,
        rho := input.rhoOld, psi := input.psiOld, rcm := input.rcmOld } data hint ∧
  NoteCommit.ProverAssumptions P.Gnc P.Qnc
      { gd := input.gdNew, pkd := input.pkdNew, value := input.vNew,
        rho := input.nfOld, psi := input.psiNew, rcm := input.rcmNew } data hint ∧
  -- (B) public-instance consistency (honest prover sets each instance cell to its output)
  ValueCommit.ProverSpec P.V P.Rvc
      { v := { magnitude := input.vNetMagnitude, sign := input.vNetSign }, rcv := input.rcv }
      { x := input.cvNetX, y := input.cvNetY } hint ∧
  DeriveNullifier.Spec P.Knf
      { nk := input.nk, rho := input.rhoOld, psi := input.psiOld, cm := input.cmOld }
      input.nfOld ∧
  SpendAuthority.ProverSpec P.Sag { akP := input.akP, alpha := input.alpha }
      { x := input.rkX, y := input.rkY } hint ∧
  NoteCommit.ProverSpec P.Gnc P.Qnc P.Rnc
      { gd := input.gdOld, pkd := input.pkdOld, value := input.vOld,
        rho := input.rhoOld, psi := input.psiOld, rcm := input.rcmOld }
      input.cmOld hint ∧
  (∃ cmNewY : Fp,
    NoteCommit.ProverSpec P.Gnc P.Qnc P.Rnc
      { gd := input.gdNew, pkd := input.pkdNew, value := input.vNew,
        rho := input.nfOld, psi := input.psiNew, rcm := input.rcmNew }
      { x := input.cmx, y := cmNewY } hint) ∧
  (∃ root : Fp,
    Sinsemilla.Merkle.CalculateRoot.ProverSpec P.Gm P.Qm
      { leaf := input.cmOld.x, path := input.path, pos := input.pos } root hint ∧
    input.vOld =
      (show Fp from input.vNew) +
        (show Fp from input.vNetMagnitude) * (show Fp from input.vNetSign) ∧
    (input.vOld = (0 : Fp) ∨ root = input.anchor) ∧
    (input.vOld = (0 : Fp) ∨ input.enableSpends = (1 : Fp)) ∧
    (input.vNew = (0 : Fp) ∨ input.enableOutputs = (1 : Fp)))

theorem constraints_of_intermediateProverAssumptions (P : Params) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main P)
      (IntermediateProverAssumptions P) (fun _ _ _ => True) := by
  circuit_proof_start [WitnessPoint.circuit, WitnessNonIdentityPoint.circuit,
    ValueCommit.circuit, DeriveNullifier.circuit, SpendAuthority.circuit,
    AddressIntegrity.circuit, NoteCommit.circuit, Gate.circuit]
  obtain ⟨haMerkle, haVC, haCmOld, haAkP, haAlpha, haAI, haNCold, haNCnew,
    hcVC, hcNF, hcSA, hcNColdSpec, hcNCnew, hcMerkleGate⟩ := h_assumptions
  obtain ⟨ePsiOld, eRhoOld, eCmOld, eGdOld, eAkP, eNk, eVOld, eVNew, eMerkle,
    eVNetMag, eVNetSign, eVC, eNF, eSA, ePkdOld, eAI, eNCold, eGdNew, ePkdNew,
    ePsiNew, eNCnew⟩ := h_env
  -- on-curve facts for the witnessed points
  have hGdOldOn : Point.OnCurve input_gdOld := haNCold.1
  have hPkdOldOn : Point.OnCurve input_pkdOld := haNCold.2.1
  have hGdNewOn : Point.OnCurve input_gdNew := haNCnew.1
  have hPkdNewOn : Point.OnCurve input_pkdNew := haNCnew.2.1
  -- witness-cell equalities
  have cmOldCell := (eCmOld haCmOld).2
  have gdOldCell := (eGdOld hGdOldOn).2
  have akPCell := (eAkP haAkP).2
  have pkdOldCell := (ePkdOld hPkdOldOn).2
  have gdNewCell := (eGdNew hGdNewOn).2
  have pkdNewCell := (ePkdNew hPkdNewOn).2
  have cmOldX : Expression.eval env.toEnvironment (varFromOffset Point (i₀ + 1 + 1)).x
      = input_cmOld.x := congrArg Point.x cmOldCell
  have akPX : Expression.eval env.toEnvironment (varFromOffset Point (i₀ + 1 + 1 + 2 + 2)).x
      = input_akP.x := congrArg Point.x akPCell
  -- nullifier edge: the DeriveNullifier output cell equals the public NF_OLD.
  have hNfSpec := eNF (by show Point.Valid _; rw [cmOldCell]; exact haCmOld)
  rw [eNk, eRhoOld, ePsiOld, cmOldCell, DeriveNullifier.Spec] at hNfSpec
  have hNfEdge := hNfSpec.trans hcNF.symm
  -- spend-authority edge: the SpendAuthority output cell equals the public (RK_X, RK_Y).
  have hSAProver := (eSA ⟨by show Point.Valid _; rw [akPCell]; exact Or.inl haAkP,
    haAlpha⟩).2
  rw [akPCell, SpendAuthority.ProverSpec] at hSAProver
  rw [SpendAuthority.ProverSpec] at hcSA
  have hRkEdge := hSAProver.trans hcSA.symm
  -- value-commitment edge: the ValueCommit output cell equals the public (CV_NET_X, CV_NET_Y).
  have hVCProver := (eVC (by rw [eVNetMag, eVNetSign]; exact haVC)).2
  rw [eVNetMag, eVNetSign, ValueCommit.ProverSpec] at hVCProver
  rw [ValueCommit.ProverSpec] at hcVC
  have hCvEdge :=
    haVC.2.1.elim
      (fun hs => (hVCProver.1 hs).trans (hcVC.1 hs).symm)
      (fun hs => (hVCProver.2 hs).trans (hcVC.2 hs).symm)
  -- old note-commitment edge: the derived cm_old output cell equals the witnessed cm_old.
  have hNCoProver := (eNCold (by
    rw [gdOldCell, pkdOldCell, eVOld, eRhoOld, ePsiOld]; exact haNCold)).2
  rw [gdOldCell, pkdOldCell, eVOld, eRhoOld, ePsiOld,
    NoteCommit.ProverSpec, NoteCommit.ProverNoteCommitRelation] at hNCoProver
  rw [NoteCommit.ProverSpec, NoteCommit.ProverNoteCommitRelation] at hcNColdSpec
  obtain ⟨Bold, hBold⟩ := haNCold.2.2.2.2
  have hNCoEdge := (hNCoProver Bold hBold).trans (hcNColdSpec Bold hBold).symm
  -- new note-commitment edge: the derived cm_new output cell's x-coordinate equals CMX.
  obtain ⟨cmNewY, hcNCnewSpec⟩ := hcNCnew
  have hNCnProver := (eNCnew (by
    rw [gdNewCell, pkdNewCell, eVNew, ePsiNew, hNfEdge]; exact haNCnew)).2
  rw [gdNewCell, pkdNewCell, eVNew, ePsiNew, hNfEdge,
    NoteCommit.ProverSpec, NoteCommit.ProverNoteCommitRelation] at hNCnProver
  rw [NoteCommit.ProverSpec, NoteCommit.ProverNoteCommitRelation] at hcNCnewSpec
  obtain ⟨Bnew, hBnew⟩ := haNCnew.2.2.2.2
  have hCmnEdge := (hNCnProver Bnew hBnew).trans (hcNCnewSpec Bnew hBnew).symm
  refine ⟨haCmOld, hGdOldOn, haAkP, ?_, ?_⟩
  · -- Merkle ProverAssumptions
    rw [cmOldX]; exact haMerkle
  refine ⟨?vcpa, ?cvedge, ?dnassum, ?nfedge, ?sapa, ?rkedge, ?pkdold, ?aipa,
    ?ncoldpa, ?ncoldedge, ?gdnew, ?pkdnew, ?ncnewpa, ?cmnewedge, ?gate⟩
  case vcpa => rw [eVNetMag, eVNetSign]; exact haVC
  case cvedge => exact hCvEdge
  case dnassum =>
    show Point.Valid _
    rw [cmOldCell]; exact haCmOld
  case nfedge => exact hNfEdge
  case sapa =>
    exact ⟨by show Point.Valid _; rw [akPCell]; exact Or.inl haAkP, haAlpha⟩
  case rkedge => exact hRkEdge
  case pkdold => exact hPkdOldOn
  case aipa =>
    rw [akPX, eNk, gdOldCell, pkdOldCell]; exact haAI
  case ncoldpa =>
    rw [gdOldCell, pkdOldCell, eVOld, eRhoOld, ePsiOld]; exact haNCold
  case ncoldedge => exact hNCoEdge.trans cmOldCell.symm
  case gdnew => exact hGdNewOn
  case pkdnew => exact hPkdNewOn
  case ncnewpa =>
    rw [gdNewCell, pkdNewCell, eVNew, ePsiNew, hNfEdge]; exact haNCnew
  case cmnewedge => exact congrArg Point.x hCmnEdge
  case gate =>
    obtain ⟨mroot, hMrootSpec, hVeq, hRoot, hSpend, hOut⟩ := hcMerkleGate
    -- the witnessed Merkle root cell equals the root determined by the honest hash chain.
    obtain ⟨r₀, hr₀⟩ := Option.isSome_iff_exists.mp haMerkle
    have hMerkleProver := (eMerkle (by rw [cmOldX]; exact haMerkle)).2
    rw [cmOldX] at hMerkleProver
    simp only [Sinsemilla.Merkle.CalculateRoot.ProverSpec] at hMerkleProver hMrootSpec
    have hRootEdge : Expression.eval env.toEnvironment
        ((Sinsemilla.Merkle.CalculateRoot.circuit P.Gm P.Qm P.hQm).output _ _) = mroot :=
      (hMerkleProver r₀ hr₀).trans (hMrootSpec r₀ hr₀).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [eVOld, eVNew, eVNetMag, eVNetSign]; exact hVeq
    · rw [eVOld, hRootEdge]; exact hRoot
    · rw [eVOld]; exact hSpend
    · rw [eVNew]; exact hOut

def circuit (P : Params) : GeneralFormalCircuit.WithHint Fp Input unit where
  main := main P
  elaborated := elaborated P
  Spec := IntermediateSpec P
  ProverAssumptions := IntermediateProverAssumptions P
  soundness := intermediateSpec_of_constraints P
  completeness := constraints_of_intermediateProverAssumptions P
  requirementsChannelsLawful := by
    try dsimp only [main]
    simp only [circuit_norm, seval]
    try first | ac_rfl | trivial | tauto

end Orchard.Action
