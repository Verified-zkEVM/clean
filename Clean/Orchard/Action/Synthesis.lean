import Clean.Orchard.Action.ValueCommit
import Clean.Orchard.Action.DeriveNullifier
import Clean.Orchard.Action.SpendAuthority
import Clean.Orchard.Action.AddressIntegrity
import Clean.Orchard.Action.NoteCommit
import Clean.Orchard.Action.Gate
import Clean.Orchard.Ecc.WitnessPoint
import Clean.Orchard.Sinsemilla.Merkle

/-!
# Orchard action synthesis (final assembly)

Clean port of the body of `Circuit::synthesize` in `orchard@0.14.0/src/circuit.rs`: the
final action circuit that composes the mid-level gadgets — Merkle path validity, value
commitment, nullifier derivation, spend authority, diversified-address integrity, and the
old/new note commitments — and ties their outputs to the public instance columns plus the
`q_orchard` arithmetic gate.

This `IntermediateSpec` is a placeholder, faithful "constraints → meaning" postcondition:
each public-instance value equals the corresponding gadget evaluation of the private
witnesses, the calculated Merkle root is the root of `cm_old`, and the `q_orchard`
arithmetic relation holds. It is intended to be *bridged* to a polished, hand-written final
`Spec` by a separate theorem (`*_of_intermediate`); soundness/completeness are therefore
factored through the standalone `intermediate_spec_of_constraints` /
`intermediate_completeness` theorems so the bridge can compose with them.

Public instance column order (source `circuit.rs`):
`ANCHOR=0, CV_NET_X=1, CV_NET_Y=2, NF_OLD=3, RK_X=4, RK_Y=5, CMX=6, ENABLE_SPEND=7,
ENABLE_OUTPUT=8`.
-/

namespace Orchard.Action.Synthesis

open Ecc Ecc.ScalarMul
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Orchard.Specs.Sinsemilla (Generators)
open Orchard.Sinsemilla.Merkle (MerkleRoot depth)

/-- All fixed-base generators / Sinsemilla domains the action circuit composes. Kept as a
single bundle to avoid an unwieldy parameter list; the polished version may share or
specialise these. -/
structure Params where
  /-- Merkle CRH Sinsemilla domain. -/
  Gm : Generators
  Qm : SWPoint Pallas.curve
  hQm : Qm ≠ 0
  /-- Note-commitment Sinsemilla domain (shared by the old and new note commitments). -/
  Gnc : Generators
  Qnc : SWPoint Pallas.curve
  hQnc : Qnc ≠ 0
  /-- Note-commitment blinding base `NoteCommit^Orchard_R`. -/
  Rnc : MulFixed.FixedBase
  /-- `CommitIvk` Sinsemilla domain (used inside diversified-address integrity). -/
  Gci : Generators
  Qci : SWPoint Pallas.curve
  hQci : Qci ≠ 0
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
`Unconstrained`/`UnconstrainedDep` here and are witnessed inside `main`, not exposed as
already-assigned cells. -/
structure Input (F : Type) where
  -- old note
  gdOld : UnconstrainedDep Point F
  pkdOld : UnconstrainedDep Point F
  vOld : UnconstrainedDep field F
  rhoOld : UnconstrainedDep field F
  psiOld : UnconstrainedDep field F
  rcmOld : Unconstrained Fq F
  cmOld : UnconstrainedDep Point F
  -- spend authority / key material
  alpha : Unconstrained Fq F
  akP : UnconstrainedDep Point F
  nk : UnconstrainedDep field F
  rivk : Unconstrained Fq F
  -- new note
  gdNew : UnconstrainedDep Point F
  pkdNew : UnconstrainedDep Point F
  vNew : UnconstrainedDep field F
  psiNew : UnconstrainedDep field F
  rcmNew : Unconstrained Fq F
  -- value commitment
  rcv : Unconstrained Fq F
  vNetMagnitude : UnconstrainedDep field F
  vNetSign : UnconstrainedDep field F
  -- merkle path
  path : UnconstrainedDep (fields 32) F
  pos : Unconstrained (Vector Bool 32) F
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

instance : Inhabited (Var Input Fp) :=
  ⟨{ gdOld := fun _ => default, pkdOld := fun _ => default,
     vOld := fun _ => default, rhoOld := fun _ => default, psiOld := fun _ => default,
     rcmOld := fun _ => default, cmOld := fun _ => default, alpha := fun _ => default,
     akP := fun _ => default, nk := fun _ => default, rivk := fun _ => default,
     gdNew := fun _ => default, pkdNew := fun _ => default,
     vNew := fun _ => default, psiNew := fun _ => default,
     rcmNew := fun _ => default, rcv := fun _ => default,
     vNetMagnitude := fun _ => default, vNetSign := fun _ => default,
     path := fun _ => default, pos := fun _ => default,
     anchor := default, cvNetX := default, cvNetY := default, nfOld := default,
     rkX := default, rkY := default, cmx := default,
     enableSpends := default, enableOutputs := default }⟩

def main (P : Params) (input : Var Input Fp) : Circuit Fp (Var unit Fp) := do
  -- Witness private inputs used across multiple checks, matching the source block at the
  -- start of `Circuit::synthesize`.
  let psiOld ← witnessField input.psiOld
  let rhoOld ← witnessField input.rhoOld
  let cmOld ← WitnessPoint.circuit input.cmOld
  let gdOld ← WitnessNonIdentityPoint.circuit input.gdOld
  let akP ← WitnessNonIdentityPoint.circuit input.akP
  let nk ← witnessField input.nk
  let vOld ← witnessField input.vOld
  let vNew ← witnessField input.vNew
  -- Merkle path validity: leaf = cm_old.extract_p()
  let root ← Orchard.Sinsemilla.Merkle.CalculateRoot.circuit P.Gm P.Qm P.hQm
    { leaf := cmOld.x, path := input.path, pos := input.pos }
  -- Value commitment integrity: cv_net constrained to (CV_NET_X, CV_NET_Y)
  let vNetMagnitude ← witnessField input.vNetMagnitude
  let vNetSign ← witnessField input.vNetSign
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
  let psiNew ← witnessField input.psiNew
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

/-- Soundness preconditions: the witnessed points feeding each gadget are well-formed
Pallas points (the source witnesses them with `Point::new` / `NonIdentityPoint::new`). This
is a placeholder paralleling `IntermediateSpec`, to be bridged to the final hand-written
assumptions. -/
def IntermediateAssumptions (_input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  True

/-- Placeholder "constraints → meaning" postcondition (to be bridged to a polished final
`Spec`). Each public-instance value is the gadget evaluation of the private witnesses; the
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
    Orchard.Sinsemilla.Merkle.CalculateRoot.Spec P.Gm P.Qm
      { leaf := leaf, path := (), pos := () } root pd ∧
    vOld = vNew + vNetMagnitude * vNetSign ∧
    (vOld = 0 ∨ root = input.anchor) ∧
    (vOld = 0 ∨ input.enableSpends = 1) ∧
    (vNew = 0 ∨ input.enableOutputs = 1)

theorem intermediate_spec_of_constraints (P : Params) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main P)
      IntermediateAssumptions (IntermediateSpec P) := by
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
  subst input_gdOld
  subst input_pkdOld
  subst input_vOld
  subst input_rhoOld
  subst input_psiOld
  subst input_rcmOld
  subst input_cmOld
  subst input_alpha
  subst input_akP
  subst input_nk
  subst input_rivk
  subst input_gdNew
  subst input_pkdNew
  subst input_vNew
  subst input_psiNew
  subst input_rcmNew
  subst input_rcv
  subst input_vNetMagnitude
  subst input_vNetSign
  subst input_path
  subst input_pos
  have hSA := hSAImpl (Or.inl hAkPOn)
  have hAI := hAIImpl hGdOldOn
  have hNCold := hNColdImpl ⟨(Point.onCurve_iff _).mp hGdOldOn,
    (Point.onCurve_iff _).mp hPkdOldOn⟩
  have hNCnew := hNCnewImpl ⟨(Point.onCurve_iff _).mp hGdNewOn,
    (Point.onCurve_iff _).mp hPkdNewOn⟩
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
  let merkleInput : Var Orchard.Sinsemilla.Merkle.CalculateRoot.Input Fp :=
    { leaf := (varFromOffset Point (i₀ + 1 + 1)).x,
      path := input_var.path, pos := input_var.pos }
  let afterMerkle : ℕ :=
    i₀ + 1 + 1 + 2 + 2 + 2 + 1 + 1 + 1 +
      (Orchard.Sinsemilla.Merkle.CalculateRoot.circuit P.Gm P.Qm P.hQm).localLength merkleInput
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
  · exact ⟨Or.inr trivial, Or.inr hCmOldValid⟩

/-- Honest-prover preconditions: each composed gadget's `ProverAssumptions` instantiated at
the honest witnesses. Placeholder paralleling `IntermediateAssumptions`, to be bridged to
the final hand-written prover assumptions. The new note's ρ is the public `nf_old` (the
honest prover sets that instance cell to the nullifier it derives). -/
def IntermediateProverAssumptions (P : Params) (input : ProverValue Input Fp)
    (data : ProverData Fp) (hint : ProverHint Fp) : Prop :=
  -- merkle: the authentication-path hash chain succeeds at every layer
  Orchard.Sinsemilla.Merkle.CalculateRoot.ProverAssumptions P.Gm P.Qm
      { leaf := input.cmOld.x, path := input.path, pos := input.pos } data hint ∧
  -- value commitment: the signed magnitude is a 64-bit value with sign ±1
  ValueCommit.ProverAssumptions
      { v := { magnitude := input.vNetMagnitude, sign := input.vNetSign }, rcv := input.rcv }
      data hint ∧
  -- nullifier: `cm_old` is a valid point (DeriveNullifier is a `FormalCircuit`)
  input.cmOld.Valid ∧
  -- spend authority: `ak_P` is a valid point
  SpendAuthority.ProverAssumptions { akP := input.akP, alpha := input.alpha } data hint ∧
  -- diversified address integrity
  AddressIntegrity.ProverAssumptions P.Gci P.Qci P.Rci
      { ak := input.akP.x, nk := input.nk, rivk := input.rivk,
        gDOld := input.gdOld, pkDOld := input.pkdOld } data hint ∧
  -- old note commitment
  NoteCommit.ProverAssumptions P.Gnc P.Qnc
      { gd := input.gdOld, pkd := input.pkdOld, value := input.vOld,
        rho := input.rhoOld, psi := input.psiOld, rcm := input.rcmOld } data hint ∧
  -- new note commitment (ρ = the public nf_old)
  NoteCommit.ProverAssumptions P.Gnc P.Qnc
      { gd := input.gdNew, pkd := input.pkdNew, value := input.vNew,
        rho := input.nfOld, psi := input.psiNew, rcm := input.rcmNew } data hint

/-- Honest-prover postcondition: the deterministic (`ProverSpec`) image of `IntermediateSpec`.
Each public-instance cell is the honest gadget evaluation of the private witnesses. -/
def IntermediateProverSpec (P : Params) (input : ProverValue Input Fp) (_ : Unit)
    (hint : ProverHint Fp) : Prop :=
  ValueCommit.ProverSpec P.V P.Rvc
      { v := { magnitude := input.vNetMagnitude, sign := input.vNetSign }, rcv := input.rcv }
      { x := input.cvNetX, y := input.cvNetY } hint ∧
  DeriveNullifier.Spec P.Knf
      { nk := input.nk, rho := input.rhoOld, psi := input.psiOld, cm := input.cmOld }
      input.nfOld ∧
  SpendAuthority.ProverSpec P.Sag { akP := input.akP, alpha := input.alpha }
      { x := input.rkX, y := input.rkY } hint ∧
  AddressIntegrity.ProverSpec P.Gci P.Qci P.Rci
      input.akP.x input.nk input.rivk input.gdOld input.pkdOld ∧
  NoteCommit.ProverSpec P.Gnc P.Qnc P.Rnc
      { gd := input.gdOld, pkd := input.pkdOld, value := input.vOld,
        rho := input.rhoOld, psi := input.psiOld, rcm := input.rcmOld }
      input.cmOld hint ∧
  (∃ cmNewY : Fp,
    NoteCommit.ProverSpec P.Gnc P.Qnc P.Rnc
      { gd := input.gdNew, pkd := input.pkdNew, value := input.vNew,
        rho := input.nfOld, psi := input.psiNew, rcm := input.rcmNew }
      { x := input.cmx, y := cmNewY } hint) ∧
  (∃ (leaf root : Fp),
    leaf = input.cmOld.x ∧
    Orchard.Sinsemilla.Merkle.CalculateRoot.ProverSpec P.Gm P.Qm
      { leaf := leaf, path := input.path, pos := input.pos } root hint ∧
    (show Fp from input.vOld) =
      (show Fp from input.vNew) +
        (show Fp from input.vNetMagnitude) * (show Fp from input.vNetSign) ∧
    ((show Fp from input.vOld) = 0 ∨ root = input.anchor) ∧
    ((show Fp from input.vOld) = 0 ∨ input.enableSpends = 1) ∧
    ((show Fp from input.vNew) = 0 ∨ input.enableOutputs = 1))

theorem intermediate_completeness (P : Params) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main P)
      (IntermediateProverAssumptions P) (IntermediateProverSpec P) := by
  sorry

def circuit (P : Params) : GeneralFormalCircuit.WithHint Fp Input unit where
  main := main P
  elaborated := elaborated P
  Assumptions := IntermediateAssumptions
  Spec := IntermediateSpec P
  ProverAssumptions := IntermediateProverAssumptions P
  ProverSpec := IntermediateProverSpec P
  soundness := intermediate_spec_of_constraints P
  completeness := intermediate_completeness P

end Orchard.Action.Synthesis
