import Clean.Orchard.Action.ValueCommit
import Clean.Orchard.Action.DeriveNullifier
import Clean.Orchard.Action.SpendAuthority
import Clean.Orchard.Action.AddressIntegrity
import Clean.Orchard.Action.NoteCommit
import Clean.Orchard.Action.Gate
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

/-- Inputs of the action circuit: every privately-witnessed value of `Circuit::synthesize`
plus the nine public-instance cells (modelled as ordinary input cells that the body
constrains the gadget outputs equal to). -/
structure Input (F : Type) where
  -- old note
  gdOld : Point F
  pkdOld : Point F
  vOld : F
  rhoOld : F
  psiOld : F
  rcmOld : Unconstrained Fq F
  cmOld : Point F
  -- spend authority / key material
  alpha : Unconstrained Fq F
  akP : Point F
  nk : F
  rivk : Unconstrained Fq F
  -- new note
  gdNew : Point F
  pkdNew : Point F
  vNew : F
  psiNew : F
  rcmNew : Unconstrained Fq F
  -- value commitment
  rcv : Unconstrained Fq F
  vNetMagnitude : F
  vNetSign : F
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
  ⟨{ gdOld := { x := default, y := default }, pkdOld := { x := default, y := default },
     vOld := default, rhoOld := default, psiOld := default, rcmOld := fun _ => default,
     cmOld := { x := default, y := default }, alpha := fun _ => default,
     akP := { x := default, y := default }, nk := default, rivk := fun _ => default,
     gdNew := { x := default, y := default }, pkdNew := { x := default, y := default },
     vNew := default, psiNew := default, rcmNew := fun _ => default, rcv := fun _ => default,
     vNetMagnitude := default, vNetSign := default,
     path := fun _ => default, pos := fun _ => default,
     anchor := default, cvNetX := default, cvNetY := default, nfOld := default,
     rkX := default, rkY := default, cmx := default,
     enableSpends := default, enableOutputs := default }⟩

def main (P : Params) (input : Var Input Fp) : Circuit Fp (Var unit Fp) := do
  -- Merkle path validity: leaf = cm_old.extract_p()
  let root ← Orchard.Sinsemilla.Merkle.CalculateRoot.circuit P.Gm P.Qm P.hQm
    { leaf := input.cmOld.x, path := input.path, pos := input.pos }
  -- Value commitment integrity: cv_net constrained to (CV_NET_X, CV_NET_Y)
  let cvNet ← ValueCommit.circuit P.V P.Rvc
    { v := { magnitude := input.vNetMagnitude, sign := input.vNetSign }, rcv := input.rcv }
  cvNet === { x := input.cvNetX, y := input.cvNetY }
  -- Nullifier integrity: nf_old constrained to NF_OLD
  let nfOld ← DeriveNullifier.circuit P.Knf
    { nk := input.nk, rho := input.rhoOld, psi := input.psiOld, cm := input.cmOld }
  nfOld === input.nfOld
  -- Spend authority: rk = [alpha] SpendAuthG + ak_P, constrained to (RK_X, RK_Y)
  let rk ← SpendAuthority.circuit P.Sag
    { akP := input.akP, alpha := input.alpha }
  rk === { x := input.rkX, y := input.rkY }
  -- Diversified address integrity: pk_d_old = [ivk] g_d_old (constrained internally)
  let _pkdOld ← AddressIntegrity.circuit P.Gci P.Qci P.hQci P.Rci
    { ak := input.akP.x, nk := input.nk, rivk := input.rivk,
      gDOld := input.gdOld, pkDOld := input.pkdOld }
  -- Old note commitment integrity: derived cm_old constrained equal to witnessed cm_old
  let cmOldDerived ← NoteCommit.circuit P.Gnc P.Qnc P.hQnc P.Rnc
    { gd := input.gdOld, pkd := input.pkdOld, value := input.vOld,
      rho := input.rhoOld, psi := input.psiOld, rcm := input.rcmOld }
  cmOldDerived === input.cmOld
  -- New note commitment integrity: rho_new = nf_old; cmx = cm_new.extract_p()
  let cmNew ← NoteCommit.circuit P.Gnc P.Qnc P.hQnc P.Rnc
    { gd := input.gdNew, pkd := input.pkdNew, value := input.vNew,
      rho := nfOld, psi := input.psiNew, rcm := input.rcmNew }
  cmNew.x === input.cmx
  -- q_orchard arithmetic checks
  Gate.circuit
    { vOld := input.vOld, vNew := input.vNew,
      magnitude := input.vNetMagnitude, sign := input.vNetSign,
      root := root, anchor := input.anchor,
      enableSpends := input.enableSpends, enableOutputs := input.enableOutputs }

instance elaborated (P : Params) : ElaboratedCircuit Fp Input unit (main P) := by
  elaborate_circuit

/-- Soundness preconditions: the witnessed points feeding each gadget are well-formed
Pallas points (the source witnesses them with `Point::new` / `NonIdentityPoint::new`). -/
def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  Pallas.OnCurve input.gdOld.coords ∧ Pallas.OnCurve input.pkdOld.coords ∧
  Pallas.OnCurve input.gdNew.coords ∧ Pallas.OnCurve input.pkdNew.coords ∧
  Pallas.Valid input.cmOld.coords ∧ Pallas.Valid input.akP.coords

/-- Placeholder "constraints → meaning" postcondition (to be bridged to a polished final
`Spec`). Each public-instance value is the gadget evaluation of the private witnesses; the
calculated Merkle root validates `cm_old`; the `q_orchard` arithmetic relation holds. -/
def IntermediateSpec (P : Params) (input : Value Input Fp) (_ : Unit)
    (pd : ProverData Fp) : Prop :=
  -- value commitment: the public point (CV_NET_X, CV_NET_Y) is cv_net
  ValueCommit.Spec P.V P.Rvc
      { v := { magnitude := input.vNetMagnitude, sign := input.vNetSign }, rcv := input.rcv }
      { x := input.cvNetX, y := input.cvNetY } pd ∧
  -- nullifier: the public NF_OLD is nf_old
  DeriveNullifier.Spec P.Knf
      { nk := input.nk, rho := input.rhoOld, psi := input.psiOld, cm := input.cmOld }
      input.nfOld ∧
  -- spend authority: the public (RK_X, RK_Y) is rk = [alpha] SpendAuthG + ak_P
  SpendAuthority.Spec P.Sag
      { akP := input.akP, alpha := input.alpha }
      { x := input.rkX, y := input.rkY } pd ∧
  -- address integrity: the witnessed pk_d_old equals [ivk] g_d_old
  AddressIntegrity.Spec P.Gci P.Qci P.Rci
      input.akP.x input.nk input.gdOld input.pkdOld ∧
  -- old note commitment: the relation holds for the witnessed cm_old
  NoteCommit.Spec P.Gnc P.Qnc P.Rnc
      { gd := input.gdOld, pkd := input.pkdOld, value := input.vOld,
        rho := input.rhoOld, psi := input.psiOld, rcm := input.rcmOld }
      input.cmOld pd ∧
  -- new note commitment: its ρ is the nullifier nf_old, and the commitment is the point
  -- `(CMX, y)` for some `y` (i.e. its x-coordinate is the public CMX)
  (∃ cmNewY : Fp,
    NoteCommit.Spec P.Gnc P.Qnc P.Rnc
      { gd := input.gdNew, pkd := input.pkdNew, value := input.vNew,
        rho := input.nfOld, psi := input.psiNew, rcm := input.rcmNew }
      { x := input.cmx, y := cmNewY } pd) ∧
  -- merkle path + q_orchard checks. The leaf (`cm_old.x`) is bound existentially, and the
  -- calculated-root relation is stated via the gadget's own `CalculateRoot.Spec`
  -- (definitionally `MerkleRoot … 0 leaf depth root`).
  (∃ (leaf root : Fp),
    leaf = input.cmOld.x ∧
    Orchard.Sinsemilla.Merkle.CalculateRoot.Spec P.Gm P.Qm
      { leaf := leaf, path := (), pos := () } root pd ∧
    input.vOld = input.vNew + input.vNetMagnitude * input.vNetSign ∧
    (input.vOld = 0 ∨ root = input.anchor) ∧
    (input.vOld = 0 ∨ input.enableSpends = 1) ∧
    (input.vNew = 0 ∨ input.enableOutputs = 1))

theorem intermediate_spec_of_constraints (P : Params) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main P) Assumptions (IntermediateSpec P) := by
  -- `circuit_proof_start` with the six non-recursive children. CalculateRoot.circuit is
  -- deliberately omitted from the lemma list: its foldl-based output makes the tactic's
  -- final goal-rewrite blow the kernel budget. The merkle child's spec is extracted at its
  -- own hypothesis below instead.
  circuit_proof_start [ValueCommit.circuit, DeriveNullifier.circuit, SpendAuthority.circuit,
    AddressIntegrity.circuit, NoteCommit.circuit, Gate.circuit]
  -- name composed-gadget facts via projections (discharging each child's Assumptions)
  have hVCeq := h_holds.2.2.1
  have hNFeq := h_holds.2.2.2.2.1
  have hSAeq := h_holds.2.2.2.2.2.2.1
  have hNColdEq := h_holds.2.2.2.2.2.2.2.2.2.1
  have hNCnewEq := h_holds.2.2.2.2.2.2.2.2.2.2.2.1
  have hVC := h_holds.2.1
  have hNF := h_holds.2.2.2.1 (by exact h_assumptions.2.2.2.2.1)
  have hSA := h_holds.2.2.2.2.2.1
    (by simp only [SpendAuthority.Assumptions]
        exact (Point.valid_iff input_akP).mpr h_assumptions.2.2.2.2.2)
  have hAI := h_holds.2.2.2.2.2.2.2.1 (by exact h_assumptions.1)
  have hNCold := h_holds.2.2.2.2.2.2.2.2.1 (by exact ⟨h_assumptions.1, h_assumptions.2.1⟩)
  have hNCnew := h_holds.2.2.2.2.2.2.2.2.2.2.1
    (by exact ⟨h_assumptions.2.2.1, h_assumptions.2.2.2.1⟩)
  -- merkle child: omitted from the lemma list, so it is the raw (trivial-Assumptions) impl
  have hMerkle := h_holds.1 trivial
  have hGate := h_holds.2.2.2.2.2.2.2.2.2.2.2.2
  -- Var-projection bridges: the leaf / ak fed as `input.cmOld.x` / `input.akP.x`
  have hleaf : input_cmOld.x = Expression.eval env input_var.cmOld.x :=
    (congrArg Point.x h_input.2.2.2.2.2.2.1).symm
  have hakx : input_akP.x = Expression.eval env input_var.akP.x :=
    (congrArg Point.x h_input.2.2.2.2.2.2.2.2.1).symm
  dsimp only [IntermediateSpec]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hVCeq ▸ hVC                                  -- value commitment
  · exact hNFeq ▸ hNF                                  -- nullifier
  · exact hSAeq ▸ hSA                                  -- spend authority
  · rw [hakx]; exact hAI                               -- diversified address integrity
  · exact hNColdEq ▸ hNCold                            -- old note commitment
  · rw [← hNFeq]                                       -- new note commitment: bridge ρ = nf_old
    exact ⟨_, hNCnewEq ▸ hNCnew⟩
  · -- merkle root + q_orchard checks: reduce the gate record's projections, pin leaf/root
    -- via cheap Eqs, then discharge the calculated-root gadget Spec
    simp only [Orchard.Action.Gate.Spec] at hGate
    refine ⟨_, _, hleaf.symm, ?_, hGate.1, hGate.2.1, hGate.2.2.1, hGate.2.2.2⟩
    exact hMerkle
  · -- channel-requirements side goals: merkle's (trivial `True` Assumptions) and the
    -- nullifier-Poseidon's (discharged by `cm_old` validity)
    refine ⟨Or.inr ?_, Or.inr ?_⟩
    · trivial
    · exact h_assumptions.2.2.2.2.1

/-- Honest-prover preconditions: each composed gadget's `ProverAssumptions` instantiated at
the honest witnesses. -/
def ProverAssumptions (P : Params) (input : ProverValue Input Fp)
    (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  sorry

def IntermediateProverSpec (P : Params) (input : ProverValue Input Fp) (_ : Unit)
    (_ : ProverHint Fp) : Prop :=
  sorry

theorem intermediate_completeness (P : Params) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main P)
      (ProverAssumptions P) (IntermediateProverSpec P) := by
  sorry

def circuit (P : Params) : GeneralFormalCircuit.WithHint Fp Input unit where
  main := main P
  elaborated := elaborated P
  Assumptions
  Spec := IntermediateSpec P
  ProverAssumptions := ProverAssumptions P
  ProverSpec := IntermediateProverSpec P
  soundness := intermediate_spec_of_constraints P
  completeness := intermediate_completeness P

end Orchard.Action.Synthesis
