import Clean.Ironwood.Action.PublicInput
import Clean.Ironwood.Action.RealBases

/-!
# The Orchard Action specification

This is the canonical, circuit-independent statement over the Action's public input
and private witness.
The formal-circuit bundle retains its parameterized `Circuit.SpecPost`; the theorem
at the end of this file is the explicit boundary between that implementation
spelling and the deployed Action specification.
-/

namespace Zcash.Circuits.Action

open Circuit
open NoteCommit (noteScalars)
open Specs.Sinsemilla (HashGuarded commitIvkChunks)
open CompElliptic.Fields.Pasta (Fq)

/-- The deployed Orchard Action statement over its public input and private witness. -/
def ActionSpec (input : PublicInputs Fp) (privateWitness : PrivateWitness) : Prop :=
  -- the witnessed points are well-formed
  privateWitness.cmOld.Valid ∧ privateWitness.gdOld.OnCurve ∧
  privateWitness.akP.OnCurve ∧ privateWitness.pkdOld.OnCurve ∧
  privateWitness.gdNew.OnCurve ∧ privateWitness.pkdNew.OnCurve ∧
  -- the note values are 64-bit
  privateWitness.vOld.val < 2 ^ 64 ∧ privateWitness.vNew.val < 2 ^ 64 ∧
  -- value-commitment integrity: `cv_net = [v_old − v_new] V + [rcv] R`
  (privateWitness.magnitude.val < 2 ^ 64 ∧
    ((privateWitness.sign = 1 ∧ (⟨input.cvX, input.cvY⟩ : Point Fp)
        = (privateWitness.magnitude.val : Fq) • orchardBases.valueCommitV
          + privateWitness.rcv.2 • orchardBases.valueCommitR) ∨
     (privateWitness.sign = -1 ∧ (⟨input.cvX, input.cvY⟩ : Point Fp)
        = -(privateWitness.magnitude.val : Fq) • orchardBases.valueCommitV
          + privateWitness.rcv.2 • orchardBases.valueCommitR))) ∧
  -- nullifier integrity: `nf_old = Extract([PRF(nk, ρ) + ψ] K + cm_old)`
  input.nfOld = (privateWitness.cmOld +
    ((Poseidon.Hash.ConstantLength.value
      #v[privateWitness.nk, privateWitness.rhoOld] + privateWitness.psiOld).val : Fq)
      • orchardBases.nullifierK).x ∧
  -- spend authority: `rk = [α] SpendAuthG + ak_P`
  (⟨input.rkX, input.rkY⟩ : Point Fp)
    = privateWitness.alpha.2 • orchardBases.spendAuthG + privateWitness.akP ∧
  -- diversified-address integrity
  (∃ ivk : Fp,
    HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks privateWitness.akP.x.val privateWitness.nk.val)
      (fun bp => ivk =
        (bp + privateWitness.rivk.2 • orchardBases.commitIvkR).x) ∧
    privateWitness.pkdOld = ivk.val • privateWitness.gdOld) ∧
  -- old note-commitment integrity
  HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.noteQ
    (noteScalars privateWitness.gdOld privateWitness.pkdOld privateWitness.vOld
      privateWitness.rhoOld privateWitness.psiOld).chunks
    (fun bp => privateWitness.cmOld =
      bp + privateWitness.rcmOld.2 • orchardBases.noteCommitR) ∧
  -- new note-commitment integrity, with `ρ_new = nf_old`
  HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.noteQ
    (noteScalars privateWitness.gdNew privateWitness.pkdNew privateWitness.vNew
      input.nfOld privateWitness.psiNew).chunks
    (fun bp => input.cmx =
      (bp + privateWitness.rcmNew.2 • orchardBases.noteCommitR).x) ∧
  -- exact raw-encoding Merkle path and dummy-spend anchor gate
  (∃ root : Fp,
    Sinsemilla.Merkle.ExactMerklePathData Specs.Sinsemilla.orchardGenerators
      orchardBases.merkleQ 0 32 privateWitness.cmOld.x root
      (fun i => if h : i < 32 then privateWitness.leftEncoding ⟨i, h⟩ else 0)
      (fun i => if h : i < 32 then privateWitness.rightEncoding ⟨i, h⟩ else 0)
      (fun i => if h : i < 32 then privateWitness.merkleSide ⟨i, h⟩ else false) ∧
    privateWitness.vOld * (root - input.anchor) = 0) ∧
  -- remaining `q_orchard` value checks
  privateWitness.vOld - privateWitness.vNew =
    privateWitness.magnitude * privateWitness.sign ∧
  privateWitness.vOld * (1 - input.enableSpend) = 0 ∧
  privateWitness.vNew * (1 - input.enableOutput) = 0 ∧
  -- post-NU6.3 cross-address binding
  (input.disableCrossAddress ≠ 0 →
    privateWitness.gdOld = privateWitness.gdNew ∧
      privateWitness.pkdOld = privateWitness.pkdNew)

/-- The canonical Action specification is the concrete instantiation of the
formal circuit bundle's parameterized postcondition. -/
theorem actionSpec_iff_specPost
    (input : PublicInputs Fp) (privateWitness : PrivateWitness) :
    ActionSpec input privateWitness ↔
      SpecPost Specs.Sinsemilla.orchardGenerators orchardBases
        () () (combine input privateWitness) := by
  have leftEncoding : merkleLeftEncoding (combine input privateWitness) =
      fun i => if h : i < 32 then privateWitness.leftEncoding ⟨i, h⟩ else 0 := by
    funext i
    simp only [merkleLeftEncoding, combine]
  have rightEncoding : merkleRightEncoding (combine input privateWitness) =
      fun i => if h : i < 32 then privateWitness.rightEncoding ⟨i, h⟩ else 0 := by
    funext i
    simp only [merkleRightEncoding, combine]
  have sides : merkleSide (combine input privateWitness) =
      fun i => if h : i < 32 then privateWitness.merkleSide ⟨i, h⟩ else false := by
    funext i
    simp only [merkleSide, combine]
  rw [SpecPost, SpecBase, leftEncoding, rightEncoding, sides]
  simp only [ActionSpec, combine, and_assoc]

/-- Projecting an extracted Action into public and private parts preserves its
formal circuit postcondition. -/
theorem actionSpec_ofActionData_iff_specPost (data : ActionData) :
    ActionSpec (PublicInputs.ofActionData data) (PrivateWitness.ofActionData data) ↔
      SpecPost Specs.Sinsemilla.orchardGenerators orchardBases () () data := by
  rw [actionSpec_iff_specPost, combine_parts]

end Zcash.Circuits.Action
