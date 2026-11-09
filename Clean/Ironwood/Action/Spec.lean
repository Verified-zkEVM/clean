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
def ActionSpec (input : PublicInputs Fp) (wit : PrivateWitness) : Prop :=
  -- the witnessed points are well-formed
  wit.cmOld.Valid ∧ wit.gdOld.OnCurve ∧
  wit.akP.OnCurve ∧ wit.pkdOld.OnCurve ∧
  wit.gdNew.OnCurve ∧ wit.pkdNew.OnCurve ∧
  -- the note values are 64-bit
  wit.vOld.val < 2 ^ 64 ∧ wit.vNew.val < 2 ^ 64 ∧
  -- value-commitment integrity: `cv_net = (v_old − v_new) • V + rcv • R`
  (wit.magnitude.val < 2 ^ 64 ∧
    ((wit.sign = 1 ∧ (⟨input.cvX, input.cvY⟩ : Point Fp)
        = (wit.magnitude.val : Fq) • orchardBases.valueCommitV
          + wit.rcv.2 • orchardBases.valueCommitR) ∨
     (wit.sign = -1 ∧ (⟨input.cvX, input.cvY⟩ : Point Fp)
        = -(wit.magnitude.val : Fq) • orchardBases.valueCommitV
          + wit.rcv.2 • orchardBases.valueCommitR))) ∧
  -- nullifier integrity: `nf_old = Extract((PRF(nk, ρ) + ψ) • K + cm_old)`
  input.nfOld = (wit.cmOld +
    ((Poseidon.Hash.ConstantLength.value
      #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq)
      • orchardBases.nullifierK).x ∧
  -- spend authority: `rk = α • SpendAuthG + ak_P`
  (⟨input.rkX, input.rkY⟩ : Point Fp)
    = wit.alpha.2 • orchardBases.spendAuthG + wit.akP ∧
  -- diversified-address integrity
  (∃ ivk : Fp,
    HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks wit.akP.x.val wit.nk.val)
      (fun bp => ivk =
        (bp + wit.rivk.2 • orchardBases.commitIvkR).x) ∧
    wit.pkdOld = ivk.val • wit.gdOld) ∧
  -- old note-commitment integrity
  HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.noteQ
    (noteScalars wit.gdOld wit.pkdOld wit.vOld
      wit.rhoOld wit.psiOld).chunks
    (fun bp => wit.cmOld =
      bp + wit.rcmOld.2 • orchardBases.noteCommitR) ∧
  -- new note-commitment integrity, with `ρ_new = nf_old`
  HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.noteQ
    (noteScalars wit.gdNew wit.pkdNew wit.vNew
      input.nfOld wit.psiNew).chunks
    (fun bp => input.cmx =
      (bp + wit.rcmNew.2 • orchardBases.noteCommitR).x) ∧
  -- exact raw-encoding Merkle path and dummy-spend anchor gate
  (∃ root : Fp,
    Sinsemilla.Merkle.ExactMerklePathData Specs.Sinsemilla.orchardGenerators
      orchardBases.merkleQ 0 32 wit.cmOld.x root
      (fun i => if h : i < 32 then wit.leftEncoding ⟨i, h⟩ else 0)
      (fun i => if h : i < 32 then wit.rightEncoding ⟨i, h⟩ else 0)
      (fun i => if h : i < 32 then wit.merkleSide ⟨i, h⟩ else false) ∧
    wit.vOld * (root - input.anchor) = 0) ∧
  -- remaining `q_orchard` value checks
  wit.vOld - wit.vNew =
    wit.magnitude * wit.sign ∧
  wit.vOld * (1 - input.enableSpend) = 0 ∧
  wit.vNew * (1 - input.enableOutput) = 0 ∧
  -- post-NU6.3 cross-address binding
  (input.disableCrossAddress ≠ 0 →
    wit.gdOld = wit.gdNew ∧
      wit.pkdOld = wit.pkdNew)

/-- The canonical Action specification is the concrete instantiation of the
formal circuit bundle's parameterized postcondition. -/
theorem actionSpec_iff_specPost
    (input : PublicInputs Fp) (wit : PrivateWitness) :
    ActionSpec input wit ↔
      SpecPost Specs.Sinsemilla.orchardGenerators orchardBases
        () () (combine input wit) := by
  have leftEncoding : merkleLeftEncoding (combine input wit) =
      fun i => if h : i < 32 then wit.leftEncoding ⟨i, h⟩ else 0 := by
    funext i
    simp only [merkleLeftEncoding, combine]
  have rightEncoding : merkleRightEncoding (combine input wit) =
      fun i => if h : i < 32 then wit.rightEncoding ⟨i, h⟩ else 0 := by
    funext i
    simp only [merkleRightEncoding, combine]
  have sides : merkleSide (combine input wit) =
      fun i => if h : i < 32 then wit.merkleSide ⟨i, h⟩ else false := by
    funext i
    simp only [merkleSide, combine]
  rw [SpecPost, SpecBase, leftEncoding, rightEncoding, sides]
  simp only [ActionSpec, combine, and_assoc]

/-- Projecting an extracted Action into public and private parts preserves its
formal circuit postcondition. -/
theorem actionSpec_ofActionData_iff_specPost (data : ActionData) :
    ActionSpec (.ofActionData data) (.ofActionData data) ↔
      SpecPost Specs.Sinsemilla.orchardGenerators orchardBases () () data := by
  rw [actionSpec_iff_specPost, combine_parts]

end Zcash.Circuits.Action
