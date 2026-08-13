import Clean.Halo2.TopLevel
import Clean.Ironwood.Action.Bundle

/-!
# Orchard Action public and private inputs

This module declares the Action circuit's public instance-cell layout and splits its
semantic witness into the public values supplied to the verifier and the remaining
private witness.
-/

namespace Zcash.Circuits.Action

open Halo2
open Circuit

/-- The ten field elements in one Orchard Action instance column, in row order. -/
structure PublicInputs (F : Type) where
  anchor : F
  cvX : F
  cvY : F
  nfOld : F
  rkX : F
  rkY : F
  cmx : F
  enableSpend : F
  enableOutput : F
  disableCrossAddress : F

instance : ProvableType PublicInputs where
  size := 10
  toElements inputs :=
    #v[inputs.anchor, inputs.cvX, inputs.cvY, inputs.nfOld, inputs.rkX,
      inputs.rkY, inputs.cmx, inputs.enableSpend, inputs.enableOutput,
      inputs.disableCrossAddress]
  fromElements elements := {
    anchor := elements[0]
    cvX := elements[1]
    cvY := elements[2]
    nfOld := elements[3]
    rkX := elements[4]
    rkY := elements[5]
    cmx := elements[6]
    enableSpend := elements[7]
    enableOutput := elements[8]
    disableCrossAddress := elements[9]
  }
  toElements_fromElements elements := by
    rw [Vector.ext_iff]
    intro i hi
    interval_cases i <;> rfl
  fromElements_toElements inputs := by
    cases inputs
    rfl

namespace PublicInputs

@[ext] theorem ext
    {F : Type} {left right : PublicInputs F}
    (anchor : left.anchor = right.anchor)
    (cvX : left.cvX = right.cvX)
    (cvY : left.cvY = right.cvY)
    (nfOld : left.nfOld = right.nfOld)
    (rkX : left.rkX = right.rkX)
    (rkY : left.rkY = right.rkY)
    (cmx : left.cmx = right.cmx)
    (enableSpend : left.enableSpend = right.enableSpend)
    (enableOutput : left.enableOutput = right.enableOutput)
    (disableCrossAddress :
      left.disableCrossAddress = right.disableCrossAddress) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The Action circuit's public input occupies rows 0 through 9 of `primary`. -/
def layout : PublicInputLayout PublicInputs [⟨0⟩] where
  columnSizes := #v[10]
  size_eq := rfl

/-- Project the public part of the circuit's extracted semantic witness. -/
def ofActionData (data : ActionData) : PublicInputs Fp where
  anchor := data.anchor
  cvX := data.cvX
  cvY := data.cvY
  nfOld := data.nfOld
  rkX := data.rkX
  rkY := data.rkY
  cmx := data.cmx
  enableSpend := data.enableSpend
  enableOutput := data.enableOutput
  disableCrossAddress := data.disableCrossAddress

theorem ofActionData_extractPost
    (cfg : Config) (i : RegionIndex) (env : Placed Environment Fp)
    (hprimary :
      cfg.primary = (layout.cells ⟨0, by decide⟩).1) :
    ofActionData (extractPost cfg () i env) = layout.extract env.env := by
  apply PublicInputs.ext <;>
    simp [ofActionData, layout, PublicInputLayout.extract,
      ProvableType.fromElements, hprimary] <;>
    rw [Environment.get_inst] <;>
    rfl

end PublicInputs

/-- The non-public portion of `ActionData`. -/
structure PrivateWitness where
  psiOld : Fp
  rhoOld : Fp
  nk : Fp
  vOld : Fp
  vNew : Fp
  psiNew : Fp
  magnitude : Fp
  sign : Fp
  cmOld : Point Fp
  gdOld : Point Fp
  akP : Point Fp
  pkdOld : Point Fp
  gdNew : Point Fp
  pkdNew : Point Fp
  leftEncoding : Fin 32 → ℕ
  rightEncoding : Fin 32 → ℕ
  merkleSide : Fin 32 → Bool
  merklePath : ℕ → Fp × Fp
  rcv : Vector Fp 85 × Fq
  alpha : Vector Fp 85 × Fq
  rivk : Vector Fp 85 × Fq
  rcmOld : Vector Fp 85 × Fq
  rcmNew : Vector Fp 85 × Fq

namespace PrivateWitness

/-- Project the private part of the circuit's extracted semantic witness. -/
def ofActionData (data : ActionData) : PrivateWitness where
  psiOld := data.psiOld
  rhoOld := data.rhoOld
  nk := data.nk
  vOld := data.vOld
  vNew := data.vNew
  psiNew := data.psiNew
  magnitude := data.magnitude
  sign := data.sign
  cmOld := data.cmOld
  gdOld := data.gdOld
  akP := data.akP
  pkdOld := data.pkdOld
  gdNew := data.gdNew
  pkdNew := data.pkdNew
  leftEncoding := data.leftEncoding
  rightEncoding := data.rightEncoding
  merkleSide := data.merkleSide
  merklePath := data.merklePath
  rcv := data.rcv
  alpha := data.alpha
  rivk := data.rivk
  rcmOld := data.rcmOld
  rcmNew := data.rcmNew

end PrivateWitness

/-- Reassemble the formal circuit witness from its public and private parts. -/
def combine (inputs : PublicInputs Fp) (privateWitness : PrivateWitness) :
    ActionData where
  anchor := inputs.anchor
  cvX := inputs.cvX
  cvY := inputs.cvY
  nfOld := inputs.nfOld
  rkX := inputs.rkX
  rkY := inputs.rkY
  cmx := inputs.cmx
  enableSpend := inputs.enableSpend
  enableOutput := inputs.enableOutput
  disableCrossAddress := inputs.disableCrossAddress
  psiOld := privateWitness.psiOld
  rhoOld := privateWitness.rhoOld
  nk := privateWitness.nk
  vOld := privateWitness.vOld
  vNew := privateWitness.vNew
  psiNew := privateWitness.psiNew
  magnitude := privateWitness.magnitude
  sign := privateWitness.sign
  cmOld := privateWitness.cmOld
  gdOld := privateWitness.gdOld
  akP := privateWitness.akP
  pkdOld := privateWitness.pkdOld
  gdNew := privateWitness.gdNew
  pkdNew := privateWitness.pkdNew
  leftEncoding := privateWitness.leftEncoding
  rightEncoding := privateWitness.rightEncoding
  merkleSide := privateWitness.merkleSide
  merklePath := privateWitness.merklePath
  rcv := privateWitness.rcv
  alpha := privateWitness.alpha
  rivk := privateWitness.rivk
  rcmOld := privateWitness.rcmOld
  rcmNew := privateWitness.rcmNew

@[simp] theorem combine_parts (data : ActionData) :
    combine (PublicInputs.ofActionData data) (PrivateWitness.ofActionData data) =
      data := by
  cases data
  rfl

end Zcash.Circuits.Action
