import Clean.Circuit
import Clean.Orchard.Ecc.MulFixed.FullWidth
import Clean.Orchard.Ecc.Add

/-!
# Orchard spend authority

Reference: `orchard@0.14.0/src/circuit.rs`, the `Spend authority` block in
`Circuit::synthesize`.

The source witnesses `alpha` as a full-width fixed scalar, computes
`alpha_commitment = [alpha] SpendAuthG`, discards the returned scalar decomposition, then
computes `rk = alpha_commitment + ak_P`. The final public-instance constraints on
`rk.x` and `rk.y` belong to the enclosing action synthesis circuit.
-/

namespace Orchard.Action.SpendAuthority

open Ecc
open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- Inputs of the spend-authority block: the already-assigned authorizing key point
`ak_P` and the prover-side randomizer `alpha` (the canonical natural representative of
the `Fq` scalar). -/
structure Input (F : Type) where
  akP : Point F
  alpha : UnconstrainedNat F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ akP := { x := default, y := default }, alpha := default }⟩

def main (SpendAuthG : MulFixed.FixedBase) (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  -- alpha_commitment = [alpha] SpendAuthG
  let alphaCommitment ← MulFixed.FullWidth.circuit SpendAuthG input.alpha
  -- rk = [alpha] SpendAuthG + ak_P
  Add.circuit { p := alphaCommitment, q := input.akP }

instance elaborated (SpendAuthG : MulFixed.FixedBase) :
    ElaboratedCircuit Fp Input Point (main SpendAuthG) := by
  elaborate_circuit

/-- `ak_P` is already assigned as a valid Pallas point before the spend-authority block. -/
def Assumptions (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  input.akP.Valid

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  input.akP.Valid ∧ (show ℕ from input.alpha) < PALLAS_SCALAR_CARD

/-- The spend validating key is randomized as `rk = [alpha] SpendAuthG + ak_P`. -/
def Spec (SpendAuthG : MulFixed.FixedBase) (input : Value Input Fp)
    (output : Point Fp) (_ : ProverData Fp) : Prop :=
  ∃ alpha : Fq,
    output = alpha • SpendAuthG + input.akP

def ProverSpec (SpendAuthG : MulFixed.FixedBase) (input : ProverValue Input Fp)
    (output : Point Fp) (_ : ProverHint Fp) : Prop :=
  output = ((show ℕ from input.alpha : ℕ) : Fq) • SpendAuthG + input.akP

theorem soundness (SpendAuthG : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main SpendAuthG) Assumptions
      (Spec SpendAuthG) := by
  circuit_proof_start [main, Assumptions, Spec,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.Spec,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_alpha, h_add⟩ := h_holds
  obtain ⟨alpha, h_alpha_commitment⟩ := h_alpha
  have h_final := h_add ⟨by
      rw [h_alpha_commitment]
      exact SpendAuthG.smul_valid alpha,
    h_assumptions⟩
  exact ⟨alpha, by
    rw [h_alpha_commitment] at h_final
    exact h_final.2⟩

theorem completeness (SpendAuthG : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main SpendAuthG) ProverAssumptions
      (ProverSpec SpendAuthG) := by
  circuit_proof_start [main, ProverAssumptions, ProverSpec,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.ProverAssumptions,
    MulFixed.FullWidth.ProverSpec,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_alpha_env, h_add_env⟩ := h_env
  obtain ⟨_, h_alpha_commitment⟩ := h_alpha_env h_assumptions.2
  have h_final := h_add_env ⟨by
      rw [h_alpha_commitment]
      exact SpendAuthG.smul_valid _,
    h_assumptions.1⟩
  exact ⟨⟨h_assumptions.2, by
      rw [h_alpha_commitment]
      exact SpendAuthG.smul_valid _,
    h_assumptions.1⟩, by
      rw [h_alpha_commitment] at h_final
      exact h_final.2⟩

def circuit (SpendAuthG : MulFixed.FixedBase) : GeneralFormalCircuit.WithHint Fp Input Point where
  main := main SpendAuthG
  elaborated := elaborated SpendAuthG
  Assumptions
  Spec := Spec SpendAuthG
  ProverAssumptions
  ProverSpec := ProverSpec SpendAuthG
  soundness := soundness SpendAuthG
  completeness := completeness SpendAuthG

end Orchard.Action.SpendAuthority
