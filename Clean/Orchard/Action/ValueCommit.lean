import Clean.Circuit
import Clean.Orchard.Ecc.MulFixed.FullWidth
import Clean.Orchard.Ecc.MulFixed.Short
import Clean.Orchard.Ecc.MulFixed.BaseFieldElem
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Poseidon.Hash
import Clean.Orchard.Utilities

/-!
# Orchard value commitment

Reference: `orchard/src/circuit/gadget.rs`.

`Action.ValueCommit.circuit` is `gadget.rs::value_commit_orchard`:
`cv = [v] ValueCommitV + [rcv] ValueCommitR`, where `v` is a signed 64-bit magnitude
multiplied by the short fixed base `ValueCommitV` and `rcv` is a full-width scalar
multiplied by the fixed base `ValueCommitR`.
-/

namespace Orchard.Action.ValueCommit

open Ecc
open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- The inputs of `value_commit_orchard`: the magnitude-sign pair behind the
`ScalarFixedShort` value `v` (already-assigned cells) and the prover-side full-width
scalar behind the `ScalarFixed` value `rcv` (the canonical natural representative of
the `Fq` scalar). -/
structure Input (F : Type) where
  v : MulFixed.Short.MagnitudeSign F
  rcv : UnconstrainedNat F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ v := { magnitude := default, sign := default }, rcv := default }⟩

def main (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase)
    (input : Var Input Fp) : Circuit Fp (Var Point Fp) := do
  -- commitment = [v] ValueCommitV
  let commitment ← MulFixed.Short.circuit V input.v
  -- blind = [rcv] ValueCommitR
  let blind ← MulFixed.FullWidth.circuit R input.rcv
  -- cv = [v] ValueCommitV + [rcv] ValueCommitR
  Add.circuit { p := commitment, q := blind }

instance elaborated (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase) :
    ElaboratedCircuit Fp Input Point (main V R) := by
  elaborate_circuit

def Spec (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase)
    (input : Value Input Fp) (output : Point Fp) (_ : ProverData Fp) : Prop :=
  ∃ (m : ℕ) (rcv : Fq), m < 2 ^ 64 ∧ input.v.magnitude = (m : Fp) ∧
    ((input.v.sign = 1 ∧
        output = (m : Fq) • V + rcv • R) ∨
      (input.v.sign = -1 ∧
        output = ((-(m : Fq)) : Fq) • V + rcv • R))

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  input.v.magnitude.val < 2 ^ 64 ∧ (input.v.sign = 1 ∨ input.v.sign = -1) ∧
    (show ℕ from input.rcv) < PALLAS_SCALAR_CARD

def ProverSpec (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (output : Point Fp) (_ : ProverHint Fp) : Prop :=
  (input.v.sign = 1 →
      output = (input.v.magnitude.val : Fq) • V
        + ((show ℕ from input.rcv : ℕ) : Fq) • R) ∧
    (input.v.sign = -1 →
      output = ((-(input.v.magnitude.val : Fq)) : Fq) • V
        + ((show ℕ from input.rcv : ℕ) : Fq) • R)

theorem soundness (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main V R) (fun _ _ => True)
      (Spec V R) := by
  circuit_proof_start [main, Spec,
    MulFixed.Short.circuit, MulFixed.Short.Spec,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.Spec,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_short, h_fw, h_add⟩ := h_holds
  obtain ⟨m, hm_lt, hmag, hcases⟩ := h_short
  obtain ⟨s, hblind⟩ := h_fw
  have h_final := h_add ⟨by
      rcases hcases with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> exact V.smul_valid _,
    by rw [hblind]; exact R.smul_valid s⟩
  refine ⟨m, s, hm_lt, hmag, ?_⟩
  rcases hcases with ⟨hsign, hC1⟩ | ⟨hsign, hC1⟩
  · rw [hC1, hblind] at h_final
    exact Or.inl ⟨hsign, by simpa using h_final.2⟩
  · rw [hC1, hblind] at h_final
    exact Or.inr ⟨hsign, by simpa using h_final.2⟩

theorem completeness (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main V R) ProverAssumptions
      (ProverSpec V R) := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions,
    MulFixed.Short.circuit, MulFixed.Short.ProverSpec, MulFixed.Short.ProverAssumptions,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.ProverAssumptions,
    MulFixed.FullWidth.ProverSpec,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_short_env, h_fw_env, h_add_env⟩ := h_env
  obtain ⟨hmag, hsign, hrcv⟩ := h_assumptions
  obtain ⟨_, hC1, hCneg⟩ := h_short_env ⟨hmag, hsign⟩
  obtain ⟨_, hblind⟩ := h_fw_env hrcv
  have h_final := h_add_env ⟨by
      rcases hsign with h | h
      · rw [hC1 h]
        exact V.smul_valid _
      · rw [hCneg h]
        exact V.smul_valid _,
    by rw [hblind]; exact R.smul_valid _⟩
  refine ⟨⟨⟨hmag, hsign⟩, hrcv, ?_, ?_⟩, ?_, ?_⟩
  · rcases hsign with h | h
    · rw [hC1 h]
      exact V.smul_valid _
    · rw [hCneg h]
      exact V.smul_valid _
  · rw [hblind]
    exact R.smul_valid _
  · intro hs
    rw [hC1 hs, hblind] at h_final
    simpa using h_final.2
  · intro hs
    rw [hCneg hs, hblind] at h_final
    simpa using h_final.2

def circuit (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint Fp Input Point where
  main := main V R
  elaborated := elaborated V R
  Spec := Spec V R
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec V R
  soundness := soundness V R
  completeness := completeness V R

end Orchard.Action.ValueCommit
