import Clean.Circuit
import Clean.Orchard.Ecc.ScalarMul.MulFixed.FullWidth
import Clean.Orchard.Ecc.ScalarMul.MulFixed.Short
import Clean.Orchard.Ecc.Add

/-!
# Orchard source gadget APIs

Reference: `orchard/src/circuit/gadget.rs`.

`ValueCommitOrchard.circuit` is `gadget.rs::value_commit_orchard`:
`cv = [v] ValueCommitV + [rcv] ValueCommitR`, where `v` is a signed 64-bit magnitude
multiplied by the short fixed base `ValueCommitV` and `rcv` is a full-width scalar
multiplied by the fixed base `ValueCommitR`.

TODO(source-conformance): `derive_nullifier` is not implemented.

The replacement should compose the Poseidon hash, nullifier fixed-base multiplication,
and complete addition internally, instead of taking the Poseidon result and scalar-mul
product as row inputs.

TODO(source-conformance): spend-authority key derivation is not implemented.

The replacement should witness `[alpha] SpendAuthG` internally and then compose complete
addition with `ak_P`, instead of taking the fixed-base product as a row input.
-/

namespace Orchard
namespace Gadget

open Ecc Ecc.ScalarMul
open CompElliptic.Curves.Pasta

namespace ValueCommitOrchard

/-- The inputs of `value_commit_orchard`: the magnitude-sign pair behind the
`ScalarFixedShort` value `v` (already-assigned cells) and the prover-side full-width
scalar behind the `ScalarFixed` value `rcv`. -/
structure Input (F : Type) where
  v : MulFixed.Short.MagnitudeSign F
  rcv : Unconstrained Fq F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ v := { magnitude := default, sign := default }, rcv := fun _ => default }⟩

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
        output.coords = Pallas.add (V.mulValue (m : Fq)).coords (R.mulValue rcv).coords) ∨
      (input.v.sign = -1 ∧
        output.coords
          = Pallas.add (V.mulValue (-(m : Fq))).coords (R.mulValue rcv).coords))

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  input.v.magnitude.val < 2 ^ 64 ∧ (input.v.sign = 1 ∨ input.v.sign = -1)

def ProverSpec (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase)
    (input : ProverValue Input Fp) (output : Point Fp) (_ : ProverHint Fp) : Prop :=
  (input.v.sign = 1 →
      output.coords = Pallas.add (V.mulValue (input.v.magnitude.val : Fq)).coords
        (R.mulValue input.rcv).coords) ∧
    (input.v.sign = -1 →
      output.coords = Pallas.add (V.mulValue (-(input.v.magnitude.val : Fq))).coords
        (R.mulValue input.rcv).coords)

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
      rcases hcases with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> exact V.mulValue_valid _,
    by rw [hblind]; exact R.mulValue_valid s⟩
  refine ⟨m, s, hm_lt, hmag, ?_⟩
  rcases hcases with ⟨hsign, hC1⟩ | ⟨hsign, hC1⟩
  · exact Or.inl ⟨hsign, by rw [h_final.2, hC1, hblind]⟩
  · exact Or.inr ⟨hsign, by rw [h_final.2, hC1, hblind]⟩

theorem completeness (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main V R) ProverAssumptions
      (ProverSpec V R) := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions,
    MulFixed.Short.circuit, MulFixed.Short.ProverSpec, MulFixed.Short.ProverAssumptions,
    MulFixed.FullWidth.circuit, MulFixed.FullWidth.ProverSpec,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_short_env, h_fw_env, h_add_env⟩ := h_env
  obtain ⟨_, hC1, hCneg⟩ := h_short_env h_assumptions
  obtain ⟨_, hblind⟩ := h_fw_env
  have h_final := h_add_env ⟨by
      rcases h_assumptions.2 with h | h
      · rw [hC1 h]
        exact V.mulValue_valid _
      · rw [hCneg h]
        exact V.mulValue_valid _,
    by rw [hblind]; exact R.mulValue_valid _⟩
  refine ⟨⟨h_assumptions, ?_, ?_⟩, ?_, ?_⟩
  · rcases h_assumptions.2 with h | h
    · rw [hC1 h]
      exact V.mulValue_valid _
    · rw [hCneg h]
      exact V.mulValue_valid _
  · rw [hblind]
    exact R.mulValue_valid _
  · intro hs
    rw [h_final.2, hC1 hs, hblind]
  · intro hs
    rw [h_final.2, hCneg hs, hblind]

def circuit (V : MulFixed.Short.FixedBase) (R : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint Fp Input Point where
  main := main V R
  Spec := Spec V R
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec V R
  soundness := soundness V R
  completeness := completeness V R

end ValueCommitOrchard

end Gadget
end Orchard
