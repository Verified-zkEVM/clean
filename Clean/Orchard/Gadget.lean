import Clean.Circuit
import Clean.Orchard.Ecc.ScalarMul.MulFixed.FullWidth
import Clean.Orchard.Ecc.ScalarMul.MulFixed.Short
import Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Poseidon.Hash
import Clean.Orchard.Utilities

/-!
# Orchard source gadget APIs

Reference: `orchard/src/circuit/gadget.rs`.

`ValueCommitOrchard.circuit` is `gadget.rs::value_commit_orchard`:
`cv = [v] ValueCommitV + [rcv] ValueCommitR`, where `v` is a signed 64-bit magnitude
multiplied by the short fixed base `ValueCommitV` and `rcv` is a full-width scalar
multiplied by the fixed base `ValueCommitR`.

`DeriveNullifier.circuit` is `gadget.rs::derive_nullifier`:
`nf = extract_p(cm + [poseidon_hash(nk, rho) + psi] NullifierK)`, composing the Poseidon
hash, the base-field-element fixed-base multiplication by `NullifierK`, and the complete
addition with `cm`.
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

namespace DeriveNullifier

/-- The inputs of `derive_nullifier`: the already-assigned cells `nk`, `rho`, `psi`, and
the note commitment point `cm`. -/
structure Input (F : Type) where
  nk : F
  rho : F
  psi : F
  cm : Point F
deriving ProvableStruct

instance : Inhabited (Var Input Fp) :=
  ⟨{ nk := default, rho := default, psi := default, cm := { x := default, y := default } }⟩

def main (K : MulFixed.FixedBase) (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  -- hash = poseidon_hash(nk, rho)
  let hash ← Poseidon.Hash.ConstantLength.circuit 2 #v[input.nk, input.rho]
  -- scalar = poseidon_hash(nk, rho) + psi
  let scalar ← Utilities.AddChip.circuit (hash, input.psi)
  -- product = [scalar] NullifierK
  let product ← MulFixed.BaseFieldElem.circuit K scalar
  -- nf = cm + product; the nullifier is its extracted x-coordinate
  let nf ← Add.circuit { p := input.cm, q := product }
  return nf.x

instance elaborated (K : MulFixed.FixedBase) :
    ElaboratedCircuit Fp Input field (main K) := by
  elaborate_circuit

/-- `cm` is an already-assigned valid point. -/
def Assumptions (input : Input Fp) : Prop :=
  Pallas.Valid input.cm.coords

/-- The nullifier `nf = extract_p(cm + [poseidon_hash(nk, rho) + psi] NullifierK)`: the
`x`-coordinate of the complete sum of `cm` with the base-field-element fixed-base product. -/
def Spec (K : MulFixed.FixedBase) (input : Input Fp) (output : Fp) : Prop :=
  output = (Pallas.add input.cm.coords
    (K.mulValue ((Poseidon.Hash.ConstantLength.value #v[input.nk, input.rho]
      + input.psi).val : Fq)).coords).1

theorem soundness (K : MulFixed.FixedBase) :
    Soundness Fp (main K) Assumptions (Spec K) := by
  circuit_proof_start [main, Spec, Assumptions,
    Poseidon.Hash.ConstantLength.circuit, Poseidon.Hash.ConstantLength.Spec,
    Utilities.AddChip.circuit, Utilities.AddChip.Spec,
    MulFixed.BaseFieldElem.circuit, MulFixed.BaseFieldElem.Spec,
    MulFixed.BaseFieldElem.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_hash, h_scalar, h_bfe, h_complete⟩ := h_holds
  have h_nf := (h_complete ⟨h_assumptions, by rw [h_bfe]; exact K.mulValue_valid _⟩).2
  rw [h_bfe, h_scalar, h_hash] at h_nf
  exact congrArg Prod.fst h_nf

theorem completeness (K : MulFixed.FixedBase) :
    Completeness Fp (main K) Assumptions := by
  circuit_proof_start [main, Assumptions,
    Poseidon.Hash.ConstantLength.circuit, Poseidon.Hash.ConstantLength.Spec,
    Utilities.AddChip.circuit, Utilities.AddChip.Spec,
    MulFixed.BaseFieldElem.circuit, MulFixed.BaseFieldElem.Spec,
    MulFixed.BaseFieldElem.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_hash_env, h_scalar_env, h_bfe_env, -⟩ := h_env
  exact ⟨h_assumptions, h_bfe_env ▸ K.mulValue_valid _⟩

def circuit (K : MulFixed.FixedBase) : FormalCircuit Fp Input field where
  main := main K
  Assumptions := Assumptions
  Spec := Spec K
  soundness := soundness K
  completeness := completeness K

end DeriveNullifier

end Gadget
end Orchard
