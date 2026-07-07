import Clean.Circuit
import Clean.Orchard.Ecc.MulFixed.FullWidth
import Clean.Orchard.Ecc.MulFixed.Short
import Clean.Orchard.Ecc.MulFixed.BaseFieldElem
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Poseidon.Hash
import Clean.Orchard.Utilities

/-!
# Orchard nullifier derivation

Reference: `orchard/src/circuit/gadget.rs`.

`Action.DeriveNullifier.circuit` is `gadget.rs::derive_nullifier`:
`nf = extract_p(cm + [poseidon_hash(nk, rho) + psi] NullifierK)`, composing the Poseidon
hash, the base-field-element fixed-base multiplication by `NullifierK`, and the complete
addition with `cm`.
-/

namespace Orchard.Action.DeriveNullifier

open Ecc
open CompElliptic.Curves.Pasta

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
  input.cm.Valid

/-- The nullifier `nf = extract_p(cm + [poseidon_hash(nk, rho) + psi] NullifierK)`: the
`x`-coordinate of the complete sum of `cm` with the base-field-element fixed-base product. -/
def Spec (K : MulFixed.FixedBase) (input : Input Fp) (output : Fp) : Prop :=
  output = (input.cm +
    ((Poseidon.Hash.ConstantLength.value #v[input.nk, input.rho] + input.psi).val : Fq) • K).x

theorem soundness (K : MulFixed.FixedBase) :
    Soundness Fp (main K) Assumptions (Spec K) := by
  circuit_proof_start [main, Spec, Assumptions,
    Poseidon.Hash.ConstantLength.circuit, Poseidon.Hash.ConstantLength.Spec,
    Utilities.AddChip.circuit, Utilities.AddChip.Spec,
    MulFixed.BaseFieldElem.circuit, MulFixed.BaseFieldElem.Spec,
    MulFixed.BaseFieldElem.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_hash, h_scalar, h_bfe, h_complete⟩ := h_holds
  have h_nf := (h_complete ⟨h_assumptions, by rw [h_bfe]; exact K.smul_valid _⟩).2
  rw [h_bfe, h_scalar, h_hash] at h_nf
  exact congrArg Point.x h_nf

theorem completeness (K : MulFixed.FixedBase) :
    Completeness Fp (main K) Assumptions := by
  circuit_proof_start [main, Assumptions,
    Poseidon.Hash.ConstantLength.circuit, Poseidon.Hash.ConstantLength.Spec,
    Utilities.AddChip.circuit, Utilities.AddChip.Spec,
    MulFixed.BaseFieldElem.circuit, MulFixed.BaseFieldElem.Spec,
    MulFixed.BaseFieldElem.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_hash_env, h_scalar_env, h_bfe_env, -⟩ := h_env
  exact ⟨h_assumptions, h_bfe_env ▸ K.smul_valid _⟩

def circuit (K : MulFixed.FixedBase) : FormalCircuit Fp Input field where
  main := main K
  elaborated := elaborated K
  Assumptions
  Spec := Spec K
  soundness := soundness K
  completeness := completeness K

end Orchard.Action.DeriveNullifier
