import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem
import Clean.Ironwood.Poseidon.Hash
import Clean.Ironwood.Utilities.AddChip

/-!
# Orchard nullifier derivation (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/gadget.rs::derive_nullifier` (lines 154-206):
`nf = extract_p(cm + [poseidon_hash(nk, rho) + psi] NullifierK)` — four layouter pieces
in source order:
1. `PoseidonHash::init` + `hash([nk, rho])` (`ConstantLength<2>` on the Pow5 chip; the
   Ironwood `Poseidon.hash` bundle at capacity `2·2⁶⁴`);
2. `add_chip.add(hash, psi)` (region `"c = a + b"`, `add_chip.rs:71-91`);
3. `FixedPointBaseField::from_inner(NullifierK).mul(scalar)` (the
   `Ecc.MulFixed.BaseFieldElem` bundle);
4. `cm.add(product)` (region `"complete point addition"`, `ecc/chip.rs:582-595`); the
   returned nullifier is `.extract_p()` — the x-coordinate.

Phase-1 donor: `Clean/Orchard/Action/DeriveNullifier.lean`.
-/

namespace Zcash.Circuits.Action.DeriveNullifier

open Halo2
open Ecc.MulFixed (FixedBase)
open Poseidon
open Poseidon.Permute.P128Pow5T3 (roundConstants)

/-- The inputs of `derive_nullifier`: the already-assigned cells `nk`, `rho`, `psi`, and
the note commitment point `cm`. -/
structure Input (F : Type) where
  nk : F
  rho : F
  psi : F
  cm : Point F
deriving ProvableStruct

/-- The `ConstantLength<2>` hash value is the one-padded-block hash at capacity `2·2⁶⁴`:
the message is exactly one rate-2 block, so the donor scheduler's fold is a single
absorb/permute step — the value-level bridge onto the Ironwood `Poseidon.hash` bundle's
`HashPaddedBlock` contract. -/
theorem constantLength_value_two (a b : Fp) :
    Hash.ConstantLength.value #v[a, b]
      = Hash.HashPaddedBlock.value roundConstants (Hash.ConstantLength.capacity 2)
          { x0 := a, x1 := b } := by
  simp [Hash.ConstantLength.value, Hash.HashPaddedBlock.value,
    Hash.ConstantLength.blockCount, Hash.ConstantLength.stepValueAt,
    Hash.ConstantLength.absorbPermuteValue, Permute.concreteValue,
    Hash.ConstantLength.blockValue, Hash.ConstantLength.paddedWord,
    Fin.foldl_succ, Fin.foldl_zero]

/-! ## Region counts -/

/-- The region count of `derive_nullifier`: the Poseidon child's three regions, the
add-chip region, the fixed-base mul's four regions, the final complete addition. -/
private theorem deriveNullifier_regionCount (K : FixedBase)
    (pcfg : Poseidon.Config) (acfg : AddChip.Config)
    (bcfg : Ecc.MulFixed.BaseFieldElem.Config) (ecfg : Ecc.Add.Config)
    (input : Var Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let hash ← (Poseidon.hash (Hash.ConstantLength.capacity 2)).call pcfg
          { x0 := input.nk, x1 := input.rho }
        let scalar ← AddChip.addFormal.call acfg
          { a := hash, b := input.psi }
        let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg scalar
        let nf ← Ecc.Add.addFormal.call ecfg
          { p := input.cm, q := product }
        pure nf.x : Circuit Fp (Var field Fp)).operations i)
      = 9 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    FormalCircuit.call_regionCount]
  rfl

/-! ## The `derive_nullifier` bundle -/

@[keygen_norm]
def keygenRequirements (K : FixedBase) : KeygenRequirements Fp
    (Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config) where
  configLawful cfg :=
    (Poseidon.hash (Hash.ConstantLength.capacity 2)).Configured cfg.1 ×
      AddChip.addFormal.Configured cfg.2.1 ×
        (Ecc.MulFixed.BaseFieldElem.circuit K).Configured cfg.2.2.1 ×
          Ecc.Add.addFormal.Configured cfg.2.2.2
  gates _ configured :=
    configured.1.gates ++ configured.2.1.gates ++
      configured.2.2.1.gates ++ configured.2.2.2.gates
  lookups _ configured :=
    configured.1.lookups ++ configured.2.1.lookups ++
      configured.2.2.1.lookups ++ configured.2.2.2.lookups

/-- Rust `gadget.rs::derive_nullifier`: the Poseidon hash of `(nk, rho)`, the add-chip
sum with `psi`, the `[scalar] NullifierK` base-field-element fixed-base mul, and the
complete addition with `cm`. `Spec` is the donor contract: the nullifier is
`extract_p(cm + [poseidon_hash(nk, rho) + psi] NullifierK)` — the x-coordinate of the
complete sum. -/
def circuit (K : FixedBase) : FormalCircuit Fp
    (Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config)
    (Poseidon.Config × AddChip.Config × Ecc.MulFixed.BaseFieldElem.Config ×
      Ecc.Add.Config)
    Input field where
  name := "derive nullifier"
  configure := pure

  synthesize := fun (pcfg, acfg, bcfg, ecfg) input => do
    let hash ← (Poseidon.hash (Hash.ConstantLength.capacity 2)).call pcfg
      { x0 := input.nk, x1 := input.rho }
    let scalar ← AddChip.addFormal.call acfg
      { a := hash, b := input.psi }
    let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg scalar
    let nf ← Ecc.Add.addFormal.call ecfg
      { p := input.cm, q := product }
    pure nf.x

  elaborated :=
    { keygenRequirements := keygenRequirements K
      registered := by keygen_registration
      output cfg input i :=
        let (pcfg, acfg, bcfg, ecfg) := cfg
        ((do
          let hash ← (Poseidon.hash (Hash.ConstantLength.capacity 2)).call pcfg
            { x0 := input.nk, x1 := input.rho }
          let scalar ← AddChip.addFormal.call acfg
            { a := hash, b := input.psi }
          let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg scalar
          let nf ← Ecc.Add.addFormal.call ecfg
            { p := input.cm, q := product }
          pure nf.x : Circuit Fp (Var field Fp)).output i)
      regionCount _ := 9
      output_eq := by intro _ _ _; rfl
      regionCount_eq := fun (pcfg, acfg, bcfg, ecfg) input i =>
        (deriveNullifier_regionCount K pcfg acfg bcfg ecfg input i).symm }

  EnvAssumptions := fun (_, _, bcfg, _) env =>
    Ecc.MulFixed.BaseFieldElem.EnvAssumptions bcfg env

  -- `cm` is an already-assigned valid point
  Assumptions input := input.cm.Valid

  Spec input output _ :=
    output = ((input.cm +
      ((Hash.ConstantLength.value #v[input.nk, input.rho] + input.psi).val : Fq) • K
      : Point Fp)).x

  soundness := by
    circuit_proof_start
    obtain ⟨hHash, hScalar, hBfe, hAdd⟩ := hc
    -- the Poseidon child: the output cell is the one-block hash of `(nk, rho)`
    have hH := hHash trivial trivial
    rw [Poseidon.hash_spec_eq] at hH
    -- the add-chip child: the scalar cell is `hash + psi`
    have hS := hScalar trivial trivial
    rw [AddChip.addFormal_spec_eq] at hS
    -- the fixed-base mul child: the product is `[scalar] K`
    have hB := hBfe (by rw [Ecc.MulFixed.BaseFieldElem.circuit_envAssumptions_eq]; exact _hE)
      (by rw [Ecc.MulFixed.BaseFieldElem.circuit_assumptions_eq]; trivial)
    rw [Ecc.MulFixed.BaseFieldElem.circuit_spec_eq] at hB
    simp only [Ecc.MulFixed.BaseFieldElem.Spec] at hB
    -- the complete addition: `nf = cm + product` (both summands valid)
    have hAddS := hAdd trivial (by
      rw [Ecc.Add.addFormal_assumptions_eq]
      exact ⟨hA, by rw [hB]; exact K.smul_valid _⟩)
    rw [Ecc.Add.addFormal_spec_eq] at hAddS
    have hSum : (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_3
        : Value Point Fp)
        = ({ x := input_cm_x, y := input_cm_y } : Point Fp)
          + (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_2
            : Value Point Fp) := hAddS.2
    rw [← h_output]
    rw [show AssignedCell.eval place env x_gen_out_3.x
      = (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_3
          : Value Point Fp).x from by simp only [Point.eval_eq, circuit_norm]]
    rw [hSum, hB, hS, hH, constantLength_value_two]

  completeness := by
    circuit_proof_start
    -- the fixed-base mul child's honest contract: the product is `[scalar] K`
    have hB := (h_spec_2 (by rw [Ecc.MulFixed.BaseFieldElem.circuit_envAssumptions_eq]; exact _hE) trivial trivial).1
    rw [Ecc.MulFixed.BaseFieldElem.circuit_spec_eq] at hB
    simp only [Ecc.MulFixed.BaseFieldElem.Spec] at hB
    refine ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      ⟨by rw [Ecc.MulFixed.BaseFieldElem.circuit_envAssumptions_eq]; exact _hE, trivial, trivial⟩,
      trivial, ?_, trivial⟩
    rw [Ecc.Add.addFormal_assumptions_eq]
    exact ⟨hA, by rw [hB]; exact K.smul_valid _⟩

derive_contract_bridges circuit (K : FixedBase) := circuit K

end Zcash.Circuits.Action.DeriveNullifier
