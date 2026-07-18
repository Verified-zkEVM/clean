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

namespace Halo2.Ironwood.Action.DeriveNullifier

open Halo2.Ironwood (Fp)
open Orchard (Point Fq)
open Orchard.Ecc.MulFixed (FixedBase)
open Orchard.Poseidon
open Orchard.Poseidon.Permute.P128Pow5T3 (roundConstants)

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

/-! ## Child contract bridges (`rfl`, children stay folded) -/

section Bridges

variable (K : FixedBase)

private theorem hash_spec_eq :
    (Poseidon.hash (Hash.ConstantLength.capacity 2)).Spec
      = fun input output _ =>
          output = Hash.HashPaddedBlock.value roundConstants
            (Hash.ConstantLength.capacity 2) input := rfl

private theorem hash_proverSpec_eq :
    (Poseidon.hash (Hash.ConstantLength.capacity 2)).ProverSpec
      = fun input output _ _ =>
          output = Hash.HashPaddedBlock.value roundConstants
            (Hash.ConstantLength.capacity 2) input := rfl

private theorem addChip_spec_eq :
    (AddChip.add.toFormal "c = a + b").Spec
      = fun (input : Value AddChip.Inputs Fp) output (_ : Unit) =>
          output = input.a + input.b := rfl

private theorem addChip_proverSpec_eq :
    (AddChip.add.toFormal "c = a + b").ProverSpec
      = fun (input : ProverValue AddChip.Inputs Fp) output (_ : Unit) _ =>
          output = input.a + input.b := rfl

private theorem bfe_spec_eq :
    (Ecc.MulFixed.BaseFieldElem.circuit K).Spec
      = fun alpha output _ => Ecc.MulFixed.BaseFieldElem.Spec K alpha output := rfl

private theorem bfe_assumptions_eq :
    (Ecc.MulFixed.BaseFieldElem.circuit K).Assumptions = fun _ => True := rfl

private theorem bfe_envAssumptions_eq :
    (Ecc.MulFixed.BaseFieldElem.circuit K).EnvAssumptions
      = Ecc.MulFixed.BaseFieldElem.EnvAssumptions := rfl

private theorem bfe_proverAssumptions_eq :
    (Ecc.MulFixed.BaseFieldElem.circuit K).ProverAssumptions
      = fun _ _ _ => True := rfl

end Bridges

/-! ## Region counts -/

/-- The Poseidon child's call chunk spans its three regions. -/
private theorem hash_call_regionCount (pcfg : Poseidon.Config)
    (input : Var Sponge.Rate2 Fp) (j : RegionIndex) :
    Operations.regionCount
      (((Poseidon.hash (Hash.ConstantLength.capacity 2)).call pcfg input).operations j)
      = 3 := by
  rw [FormalCircuit.call_regionCount]
  rfl

/-- The add-chip child's call chunk is one region. -/
private theorem addChip_call_regionCount (acfg : AddChip.Config)
    (input : Var AddChip.Inputs Fp) (j : RegionIndex) :
    Operations.regionCount
      (((AddChip.add.toFormal "c = a + b").call acfg input).operations j) = 1 := by
  rw [FormalCircuit.call_regionCount]
  rfl

/-- The fixed-base-mul child's call chunk spans its four regions. -/
private theorem bfe_call_regionCount (K : FixedBase)
    (bcfg : Ecc.MulFixed.BaseFieldElem.Config) (input : Var field Fp) (j : RegionIndex) :
    Operations.regionCount
      (((Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg input).operations j) = 4 := by
  rw [FormalCircuit.call_regionCount]
  rfl

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
        let scalar ← (AddChip.add.toFormal "c = a + b").call acfg
          { a := hash, b := input.psi }
        let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg scalar
        let nf ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
          { p := input.cm, q := product }
        pure nf.x : Circuit Fp (Var field Fp)).operations i)
      = 9 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    hash_call_regionCount, addChip_call_regionCount, bfe_call_regionCount,
    Ecc.Add.toFormal_call_regionCount]

/-! ## The `derive_nullifier` bundle -/

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
    let scalar ← (AddChip.add.toFormal "c = a + b").call acfg
      { a := hash, b := input.psi }
    let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg scalar
    let nf ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
      { p := input.cm, q := product }
    pure nf.x

  elaborated := fun (pcfg, acfg, bcfg, ecfg) =>
    { output := fun input i =>
        ((do
          let hash ← (Poseidon.hash (Hash.ConstantLength.capacity 2)).call pcfg
            { x0 := input.nk, x1 := input.rho }
          let scalar ← (AddChip.add.toFormal "c = a + b").call acfg
            { a := hash, b := input.psi }
          let product ← (Ecc.MulFixed.BaseFieldElem.circuit K).call bcfg scalar
          let nf ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
            { p := input.cm, q := product }
          pure nf.x : Circuit Fp (Var field Fp)).output i)
      regionCount := fun _ => 9
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
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
    rw [hash_spec_eq] at hH
    -- the add-chip child: the scalar cell is `hash + psi`
    have hS := hScalar trivial trivial
    rw [addChip_spec_eq] at hS
    -- the fixed-base mul child: the product is `[scalar] K`
    have hB := hBfe (by rw [bfe_envAssumptions_eq]; exact _hE)
      (by rw [bfe_assumptions_eq]; trivial)
    rw [bfe_spec_eq] at hB
    simp only [Ecc.MulFixed.BaseFieldElem.Spec] at hB
    -- the complete addition: `nf = cm + product` (both summands valid)
    have hAddS := hAdd trivial (by
      rw [Ecc.Add.toFormal_assumptions_eq]
      exact ⟨hA, by rw [hB]; exact K.smul_valid _⟩)
    rw [Ecc.Add.toFormal_spec_eq] at hAddS
    have hSum : (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_3
        : Value Point Fp)
        = ({ x := input_cm_x, y := input_cm_y } : Point Fp)
          + (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_2
            : Value Point Fp) := hAddS.2
    rw [← h_output]
    rw [show env.get x_gen_out_3.x.cell.column
        ((place x_gen_out_3.x.cell.regionIndex
          + x_gen_out_3.x.cell.rowOffset : ℕ) : ℤ)
      = (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_3
          : Value Point Fp).x from by with_unfolding_all rfl]
    rw [hSum, hB, hS, hH, constantLength_value_two]

  completeness := by
    circuit_proof_start
    -- the fixed-base mul child's honest contract: the product is `[scalar] K`
    have hB := (h_spec_2 (by rw [bfe_envAssumptions_eq]; exact _hE) trivial trivial).1
    rw [bfe_spec_eq] at hB
    simp only [Ecc.MulFixed.BaseFieldElem.Spec] at hB
    refine ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩,
      ⟨by rw [bfe_envAssumptions_eq]; exact _hE, trivial, trivial⟩,
      trivial, ?_, trivial⟩
    rw [Ecc.Add.toFormal_assumptions_eq]
    exact ⟨hA, by rw [hB]; exact K.smul_valid _⟩

end Halo2.Ironwood.Action.DeriveNullifier
