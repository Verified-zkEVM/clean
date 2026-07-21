import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Halo2.CircuitTypeDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Mul
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Orchard diversified address integrity (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit.rs`, the `Diversified address integrity` block in
`Circuit::synthesize` — the part *after* `commit_ivk` (the commitment itself is a
separate building block; its output cell feeds in here as `ivk`):
1. `ScalarVar::from_base` (`ecc/chip.rs:688-694`) — a pure wrapper, no region;
2. `g_d_old.mul(|| "[ivk] g_d_old", ivk)` — variable-base scalar mul (the `Ecc.Mul`
   bundle, four regions);
3. `NonIdentityPoint::new(|| "witness pk_d_old")` — the `"witness non-identity point"`
   region witnessing the explicit `pk_d_old`;
4. `derived_pk_d_old.constrain_equal(|| "pk_d_old equality")` — the `"constrain equal"`
   region (`ecc/chip.rs:474-488`), two copy constraints.

The block returns the witnessed `pk_d_old`. `Spec` is knowledge-sound with no
existential: `pk_d_old = [ivk] g_d_old` at the input `ivk` cell (the phase-1 donor
carried the whole `CommitIvk` call inside and an `∃ ivk` — here `ivk` is an input, so
the statement is direct).

Phase-1 donor: `Clean/Orchard/Action/AddressIntegrity.lean` (post-`CommitIvk` part).
-/

namespace Halo2.Ironwood.Action.AddressIntegrity

open Halo2.Ironwood (Fp)
open Halo2.Ironwood (Point)

/-- The inputs of the address-integrity block: the committed incoming viewing key cell
`ivk` (the `commit_ivk` output, coerced by the region-free `ScalarVar::from_base`) and
the old diversified base point `g_d_old` (witnessed earlier in `synthesize`). The
explicit `pk_d_old` is witnessed *inside* the block. -/
structure Input (F : Type) where
  ivk : F
  gDOld : Point F
  -- the explicit `pk_d_old`'s reading program — a prover hint (Rust passes it as
  -- `Value<pallas::Affine>`); witnessed inside the block by the `pointNonId` region
  pkDOld : Unconstrained Point F
deriving CircuitType

/-- The region count of the address-integrity block: four regions for the variable-base
mul, the `pk_d_old` witness region, the constrain-equal region. -/
private theorem addressIntegrity_regionCount
    (mcfg : Ecc.Mul.Config) (wcfg : Ecc.WitnessPoint.Config)
    (input : Var Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
        let pkDOld ← (Ecc.WitnessPoint.pointNonId.toFormal
          "witness non-identity point").call wcfg input.pkDOld
        assignRegion "constrain equal" (do
          constrainEqual derived.x pkDOld.x
          constrainEqual derived.y pkDOld.y)
        pure pkDOld : Circuit Fp (Var Point Fp)).operations i)
      = 6 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount,
    FormalCircuit.call_regionCount]
  rfl

/-- Rust `Circuit::synthesize`'s diversified-address-integrity block (post-`commit_ivk`):
`[ivk] g_d_old` (variable-base `Ecc.Mul`), the witnessed `pk_d_old`, and the equality
constraint between them. `Spec` is knowledge soundness at the input `ivk` cell:
`pk_d_old = [ivk] g_d_old`, on-curve — no existential. -/
def circuit : FormalCircuit Fp
    (Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    Input Point where
  name := "address integrity"
  configure := pure

  synthesize := fun (mcfg, wcfg) input => do
    let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
    let pkDOld ← (Ecc.WitnessPoint.pointNonId.toFormal
      "witness non-identity point").call wcfg input.pkDOld
    assignRegion "constrain equal" (do
      constrainEqual derived.x pkDOld.x
      constrainEqual derived.y pkDOld.y)
    pure pkDOld

  elaborated := fun (mcfg, wcfg) =>
    { output := fun input i =>
        ((do
          let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
          let pkDOld ← (Ecc.WitnessPoint.pointNonId.toFormal
            "witness non-identity point").call wcfg input.pkDOld
          assignRegion "constrain equal" (do
            constrainEqual derived.x pkDOld.x
            constrainEqual derived.y pkDOld.y)
          pure pkDOld : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun _ => 6
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (addressIntegrity_regionCount mcfg wcfg input i).symm }

  EnvAssumptions := fun (mcfg, _) env => Ecc.Mul.EnvAssumptions mcfg env

  -- `g_d_old` is witnessed by `NonIdentityPoint::new` before this block
  Assumptions input := input.gDOld.OnCurve

  Spec input output _ :=
    output.OnCurve ∧ output = (show Fp from input.ivk).val • (show Point Fp from input.gDOld)

  -- honest proving requires the explicit `pk_d_old` hint value to be the derived
  -- address — otherwise the equality constraint is unsatisfiable — and a genuine curve
  -- point (protocol-side, `ivk ≠ 0`: the derived address is never the identity; the
  -- non-identity witness gate is unsatisfiable otherwise)
  ProverAssumptions input _ _ :=
    (show Point Fp from input.pkDOld).OnCurve ∧
      (show Point Fp from input.pkDOld)
        = ((show Fp from input.ivk).val • (show Point Fp from input.gDOld) : Point Fp)

  soundness := by
    -- ═══ v2-manual FRAMEWORK prefix (atomic binds; to become one `circuit_proof_start2`) ═══
    rintro ⟨mcfg, wcfg⟩
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_input h_output hE hA hC
    obtain ⟨place, env⟩ := env
    dsimp only [] at *
    simp only [ElaboratedCircuit.output_eq] at h_output
    -- bind 1 [derived ← mul.call mcfg { alpha := ivk, base := gDOld }]
    rw [Circuit.operations_bind, constraints_append] at hC
    rw [Circuit.output_bind] at h_output
    obtain ⟨h_call_mul, hC⟩ := hC
    simp only [FormalCircuit.output_call'] at hC h_output
    revert hC h_output
    generalize h_derived : Ecc.Mul.mul.output mcfg
      { alpha := input_var.ivk, base := input_var.gDOld } i₀ = derived
    intro hC h_output
    simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount] at hC h_output
    -- bind 2 [pkDOld ← (pointNonId.toFormal …).call wcfg input.pkDOld]
    rw [Circuit.operations_bind, constraints_append] at hC
    rw [Circuit.output_bind] at h_output
    obtain ⟨h_call_pkd, hC⟩ := hC
    simp only [FormalCircuit.output_call'] at hC h_output
    revert hC h_output
    generalize h_pkd : (Ecc.WitnessPoint.pointNonId.toFormal
      "witness non-identity point").output wcfg input_var.pkDOld (i₀ + 4) = pkDOld
    intro hC h_output
    simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount] at hC h_output
    -- bind 3 [_ ← assignRegion "constrain equal" …] — unit-valued, no atom; open the raw
    -- region to its two copy equations (cell reads OF THE ATOMS' cells)
    rw [Circuit.operations_bind, constraints_append] at hC
    rw [Circuit.output_bind] at h_output
    obtain ⟨h_copies, hC⟩ := hC
    simp only [circuit_norm] at h_copies
    -- terminal `pure pkDOld`
    rw [Circuit.operations_pure, constraints_nil] at hC
    rw [Circuit.output_pure] at h_output
    clear hC
    -- consume the child chunks: contracts over the atoms
    subcircuit_rw at h_call_mul
    subcircuit_rw at h_call_pkd
    -- value landing on component atoms
    provable_type_simp
    simp only [h_input, h_output] at h_call_mul h_call_pkd h_copies ⊢
    -- simp using user-supplied lemma list
    simp only [
      circuit_norm,
      Ecc.Mul.mul_assumptions_eq, Ecc.Mul.mul_spec_eq, Ecc.Mul.mul_envAssumptions_eq,
      Ecc.Mul.Assumptions, Ecc.Mul.Spec,
      Ecc.WitnessPoint.pointNonId_toFormal_assumptions_eq, Ecc.WitnessPoint.pointNonId_toFormal_spec_eq,
      Ecc.WitnessPoint.pointNonId_toFormal_envAssumptions_eq
    ] at h_call_mul h_call_pkd h_copies
    -- ═══ USER half ═══
    -- because our framework did the right thing throughout, a trivially composing parent is trivially sound
    simp_all

  completeness := by
    circuit_proof_start2
    -- (h′) prover/verifier eval coincidence for the hint-free point var (v2 TODO: this
    -- should be a circuit_norm law; cell reads already coincide via toEnvironment_get)
    have h_gdV : (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) input_var_gDOld
        : Value Point Fp) = input_gDOld := by
      rw [← h_input_gDOld]
      simp only [circuit_norm, explicit_provable_type]
    -- residual value replacement with the coincidence law (the tactic already landed
    -- the field-typed components)
    simp only [h_gdV] at h_spec_0 h_spec_1 hA ⊢
    -- ═══ USER half ═══
    -- `g_d_old`'s on-curve assumption, respelled at the input value
    -- the mul child's honest contract: the derived point is `[ivk] g_d_old`
    have hM := (h_spec_0 hE (by rw [Ecc.Mul.mul_assumptions_eq]; exact hA)
      (by rw [Ecc.Mul.mul_proverAssumptions_eq]; exact hA)).1
    rw [Ecc.Mul.mul_spec_eq] at hM
    simp only [Ecc.Mul.Spec] at hM
    -- the witness child's honest contract: the assigned cells carry the hint's value
    have hPS := (h_spec_1 trivial trivial (by
      rw [Ecc.WitnessPoint.pointNonId_toFormal_proverAssumptions_eq]
      exact hPA.1)).2
    rw [Ecc.WitnessPoint.pointNonId_toFormal_proverSpec_eq] at hPS
    have hDP := hM.trans (hPA.2.symm.trans hPS.symm)
    refine ⟨⟨hE, by rw [Ecc.Mul.mul_assumptions_eq]; exact hA,
      by rw [Ecc.Mul.mul_proverAssumptions_eq]; exact hA⟩, ⟨trivial, trivial, ?_⟩, ?_, ?_⟩
    · rw [Ecc.WitnessPoint.pointNonId_toFormal_proverAssumptions_eq]
      exact hPA.1
    · -- the x-coordinate copy constraint in the honest environment
      have h := congrArg Halo2.Ironwood.Point.x hDP
      simp only [circuit_norm, explicit_provable_type] at h
      exact h
    · -- the y-coordinate copy constraint in the honest environment
      have h := congrArg Halo2.Ironwood.Point.y hDP
      simp only [circuit_norm, explicit_provable_type] at h
      exact h

derive_contract_bridges circuit := circuit

end Halo2.Ironwood.Action.AddressIntegrity
