import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
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
deriving ProvableStruct

/-- The region count of the address-integrity block: four regions for the variable-base
mul, the `pk_d_old` witness region, the constrain-equal region. -/
private theorem addressIntegrity_regionCount (pkD : Point (WitgenIR Fp 1))
    (mcfg : Ecc.Mul.Config) (wcfg : Ecc.WitnessPoint.Config)
    (input : Var Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
        let pkDOld ← (Ecc.WitnessPoint.pointNonId.toFormal
          "witness non-identity point").call wcfg pkD
        assignRegion "constrain equal" (do
          constrainEqual derived.x pkDOld.x
          constrainEqual derived.y pkDOld.y)
        pure pkDOld : Circuit Fp (Var Point Fp)).operations i)
      = 6 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure, operations_assignRegion,
    Operations.regionCount_append, Operations.regionCount,
    Ecc.Mul.mul_call_regionCount,
    Ecc.WitnessPoint.pointNonId_toFormal_call_regionCount]

/-- Rust `Circuit::synthesize`'s diversified-address-integrity block (post-`commit_ivk`):
`[ivk] g_d_old` (variable-base `Ecc.Mul`), the witnessed `pk_d_old`, and the equality
constraint between them. `Spec` is knowledge soundness at the input `ivk` cell:
`pk_d_old = [ivk] g_d_old`, on-curve — no existential. -/
def circuit (pkD : Point (WitgenIR Fp 1)) : FormalCircuit Fp
    (Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    Input Point where
  name := "address integrity"
  configure := pure

  synthesize := fun (mcfg, wcfg) input => do
    let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
    let pkDOld ← (Ecc.WitnessPoint.pointNonId.toFormal
      "witness non-identity point").call wcfg pkD
    assignRegion "constrain equal" (do
      constrainEqual derived.x pkDOld.x
      constrainEqual derived.y pkDOld.y)
    pure pkDOld

  elaborated := fun (mcfg, wcfg) =>
    { output := fun input i =>
        ((do
          let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
          let pkDOld ← (Ecc.WitnessPoint.pointNonId.toFormal
            "witness non-identity point").call wcfg pkD
          assignRegion "constrain equal" (do
            constrainEqual derived.x pkDOld.x
            constrainEqual derived.y pkDOld.y)
          pure pkDOld : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun _ => 6
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (addressIntegrity_regionCount pkD mcfg wcfg input i).symm }

  EnvAssumptions := fun (mcfg, _) env => Ecc.Mul.EnvAssumptions mcfg env

  -- `g_d_old` is witnessed by `NonIdentityPoint::new` before this block
  Assumptions input := input.gDOld.OnCurve

  Witness := Point
  extract := fun (_, wcfg) _ i₀ env =>
    eval env ({ x := AssignedCell.of (i₀ + 4) 0 wcfg.x,
                y := AssignedCell.of (i₀ + 4) 0 wcfg.y } : Var Point Fp)

  Spec input output _ :=
    output.OnCurve ∧ output = input.ivk.val • input.gDOld

  -- honest proving requires the explicit `pk_d_old` witness (the extracted cell values)
  -- to be the derived address — otherwise the equality constraint is unsatisfiable — and
  -- a genuine curve point (protocol-side, `ivk ≠ 0`: the derived address is never the
  -- identity; the non-identity witness gate is unsatisfiable otherwise)
  ProverAssumptions input wit _ :=
    wit.OnCurve ∧ wit = (input.ivk.val • input.gDOld : Point Fp)

  soundness := by
    circuit_proof_start
    obtain ⟨hMul, hPkd, hCEx, hCEy⟩ := hc
    -- the mul child: the derived point is `[ivk] g_d_old`
    have hM := hMul (by rw [Ecc.Mul.mul_envAssumptions_eq]; exact _hE)
      (by rw [Ecc.Mul.mul_assumptions_eq]; exact hA)
    rw [Ecc.Mul.mul_spec_eq] at hM
    simp only [Ecc.Mul.Spec] at hM
    -- the witness child: the explicit `pk_d_old` is on-curve
    have hP := hPkd trivial trivial
    rw [Ecc.WitnessPoint.pointNonId_toFormal_spec_eq] at hP
    refine ⟨hP, ?_⟩
    -- the copy constraints pin the output to the derived point, componentwise
    have hox : output_x
        = (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0
            : Value Point Fp).x :=
      (congrArg Halo2.Ironwood.Point.x h_output).symm.trans
        ((by with_unfolding_all rfl : (eval (⟨place, env⟩ : Placed Environment Fp)
            x_gen_out_1 : Value Point Fp).x = _).trans
          (hCEx.symm.trans (by with_unfolding_all rfl)))
    have hoy : output_y
        = (eval (⟨place, env⟩ : Placed Environment Fp) x_gen_out_0
            : Value Point Fp).y :=
      (congrArg Halo2.Ironwood.Point.y h_output).symm.trans
        ((by with_unfolding_all rfl : (eval (⟨place, env⟩ : Placed Environment Fp)
            x_gen_out_1 : Value Point Fp).y = _).trans
          (hCEy.symm.trans (by with_unfolding_all rfl)))
    rw [← hM, hox, hoy]

  completeness := by
    circuit_proof_start
    obtain ⟨hIvkE, hGxE, hGyE⟩ := h_input
    -- `g_d_old`'s on-curve assumption, respelled at the input cells
    have hAE := hA
    rw [← hGxE, ← hGyE] at hAE
    -- the mul child's honest contract: the derived point is `[ivk] g_d_old`
    have hM := (h_spec_0 (by rw [Ecc.Mul.mul_envAssumptions_eq]; exact _hE)
      (by rw [Ecc.Mul.mul_assumptions_eq]; exact hAE)
      (by rw [Ecc.Mul.mul_proverAssumptions_eq]; exact hAE)).1
    rw [Ecc.Mul.mul_spec_eq] at hM
    simp only [Ecc.Mul.Spec] at hM
    -- the mul contract at the input cell values
    rw [hIvkE, hGxE, hGyE] at hM
    refine ⟨⟨by rw [Ecc.Mul.mul_envAssumptions_eq]; exact _hE,
      by rw [Ecc.Mul.mul_assumptions_eq]; exact hA,
      by rw [Ecc.Mul.mul_proverAssumptions_eq]; exact hA⟩,
      ⟨trivial, trivial, ?_⟩, ?_, ?_⟩
    · rw [Ecc.WitnessPoint.pointNonId_toFormal_proverAssumptions_eq,
        Ecc.WitnessPoint.pointNonId_toFormal_extract_eq,
        Ecc.Mul.mul_call_regionCount]
      with_unfolding_all exact hPA.1
    · -- the x-coordinate copy constraint in the honest environment
      rw [← h_gen_out_1, Ecc.WitnessPoint.pointNonId_toFormal_output,
        Ecc.Mul.mul_call_regionCount]
      exact ((by with_unfolding_all rfl :
          env.get x_gen_out_0.x.cell.column
            ((place x_gen_out_0.x.cell.regionIndex
              + x_gen_out_0.x.cell.rowOffset : ℕ) : ℤ)
            = (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0
                : Value Point Fp).x).trans
        ((congrArg Halo2.Ironwood.Point.x hM).trans
          ((congrArg Halo2.Ironwood.Point.x hPA.2).symm.trans
            (by with_unfolding_all rfl))))
    · -- the y-coordinate copy constraint in the honest environment
      rw [← h_gen_out_1, Ecc.WitnessPoint.pointNonId_toFormal_output,
        Ecc.Mul.mul_call_regionCount]
      exact ((by with_unfolding_all rfl :
          env.get x_gen_out_0.y.cell.column
            ((place x_gen_out_0.y.cell.regionIndex
              + x_gen_out_0.y.cell.rowOffset : ℕ) : ℤ)
            = (eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) x_gen_out_0
                : Value Point Fp).y).trans
        ((congrArg Halo2.Ironwood.Point.y hM).trans
          ((congrArg Halo2.Ironwood.Point.y hPA.2).symm.trans
            (by with_unfolding_all rfl))))

end Halo2.Ironwood.Action.AddressIntegrity
