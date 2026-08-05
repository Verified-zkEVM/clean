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

namespace Zcash.Circuits.Action.AddressIntegrity

open Halo2

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

  synthesize | (mcfg, wcfg), input => do
    let derived ← Ecc.Mul.mul.call mcfg { alpha := input.ivk, base := input.gDOld }
    let pkDOld ← Ecc.WitnessPoint.pointNonIdFormal.call wcfg input.pkDOld
    assignRegion "constrain equal" (do
      constrainEqual derived.x pkDOld.x
      constrainEqual derived.y pkDOld.y)
    pure pkDOld

  elaborated :=
    { keygenRequirements :=
        { configLawful cfg :=
            Ecc.Mul.mul.Configured cfg.1 ×
              Ecc.WitnessPoint.pointNonIdFormal.Configured cfg.2
          gates _ configured := configured.1.gates ++ configured.2.gates
          lookups _ configured := configured.1.lookups ++ configured.2.lookups
          permutationColumns cfg configured :=
            ([cfg.1.addConfig.xQR, cfg.1.addConfig.yQR,
              cfg.2.x, cfg.2.y] : List AnyColumn) ++
              configured.1.permutationColumns ++ configured.2.permutationColumns
          inputPermutationColumns _ _ input :=
            [input.ivk.cell.column, input.gDOld.x.cell.column,
              input.gDOld.y.cell.column] }
      registered := by keygen_registration
      output cfg _ i :=
        { x := .of (i + 4) 0 cfg.2.x,
          y := .of (i + 4) 0 cfg.2.y }
      regionCount _ := 6
      output_eq := by
        intro cfg input i
        simp only [Circuit.output_bind, Circuit.output_pure,
          FormalCircuit.output_call', FormalCircuit.nextRegionIndex_call',
          FormalCircuit.call_regionCount', circuit_norm,
          Ecc.WitnessPoint.pointNonIdFormal_output_cells] }

  EnvAssumptions := fun (mcfg, _) env => Ecc.Mul.EnvAssumptions mcfg env

  -- `g_d_old` is witnessed by `NonIdentityPoint::new` before this block
  Assumptions input := input.gDOld.OnCurve

  Spec
  | ⟨(ivk : Fp), (gDOld : Point Fp), _⟩, output, _ =>
    output.OnCurve ∧ output = ivk.val • gDOld

  -- honest proving requires the explicit `pk_d_old` hint value to be the derived
  -- address — otherwise the equality constraint is unsatisfiable — and a genuine curve
  -- point (protocol-side, `ivk ≠ 0`: the derived address is never the identity; the
  -- non-identity witness gate is unsatisfiable otherwise)
  ProverAssumptions
  | ⟨(ivk : Fp), (gDOld : Point Fp), (pkDOld : Point Fp)⟩, _, _ =>
    pkDOld.OnCurve ∧ pkDOld = ivk.val • gDOld

  soundness := by
    circuit_proof_start2 [Ecc.Mul.mul, Ecc.WitnessPoint.pointNonIdFormal,
      Ecc.Mul.Assumptions, Ecc.Mul.Spec]
    -- because our framework did the right thing throughout, a trivially composing
    -- parent is trivially sound
    rw [Ecc.WitnessPoint.pointNonIdFormal_output_cells] at pkDOld_eq
    have hpkCells := congrArg Point.coords pkDOld_eq
    simp only [Point.coords, Prod.mk.injEq] at hpkCells
    have hpkDOld : ({ x := output_x, y := output_y } : Point Fp) =
        { x := AssignedCell.eval place env pkDOld_x,
          y := AssignedCell.eval place env pkDOld_y } := by
      apply Point.ext_coords
      simp only [Point.coords, Prod.mk.injEq, ← hpkCells.1, ← hpkCells.2,
        circuit_norm]
      exact ⟨output_eq.1.symm, output_eq.2.symm⟩
    have hderived := derived_spec env_assumptions assumptions
    have hpkValue :
        ({ x := AssignedCell.eval place env pkDOld_x,
           y := AssignedCell.eval place env pkDOld_y } : Point Fp) =
          ZMod.val (show Fp from input_ivk) •
            ({ x := input_gDOld_x, y := input_gDOld_y } : Point Fp) := by
      rw [← hderived]
      apply Point.ext_coords
      simp only [Point.coords, Prod.mk.injEq]
      exact ⟨region_0.1.symm, region_0.2.symm⟩
    exact ⟨hpkDOld ▸ pkDOld_spec, hpkDOld.trans hpkValue⟩

  completeness := by
    circuit_proof_start2 [Ecc.Mul.mul, Ecc.WitnessPoint.pointNonIdFormal,
      Ecc.Mul.Assumptions, Ecc.Mul.Spec]
    -- because our framework did the right thing throughout, a trivially composing
    -- parent is trivially complete
    grind

derive_contract_bridges circuit := circuit

end Zcash.Circuits.Action.AddressIntegrity
