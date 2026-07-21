import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.FullWidth
import Clean.Halo2.CircuitTypeDeriving
import Clean.Ironwood.Ecc.MulFixed.Short

/-!
# Orchard value commitment (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/gadget.rs::value_commit_orchard` (lines 115-148):
`cv = [v] ValueCommitV + [rcv] ValueCommitR` — three layouter pieces in source order:
1. `FixedPointShort::from_inner(ValueCommitV).mul(v)` (the `Ecc.MulFixed.Short`
   bundle; `v` is the signed magnitude-sign pair);
2. `FixedPoint::from_inner(ValueCommitR).mul(rcv)` (the `Ecc.MulFixed.FullWidth`
   bundle; the full-width scalar lives on the child's witness boundary — the caller's
   85 window witness programs encode it, and the scalar is the extraction data);
3. `commitment.add(blind)` (region `"complete point addition"`, `ecc/chip.rs:582-595`).

Phase-1 donor: `Clean/Orchard/Action/ValueCommit.lean`.
-/

namespace Halo2.Ironwood.Action.ValueCommit

open Halo2.Ironwood (Fp)
open Halo2.Ironwood (Point Fq)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)

/-- The inputs: the short child's magnitude/sign cells and the blinding scalar's
nat-valued reading program `rcv` (a prover hint — Rust `Value<pallas::Scalar>`; the
full-width child derives its window witnesses from it, the scalar is extraction data). -/
structure Inputs (F : Type) where
  rcv : UnconstrainedNat F
  magnitude : F
  sign : F
deriving CircuitType

/-! ## The `value_commit_orchard` bundle -/

/-- Rust `gadget.rs::value_commit_orchard`: `[v] ValueCommitV` (short signed), `[rcv]
ValueCommitR` (full-width; the scalar is the child's extraction data), and the final
complete addition. `Spec` is the donor contract: the commitment is
`[±m] V + [rcv] R` at the sign-resolved magnitude `m < 2⁶⁴` and the extracted
full-width scalar. -/
def circuit (V : Halo2.Ironwood.Ecc.MulFixed.Short.FixedBase) (R : FixedBase) :
    FormalCircuit Fp
    (Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (Ecc.MulFixed.Short.Config × Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    Inputs Point where
  name := "value commit"
  configure := pure

  synthesize | (scfg, fcfg, ecfg), input => do
    let commitment ← (Ecc.MulFixed.Short.circuit V).call scfg
      ⟨input.magnitude, input.sign⟩
    let blind ← (Ecc.MulFixed.FullWidth.circuit R).call fcfg input.rcv
    let cv ← Ecc.Add.addFormal.call ecfg
      { p := commitment, q := blind }
    pure cv

  elaborated _ := { regionCount _ := 5 }

  EnvAssumptions := fun (scfg, fcfg, _) env =>
    Ecc.MulFixed.Short.EnvAssumptions scfg env ∧
    Ecc.MulFixed.FullWidth.EnvAssumptions fcfg env

  Witness F := Vector F 85 × Fq
  extract := fun (_, fcfg, _) _ i₀ env =>
    Ecc.MulFixed.FullWidth.fwExtract fcfg (i₀ + 2) env

  Spec input output wit :=
    ∃ m : ℕ, m < 2 ^ 64 ∧ (show Fp from input.magnitude) = (m : Fp) ∧
      (((show Fp from input.sign) = 1 ∧
          output = ((m : Fq) • V : Point Fp) + (wit.2 • R : Point Fp)) ∨
        ((show Fp from input.sign) = -1 ∧
          output = (((-(m : Fq)) : Fq) • V : Point Fp) + (wit.2 • R : Point Fp)))

  ProverAssumptions input _ _ :=
    (show Fp from input.magnitude).val < 2 ^ 64 ∧
      ((show Fp from input.sign) = 1 ∨ (show Fp from input.sign) = -1)

  soundness := by
    circuit_proof_start2 [
      Ecc.MulFixed.Short.circuit_envAssumptions_eq, Ecc.MulFixed.Short.circuit_assumptions_eq,
      Ecc.MulFixed.Short.circuit_spec_eq, Ecc.MulFixed.Short.Spec,
      Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_assumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_spec_eq, Ecc.MulFixed.FullWidth.circuit_extract_eq,
      Ecc.Add.addFormal_assumptions_eq, Ecc.Add.addFormal_spec_eq]
    obtain ⟨hSEnv, hFEnv⟩ := hE
    obtain ⟨m, hm_lt, hmag, hcases⟩ := h_call_commitment hSEnv
    have hBl := h_call_blind hFEnv
    have hAddS := h_call_cv trivial ⟨by
        rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact V.smul_valid _,
      by rw [hBl]; exact R.smul_valid _⟩
    refine ⟨m, hm_lt, hmag, ?_⟩
    rcases hcases with ⟨hsign, hCm⟩ | ⟨hsign, hCm⟩
    · exact Or.inl ⟨hsign, by simp_all⟩
    · exact Or.inr ⟨hsign, by simp_all⟩

  completeness := by
    circuit_proof_start2 [
      Ecc.MulFixed.Short.circuit_envAssumptions_eq, Ecc.MulFixed.Short.circuit_assumptions_eq,
      Ecc.MulFixed.Short.circuit_proverAssumptions_eq,
      Ecc.MulFixed.Short.circuit_spec_eq, Ecc.MulFixed.Short.Spec,
      Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_assumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq,
      Ecc.MulFixed.FullWidth.circuit_spec_eq, Ecc.MulFixed.FullWidth.circuit_extract_eq,
      Ecc.Add.addFormal_assumptions_eq, Ecc.Add.addFormal_spec_eq]
    obtain ⟨hSEnv, hFEnv⟩ := hE
    obtain ⟨hmag, hsign⟩ := hPA
    obtain ⟨⟨m, hm_lt, hmag', hcases⟩, -⟩ := h_spec_0 hSEnv ⟨hmag, hsign⟩
    have hBl := (h_spec_1 hFEnv).1
    refine ⟨⟨hSEnv, hmag, hsign⟩, hFEnv, trivial, ⟨?_, by rw [hBl]; exact R.smul_valid _⟩,
      trivial⟩
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact V.smul_valid _

derive_contract_bridges circuit (V : Halo2.Ironwood.Ecc.MulFixed.Short.FixedBase)
  (R : FixedBase) := circuit V R

end Halo2.Ironwood.Action.ValueCommit
