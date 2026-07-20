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

/-! ## Child contract bridges (`rfl`, children stay folded)

The `FullWidth` and `Ecc.Add` bridges are the shared ones
(`Ecc.MulFixed.FullWidth.circuit_*`, `Ecc.Add.toFormal_*`); the `Short` bundle has this
file as its only layouter-level consumer. -/

section Bridges

variable (V : Halo2.Ironwood.Ecc.MulFixed.Short.FixedBase)

private theorem short_spec_eq :
    (Ecc.MulFixed.Short.circuit V).Spec
      = fun input output _ => Ecc.MulFixed.Short.Spec V input output := rfl

private theorem short_assumptions_eq :
    (Ecc.MulFixed.Short.circuit V).Assumptions = fun _ => True := rfl

private theorem short_envAssumptions_eq :
    (Ecc.MulFixed.Short.circuit V).EnvAssumptions
      = Ecc.MulFixed.Short.EnvAssumptions := rfl

private theorem short_proverAssumptions_eq :
    (Ecc.MulFixed.Short.circuit V).ProverAssumptions
      = fun (input : Value Ecc.MulFixed.Short.Inputs Fp) _ _ =>
          input.magnitude.val < 2 ^ 64 ∧ (input.sign = 1 ∨ input.sign = -1) := rfl

/-- The short-mul child's call chunk spans its two regions. -/
private theorem short_call_regionCount (scfg : Ecc.MulFixed.Short.Config)
    (input : Var Ecc.MulFixed.Short.Inputs Fp) (j : RegionIndex) :
    Operations.regionCount
      (((Ecc.MulFixed.Short.circuit V).call scfg input).operations j) = 2 := by
  rw [FormalCircuit.call_regionCount]
  rfl

end Bridges

/-- The inputs: the short child's magnitude/sign cells and the blinding scalar's
nat-valued reading program `rcv` (a prover hint — Rust `Value<pallas::Scalar>`; the
full-width child derives its window witnesses from it, the scalar is extraction data). -/
structure Inputs (F : Type) where
  rcv : UnconstrainedNat F
  magnitude : F
  sign : F
deriving CircuitType

/-- The region count of `value_commit_orchard`: two regions each for the short and
full-width fixed-base muls, one for the final complete addition. -/
private theorem valueCommit_regionCount (V : Halo2.Ironwood.Ecc.MulFixed.Short.FixedBase)
    (R : FixedBase)
    (scfg : Ecc.MulFixed.Short.Config) (fcfg : Ecc.MulFixed.FullWidth.Config)
    (ecfg : Ecc.Add.Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let commitment ← (Ecc.MulFixed.Short.circuit V).call scfg
          ⟨input.magnitude, input.sign⟩
        let blind ← (Ecc.MulFixed.FullWidth.circuit R).call fcfg input.rcv
        let cv ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
          { p := commitment, q := blind }
        pure cv : Circuit Fp (Var Point Fp)).operations i)
      = 5 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    short_call_regionCount, Ecc.MulFixed.FullWidth.circuit_call_regionCount,
    Ecc.Add.toFormal_call_regionCount]

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

  synthesize := fun (scfg, fcfg, ecfg) input => do
    let commitment ← (Ecc.MulFixed.Short.circuit V).call scfg
      ⟨input.magnitude, input.sign⟩
    let blind ← (Ecc.MulFixed.FullWidth.circuit R).call fcfg input.rcv
    let cv ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
      { p := commitment, q := blind }
    pure cv

  elaborated := fun (scfg, fcfg, ecfg) =>
    { output := fun input i =>
        ((do
          let commitment ← (Ecc.MulFixed.Short.circuit V).call scfg
            ⟨input.magnitude, input.sign⟩
          let blind ← (Ecc.MulFixed.FullWidth.circuit R).call fcfg input.rcv
          let cv ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
            { p := commitment, q := blind }
          pure cv : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun _ => 5
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (valueCommit_regionCount V R scfg fcfg ecfg input i).symm }

  EnvAssumptions := fun (scfg, fcfg, _) env =>
    Ecc.MulFixed.Short.EnvAssumptions scfg env ∧
    Ecc.MulFixed.FullWidth.EnvAssumptions fcfg env

  Assumptions _ := True

  Witness := fun F => Vector F 85 × Fq
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
    circuit_proof_start
    obtain ⟨hSEnv, hFEnv⟩ := _hE
    obtain ⟨hShort, hFw, hAdd⟩ := hc
    -- the short child: the commitment is `[±m] V` at some `m < 2⁶⁴`
    have hSh := hShort (by rw [short_envAssumptions_eq]; exact hSEnv)
      (by rw [short_assumptions_eq]; trivial)
    rw [short_spec_eq] at hSh
    simp only [Ecc.MulFixed.Short.Spec] at hSh
    obtain ⟨m, hm_lt, hmag, hcases⟩ := hSh
    -- the full-width child: the blind is the extracted scalar times `R`
    have hBl := hFw
      (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hFEnv)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hBl
    -- the complete addition: `cv = commitment + blind` (both summands valid)
    have hAddS := hAdd trivial (by
      rw [Ecc.Add.toFormal_assumptions_eq]
      refine ⟨?_, by rw [hBl]; exact R.smul_valid _⟩
      rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact V.smul_valid _)
    rw [Ecc.Add.toFormal_spec_eq] at hAddS
    rw [short_call_regionCount] at hBl
    refine ⟨m, hm_lt, hmag, ?_⟩
    rcases hcases with ⟨hsign, hC⟩ | ⟨hsign, hC⟩
    · exact Or.inl ⟨hsign, by rw [hAddS.2, hC, hBl]⟩
    · exact Or.inr ⟨hsign, by rw [hAddS.2, hC, hBl]⟩

  completeness := by
    circuit_proof_start
    obtain ⟨hSEnv, hFEnv⟩ := _hE
    obtain ⟨hmag, hsign⟩ := hPA
    obtain ⟨-, hIn1, hIn2⟩ := h_input
    have hmagE := hmag
    rw [← hIn1] at hmagE
    have hsignE := hsign
    rw [← hIn2] at hsignE
    -- the short child's contract: the commitment is `[±m] V`
    have hSh := (h_spec_0 (by rw [short_envAssumptions_eq]; exact hSEnv)
      (by rw [short_assumptions_eq]; trivial)
      (by rw [short_proverAssumptions_eq]; exact ⟨hmagE, hsignE⟩)).1
    rw [short_spec_eq] at hSh
    simp only [Ecc.MulFixed.Short.Spec] at hSh
    obtain ⟨m, -, -, hcases⟩ := hSh
    -- the full-width child's contract: the blind is the extracted scalar times `R`
    have hBl := (h_spec_1
      (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hFEnv)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
      (by rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq]; trivial)).1
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hBl
    refine ⟨⟨by rw [short_envAssumptions_eq]; exact hSEnv,
      by rw [short_assumptions_eq]; trivial,
      by rw [short_proverAssumptions_eq]; exact ⟨hmag, hsign⟩⟩,
      ⟨by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact hFEnv,
       by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial,
       by rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq]; trivial⟩,
      trivial, ?_, trivial⟩
    rw [Ecc.Add.toFormal_assumptions_eq]
    refine ⟨?_, by rw [hBl]; exact R.smul_valid _⟩
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact V.smul_valid _

end Halo2.Ironwood.Action.ValueCommit
