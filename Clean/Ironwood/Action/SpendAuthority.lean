import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulFixed.FullWidth

/-!
# Orchard spend authority (Ironwood)

Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit.rs`, the `Spend authority` block in `Circuit::synthesize`
(lines 629-644): `alpha_commitment = [alpha] SpendAuthG` (full-width fixed-base mul,
discarding the returned scalar decomposition), then `rk = alpha_commitment + ak_P`. The
final public-instance constraints on `rk.x`/`rk.y` belong to the enclosing action
synthesis.

## Knowledge soundness

The phase-1 donor (`Clean/Orchard/Action/SpendAuthority.lean`) could only state
`∃ alpha, rk = [alpha] SpendAuthG + ak_P` — vacuous, since `SpendAuthG` generates the
group. Here `alpha` is the `FullWidth` child's extraction data (the scalar its witnessed
window cells encode), so the `Spec` is the real knowledge-soundness statement: the
extractor reads `alpha` off any satisfying assignment and `rk = [alpha] SpendAuthG + ak_P`
holds at that `alpha`, with no existential.
-/

namespace Halo2.Ironwood.Action.SpendAuthority

open Halo2.Ironwood (Fp)
open Orchard (Point Fq)
open Orchard.Ecc.MulFixed (FixedBase)

/-- The input of the spend-authority block: the already-assigned authorizing key point
`ak_P`. (The randomizer `alpha` lives on the `FullWidth` child's witness boundary — the
caller's 85 window witness programs encode it, and the scalar is the extraction data.) -/
structure Input (F : Type) where
  akP : Point F
deriving ProvableStruct

/-- The region count of the spend-authority block: two regions for the full-width
fixed-base mul, one for the final complete addition. -/
private theorem spendAuthority_regionCount (G : FixedBase)
    (windows : Vector (FExpr Fp) 85)
    (fcfg : Ecc.MulFixed.FullWidth.Config) (ecfg : Ecc.Add.Config)
    (input : Var Input Fp) (i : RegionIndex) :
    Operations.regionCount
      ((do
        let alphaCommitment ← (Ecc.MulFixed.FullWidth.circuit G windows).call fcfg ()
        let rk ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
          { p := alphaCommitment, q := input.akP }
        pure rk : Circuit Fp (Var Point Fp)).operations i)
      = 3 := by
  simp only [Circuit.operations_bind, Circuit.operations_pure,
    Operations.regionCount_append, Operations.regionCount,
    Ecc.MulFixed.FullWidth.circuit_call_regionCount,
    Ecc.Add.toFormal_call_regionCount]

/-- Rust `Circuit::synthesize`'s spend-authority block: `[alpha] SpendAuthG` (the
`FullWidth` bundle) plus `ak_P`. `Spec` is knowledge soundness at the extracted
randomizer: `rk = [alpha] SpendAuthG + ak_P` for the `alpha` read off the witnessed
window cells — no existential. -/
def circuit (G : FixedBase) (windows : Vector (FExpr Fp) 85) : FormalCircuit Fp
    (Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    Input Point where
  name := "spend authority"
  configure := pure

  synthesize := fun (fcfg, ecfg) input => do
    let alphaCommitment ← (Ecc.MulFixed.FullWidth.circuit G windows).call fcfg ()
    let rk ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
      { p := alphaCommitment, q := input.akP }
    pure rk

  elaborated := fun (fcfg, ecfg) =>
    { output := fun input i =>
        ((do
          let alphaCommitment ← (Ecc.MulFixed.FullWidth.circuit G windows).call fcfg ()
          let rk ← (Ecc.Add.add.toFormal "complete point addition").call ecfg
            { p := alphaCommitment, q := input.akP }
          pure rk : Circuit Fp (Var Point Fp)).output i)
      regionCount := fun _ => 3
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i =>
        (spendAuthority_regionCount G windows fcfg ecfg input i).symm }

  EnvAssumptions := fun (fcfg, _) env =>
    Ecc.MulFixed.FullWidth.EnvAssumptions fcfg env

  -- `ak_P` is already assigned as a valid Pallas point before the spend-authority block
  Assumptions input := input.akP.Valid

  Witness := fun F => Vector F 85 × Fq
  extract := fun (fcfg, _) _ i₀ env =>
    Ecc.MulFixed.FullWidth.fwExtract fcfg i₀ env

  Spec input output wit :=
    output = (wit.2 • G : Point Fp) + input.akP

  ProverAssumptions _ wit _ :=
    ∀ w : Fin 85, (wit.1[w.val]).val < 8

  soundness := by
    circuit_proof_start
    obtain ⟨hFw, hAdd⟩ := hc
    -- the full-width child: the commitment is the extracted scalar times `G`
    have hAl := hFw
      (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact _hE)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hAl
    -- the complete addition: `rk = alpha_commitment + ak_P` (both summands valid)
    have hAddS := hAdd trivial (by
      rw [Ecc.Add.toFormal_assumptions_eq]
      exact ⟨by rw [hAl]; exact G.smul_valid _, hA⟩)
    rw [Ecc.Add.toFormal_spec_eq] at hAddS
    rw [hAddS.2, hAl]

  completeness := by
    circuit_proof_start
    -- the full-width child's contract: the commitment is the extracted scalar times `G`
    have hAl := (h_spec_0
      (by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact _hE)
      (by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial)
      (by rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq,
            Ecc.MulFixed.FullWidth.circuit_extract_eq]
          exact hPA)).1
    rw [Ecc.MulFixed.FullWidth.circuit_spec_eq,
      Ecc.MulFixed.FullWidth.circuit_extract_eq] at hAl
    refine ⟨⟨by rw [Ecc.MulFixed.FullWidth.circuit_envAssumptions_eq]; exact _hE,
      by rw [Ecc.MulFixed.FullWidth.circuit_assumptions_eq]; trivial,
      by
        rw [Ecc.MulFixed.FullWidth.circuit_proverAssumptions_eq,
          Ecc.MulFixed.FullWidth.circuit_extract_eq]
        exact hPA⟩,
      trivial, ?_, trivial⟩
    rw [Ecc.Add.toFormal_assumptions_eq]
    exact ⟨by rw [hAl]; exact G.smul_valid _, hA⟩

end Halo2.Ironwood.Action.SpendAuthority
