import Clean.Ironwood.CommitIvk.Bundle
import Clean.Ironwood.Utilities.LookupRangeCheck

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/commit_ivk.rs` — the canonicity flow around the gate region:
`canon_bitshift_130` for `a' = a + 2^130 - t_P` (13-word `witness_check`), the `b2_c'`
shift `b_2 + 2^5·c + 2^140 - t_P` (14-word `witness_check`), then the
`"Assign cells used in canonicity gate"` region (`CommitIvkChip::assign`,
`commit_ivk.rs:519-660`). Phase-1 donor: `CommitIvk.Canonicity`
(`Clean/Orchard/Action/CommitIvk.lean`).

The composite is a three-child layouter `FormalCircuit` parameterized (like the gate
bundle) by the `b_1`/`d_1` witness programs. `Spec` is the donor composite payoff — the
canonical bit slices of `ak`/`nk` and the `b`/`d` decompositions — at the witnessed
`(b_1, d_1)` readings, which are the extraction data.
-/

namespace Zcash.Circuits.CommitIvk

open Halo2
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Specs (bitrange)
open NoteCommit (high_bit_canonical shifted_high_zero bit_one_of_val_eq
  base_val_lt_tP_val tPNat)

private theorem rangeCheckAt_output (n : ℕ) (cfg : LookupRangeCheck.Config 10)
    (i : RegionIndex) :
    (LookupRangeCheck.rangeCheckAt 10 n false).output cfg 0 () i
      = { z0 := .of i 0 cfg.runningSum, zLast := .of i n cfg.runningSum } := by
  show ((LookupRangeCheck.rangeCheckAt 10 n false).synthesize cfg 0 ()).output i = _
  simp only [LookupRangeCheck.rangeCheckAt, circuit_norm, RegionCircuit.output_bind,
    output_cellAt, Bool.false_eq_true, if_false, Nat.zero_add]

namespace Canonicity

/-- The copied-in cells (the `a'`/`b2_c'` shift decompositions are witnessed by the
lookup children; `b_1`/`d_1` are witnessed inside the gate region). -/
structure Inputs (F : Type) where
  ak : F
  a : F
  bWhole : F
  b0 : F
  b2 : F
  z13A : F
  nk : F
  c : F
  dWhole : F
  d0 : F
  z13C : F
deriving ProvableStruct

/-- The `a' = a + 2¹³⁰ − t_P` witness program (Rust `canon_bitshift_130`). -/
def aPrimeWit (a : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env a + ((2 ^ 130 : ℕ) : Fp) - tP]

@[circuit_norm]
theorem aPrimeWit_eval (a : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((aPrimeWit a).eval env)[j] = readCell env a + ((2 ^ 130 : ℕ) : Fp) - tP := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [aPrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The `b2_c' = b_2 + 2⁵·c + 2¹⁴⁰ − t_P` witness program. -/
def b2CPrimeWit (b2 c : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env b2 + ((2 ^ 5 : ℕ) : Fp) * readCell env c
    + ((2 ^ 140 : ℕ) : Fp) - tP]

@[circuit_norm]
theorem b2CPrimeWit_eval (b2 c : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((b2CPrimeWit b2 c).eval env)[j] = readCell env b2 + ((2 ^ 5 : ℕ) : Fp) * readCell env c
      + ((2 ^ 140 : ℕ) : Fp) - tP := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [b2CPrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The gate child: the `CommitIvk` two-row bundle in its own layouter region. -/
def gateChild (wb1 wd1 : WitgenIR Fp 1) :
    FormalCircuit Fp Config Config CommitIvk.Inputs unit :=
  (bundle wb1 wd1).toFormal "Assign cells used in canonicity gate"

derive_contract_bridges gateChild (wb1 wd1 : WitgenIR Fp 1) := gateChild wb1 wd1

def synth (wb1 wd1 : WitgenIR Fp 1) (gcfg : Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) : Circuit Fp Unit := do
  let aZs ← LookupRangeCheck.witnessCheck 10 13 false lcfg (aPrimeWit input.a)
  let bZs ← LookupRangeCheck.witnessCheck 10 14 false lcfg (b2CPrimeWit input.b2 input.c)
  let _ ← (gateChild wb1 wd1).call gcfg
    { ak := input.ak, a := input.a, bWhole := input.bWhole, b0 := input.b0,
      b2 := input.b2, z13A := input.z13A, aPrime := aZs.z0, z13APrime := aZs.zLast,
      nk := input.nk, c := input.c, dWhole := input.dWhole, d0 := input.d0,
      z13C := input.z13C, b2CPrime := bZs.z0, z14B2CPrime := bZs.zLast }
  pure ()

theorem synth_regionCount (wb1 wd1 : WitgenIR Fp 1) (gcfg : Config)
    (lcfg : LookupRangeCheck.Config 10) (input : Inputs (AssignedCell Fp))
    (i : RegionIndex) :
    Operations.regionCount ((synth wb1 wd1 gcfg lcfg input).operations i) = 3 := by
  simp only [synth, LookupRangeCheck.witnessCheck, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

private theorem gateChild_extract_cells (wb1 wd1 : WitgenIR Fp 1) (cfg : Config)
    (inp : Var CommitIvk.Inputs Fp) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (gateChild wb1 wd1).extract cfg inp i env
      = (eval env (AssignedCell.of i 0 (cfg.advices 4) : Var field Fp),
         eval env (AssignedCell.of i (0 + 1) (cfg.advices 4) : Var field Fp)) := rfl

/-- Rust `CommitIvkChip` canonicity flow: the two shift `witness_check`s, then the
`"Assign cells used in canonicity gate"` region. `Spec` is the donor composite payoff
(`CommitIvk.Canonicity.Spec`): the canonical bit slices of `ak`/`nk` and
the `b`/`d` sub-piece decompositions, at the witnessed `(b_1, d_1)` readings. -/
def circuit (wb1 wd1 : WitgenIR Fp 1) :
    FormalCircuit Fp (Config × LookupRangeCheck.Config 10)
      (Config × LookupRangeCheck.Config 10) Inputs unit where
  name := "CommitIvk canonicity"
  configure := pure

  synthesize := fun (gcfg, lcfg) input => synth wb1 wd1 gcfg lcfg input

  elaborated :=
    { output := fun _ _ _ => ()
      regionCount _ := 3
      output_eq := by intro _ _ _; rfl
      regionCount_eq := fun (gcfg, lcfg) input i =>
        (synth_regionCount wb1 wd1 gcfg lcfg input i).symm }

  EnvAssumptions := fun (_, lcfg) env =>
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions input :=
    input.a.val < 2 ^ 250 ∧ input.b0.val < 2 ^ 4 ∧ input.b2.val < 2 ^ 5 ∧
    input.c.val < 2 ^ 240 ∧ input.d0.val < 2 ^ 9 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp)

  Witness := fieldPair
  extract := fun (gcfg, _) _ i₀ env =>
    (eval env (AssignedCell.of (i₀ + 2) 0 (gcfg.advices 4) : Var field Fp),
     eval env (AssignedCell.of (i₀ + 2) 1 (gcfg.advices 4) : Var field Fp))

  Spec := fun input _ (wit : Fp × Fp) =>
    input.a.val = bitrange input.ak.val 0 250 ∧
    input.b0.val = bitrange input.ak.val 250 4 ∧
    wit.1.val = bitrange input.ak.val 254 1 ∧
    input.b2.val = bitrange input.nk.val 0 5 ∧
    input.c.val = bitrange input.nk.val 5 240 ∧
    input.d0.val = bitrange input.nk.val 245 9 ∧
    wit.2.val = bitrange input.nk.val 254 1 ∧
    input.bWhole = input.b0 + wit.1 * 16 + input.b2 * 32 ∧
    input.dWhole = input.d0 + wit.2 * 512

  ProverAssumptions := fun input (wit : Fp × Fp) _ =>
    input.a.val = bitrange input.ak.val 0 250 ∧
    input.b0.val = bitrange input.ak.val 250 4 ∧
    wit.1.val = bitrange input.ak.val 254 1 ∧
    input.b2.val = bitrange input.nk.val 0 5 ∧
    input.c.val = bitrange input.nk.val 5 240 ∧
    input.d0.val = bitrange input.nk.val 245 9 ∧
    wit.2.val = bitrange input.nk.val 254 1 ∧
    input.bWhole = input.b0 + wit.1 * 16 + input.b2 * 32 ∧
    input.dWhole = input.d0 + wit.2 * 512

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, circuit_norm] at hc
    obtain ⟨hWCa, hWCb, hGate⟩ := hc
    subcircuit_rw at hWCa
    subcircuit_rw at hWCb
    -- the two witnessCheck children: telescoped decompositions of `a'` and `b2_c'`
    have hWSa := hWCa
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hWSa
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hWSa
    obtain ⟨hz0a, loA, hloA, htelA⟩ := hWSa
    have hWSb := hWCb
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hWSb
    simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hWSb
    obtain ⟨hz0b, loB, hloB, htelB⟩ := hWSb
    -- the gate child: discharge its rely-conditions, harvest the donor gate `Spec`
    rw [rangeCheckAt_output, rangeCheckAt_output] at hGate
    simp only [gateChild_assumptions_eq, gateChild_spec_eq, gateChild_extract_cells,
      circuit_norm] at hGate
    obtain ⟨hiak, hia, hib, hib0, hib2, hiz13a, hink, hic, hid, hid0, hiz13c⟩ := h_input
    rw [← hz0a] at htelA
    rw [← hz0b] at htelB
    have hGSpec := hGate trivial
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2.1,
       ⟨loA, hloA, htelA⟩, hA.2.2.2.2.2.2, ⟨loB, hloB, htelB⟩⟩
    simp only [CommitIvk.toDonor,
      CommitIvk.Gate.Spec] at hGSpec
    exact hGSpec

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, Operations.regionCount, circuit_norm,
      readCell] at hwit ⊢
    obtain ⟨⟨hWaP, hWrca⟩, ⟨hWbP, hWrcb⟩, hWgate⟩ := hwit
    subcircuit_rw
    -- replay both witnessCheck children's contracts for the gate child's preconditions
    obtain ⟨hCSa, hCPa⟩ := h_spec_0
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]; simp)
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hCSa
    rw [LookupRangeCheck.rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hCPa
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hCSa hCPa
    obtain ⟨hz0a, loA, hloA, htelA⟩ := hCSa
    obtain ⟨hz0aP, hzLastA⟩ := hCPa
    obtain ⟨hCSb, hCPb⟩ := h_spec_1
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]; simp)
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hCSb
    rw [LookupRangeCheck.rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hCPb
    simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hCSb hCPb
    obtain ⟨hz0b, loB, hloB, htelB⟩ := hCSb
    obtain ⟨hz0bP, hzLastB⟩ := hCPb
    obtain ⟨hiak, hia, hib, hib0, hib2, hiz13a, hink, hic, hid, hid0, hiz13c⟩ := h_input
    obtain ⟨hpa1, hpa2, hpa3, hpa4, hpa5, hpa6, hpa7, hpa8, hpa9⟩ := hPA
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, trivial, ?_, ?_⟩
    · rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]
      simp
    · rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]
      simp
    · -- the gate child's rely-conditions (verifier view)
      rw [rangeCheckAt_output, rangeCheckAt_output]
      simp only [gateChild_assumptions_eq, circuit_norm, hia, hib0, hib2, hic, hid0,
        hiz13a, hiz13c]
      exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2.1,
        ⟨loA, hloA, by rw [hz0a]; exact htelA⟩, hA.2.2.2.2.2.2,
        ⟨loB, hloB, by rw [hz0b]; exact htelB⟩⟩
    · -- the gate child's honest-prover precondition: tails + shifts + the donor `Spec`
      rw [rangeCheckAt_output, rangeCheckAt_output]
      simp only [gateChild_proverAssumptions_eq, gateChild_extract_cells, circuit_norm]
      rw [hiak, hia, hib, hib0, hib2, hiz13a, hink, hic, hid, hid0, hiz13c]
      rw [hia] at hWaP
      rw [hib2, hic] at hWbP
      refine ⟨?_, ?_, hWaP, by rw [hWbP]; ring, ?_⟩
      · -- `b_1 = 1` ⇒ `ak` canonical ⇒ `a < t_P` ⇒ the honest `z13_a'` tail vanishes
        intro h1
        rw [hzLastA, ← hz0aP, hWaP]
        obtain ⟨-, hatp, -⟩ := high_bit_canonical (ZMod.val_lt input_ak)
          (bit_one_of_val_eq hpa3 h1)
        rw [shifted_high_zero (by norm_num) (by norm_num) (by rw [hpa1]; exact hatp)]
        simp
      · -- `d_1 = 1` ⇒ `nk` canonical ⇒ `b_2 + 2⁵·c < t_P` ⇒ the honest tail vanishes
        intro h1
        rw [hzLastB, ← hz0bP, hWbP]
        have hbase_lt := base_val_lt_tP_val hpa4 hpa5 (ZMod.val_lt input_nk)
          (bit_one_of_val_eq hpa7 h1) (by norm_num)
        rw [shifted_high_zero (by norm_num) (by norm_num) hbase_lt]
        simp
      · -- the donor gate `Spec` at the witnessed `(b_1, d_1)` readings
        simp only [CommitIvk.toDonor, CommitIvk.Gate.Spec]
        exact ⟨hpa1, hpa2, hpa3, hpa4, hpa5, hpa6, hpa7, hpa8, hpa9⟩

derive_contract_bridges circuit (wb1 wd1 : WitgenIR Fp 1) := circuit wb1 wd1

end Canonicity

end Zcash.Circuits.CommitIvk
