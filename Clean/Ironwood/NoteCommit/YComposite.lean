import Clean.Ironwood.NoteCommit.Canonicity
import Clean.Ironwood.Utilities.LookupRangeCheck

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/note_commit.rs` — `y_canonicity` (lines 1962-2032):
`witness_short(y[1..10])` (`k_0`), `witness_short(y[250..254])` (`k_2`),
`witness_check(j, 25, true)` handing out `zs[1]`/`zs[13]`, `canon_bitshift_130(j)`
(`witness_check(j', 13, false)`), then the `"y canonicity"` gate region
(`YCanonicity::assign`, lines 1345-1409). Phase-1 donor:
`Halo2.Ironwood.NoteCommit.YCanonicity` (`Clean/Orchard/Action/NoteCommit.lean:525-646`).

Only the `lsb` witness program is a parameter (the caller computes it from its Sinsemilla
sign bit); `k_0`/`k_2`/`k_3` and `j` are witnessed by the canonical bit-slice programs, so
their honest values fall out of the parent's witness hypotheses. `Spec` is the donor
composite payoff (`lsb` is the low bit of `y`), conditioned on the lsb cell's booleanity
(constrained outside this flow, exactly as in the gate bundle).
-/

namespace Halo2.Ironwood.NoteCommit.YCanonicityCheck

open Halo2.Ironwood (Fp)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Halo2.Ironwood.Specs (bitrange bitrange_lt cast_bitrange_val)
open Halo2.Ironwood.NoteCommit (high_bit_canonical shifted_high_zero bit_one_of_val_eq
  IsLowBit isLowBit_iff_mod_two nat_mod_two_isBool tPNat)

/-! ## `witnessCheck`/short-check child bridges (`rfl`, children stay folded) -/

section ChildBridges

variable (n b : ℕ)

private theorem rangeCheckAt_spec_eq :
    (LookupRangeCheck.rangeCheckAt 10 n false).Spec
      = fun _ output (elt : Fp) =>
          output.z0 = elt ∧
          (∃ lo : ℕ, lo < 2 ^ (10 * n) ∧
            elt = (lo : Fp) + ((2 ^ (10 * n) : ℕ) : Fp) * output.zLast) ∧
          (false = true → output.zLast = 0 ∧ elt.val < 2 ^ (10 * n)) := rfl

private theorem rangeCheckAt_assumptions_eq :
    (LookupRangeCheck.rangeCheckAt 10 n false).Assumptions
      = fun _ => 2 ^ (10 * n) ≤ PALLAS_BASE_CARD ∧ 2 ^ 10 ≤ PALLAS_BASE_CARD := rfl

private theorem rangeCheckAt_envAssumptions_eq (cfg : LookupRangeCheck.Config 10)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.rangeCheckAt 10 n false).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded 10 cfg env.env ∧
          cfg.qLookup.index ≠ cfg.qRunning.index) := rfl

private theorem rangeCheckAt_proverAssumptions_eq :
    (LookupRangeCheck.rangeCheckAt 10 n false).ProverAssumptions
      = fun _ (elt : Fp) _ => (false = true → elt.val < 2 ^ (10 * n)) := rfl

private theorem rangeCheckAt_output (cfg : LookupRangeCheck.Config 10) (i : RegionIndex) :
    (LookupRangeCheck.rangeCheckAt 10 n false).output cfg 0 () i
      = { z0 := .of i 0 cfg.runningSum, zLast := .of i n cfg.runningSum } := by
  show ((LookupRangeCheck.rangeCheckAt 10 n false).synthesize cfg 0 ()).output i = _
  simp only [LookupRangeCheck.rangeCheckAt, circuit_norm, RegionCircuit.output_bind,
    output_cellAt, Bool.false_eq_true, if_false, Nat.zero_add]

private theorem rangeCheckAt_proverSpec_eq :
    (LookupRangeCheck.rangeCheckAt 10 n false).ProverSpec
      = fun _ output (elt : Fp) _ =>
          output.z0 = elt ∧
          output.zLast = ((elt.val / 2 ^ (10 * n) : ℕ) : Fp) := rfl

private theorem decomposed_spec_eq (h13 : 13 ≤ n) (hpow : 10 * n ≤ 254) :
    (LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).Spec
      = fun _ output (elt : Fp) =>
          output.z0 = elt ∧ elt.val < 2 ^ (10 * n) ∧
          output.z1.val = elt.val / 2 ^ 10 ∧ output.z13.val = elt.val / 2 ^ 130 := rfl

private theorem decomposed_assumptions_eq (h13 : 13 ≤ n) (hpow : 10 * n ≤ 254) :
    (LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).Assumptions = fun _ => True := rfl

private theorem decomposed_envAssumptions_eq (h13 : 13 ≤ n) (hpow : 10 * n ≤ 254)
    (cfg : LookupRangeCheck.Config 10) (env : Placed Environment Fp) :
    (LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded 10 cfg env.env ∧
          cfg.qLookup.index ≠ cfg.qRunning.index) := rfl

private theorem decomposed_proverAssumptions_eq (h13 : 13 ≤ n) (hpow : 10 * n ≤ 254) :
    (LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).ProverAssumptions
      = fun _ (elt : Fp) _ => elt.val < 2 ^ (10 * n) := rfl

private theorem decomposed_proverSpec_eq (h13 : 13 ≤ n) (hpow : 10 * n ≤ 254) :
    (LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).ProverSpec
      = fun _ output (elt : Fp) _ =>
          output.z0 = elt ∧ output.z1 = ((elt.val / 2 ^ 10 : ℕ) : Fp) ∧
          output.z13 = ((elt.val / 2 ^ 130 : ℕ) : Fp) := rfl

private theorem decomposed_output (h13 : 13 ≤ n) (hpow : 10 * n ≤ 254)
    (cfg : LookupRangeCheck.Config 10) (i : RegionIndex) :
    (LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).output cfg 0 () i
      = { z0 := .of i 0 cfg.runningSum, z1 := .of i 1 cfg.runningSum,
          z13 := .of i 13 cfg.runningSum } := by
  show ((LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).synthesize cfg 0 ()).output i
    = _
  simp only [LookupRangeCheck.rangeCheckAtDecomposed, circuit_norm,
    RegionCircuit.output_bind, output_cellAt, Nat.zero_add]

private theorem short_spec_eq :
    (LookupRangeCheck.shortRangeCheck 10 b).Spec
      = fun _ (out : Fp) _ => out.val < 2 ^ b := rfl

private theorem short_assumptions_eq :
    (LookupRangeCheck.shortRangeCheck 10 b).Assumptions
      = fun _ => b ≤ 10 ∧ 2 ^ 10 * 2 ^ 10 < PALLAS_BASE_CARD := rfl

private theorem short_envAssumptions_eq (cfg : LookupRangeCheck.Config 10)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.shortRangeCheck 10 b).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded 10 cfg env.env ∧
          cfg.qLookup.index ≠ cfg.qRunning.index) := rfl

private theorem short_proverAssumptions_eq :
    (LookupRangeCheck.shortRangeCheck 10 b).ProverAssumptions
      = fun _ (wit : Fp) _ => wit.val < 2 ^ b := rfl

private theorem short_output (cfg : LookupRangeCheck.Config 10) (i : RegionIndex) :
    (LookupRangeCheck.shortRangeCheck 10 b).output cfg 0 () i
      = .of i 0 cfg.runningSum := by
  show ((LookupRangeCheck.shortRangeCheck 10 b).synthesize cfg 0 ()).output i = _
  simp only [LookupRangeCheck.shortRangeCheck, circuit_norm, RegionCircuit.output_bind,
    output_cellAt, Nat.zero_add]

private theorem short_extract_eq (cfg : LookupRangeCheck.Config 10) (i : RegionIndex)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.shortRangeCheck 10 b).extract cfg 0 () i env
      = env.env.advice cfg.runningSum ((env.place i : ℕ) : ℤ) := by
  show eval env (AssignedCell.of i 0 cfg.runningSum : Var field Fp) = _
  simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_zero]

private theorem decomposed_extract_eq (h13 : 13 ≤ n) (hpow : 10 * n ≤ 254)
    (cfg : LookupRangeCheck.Config 10) (i : RegionIndex) (env : Placed Environment Fp) :
    (LookupRangeCheck.rangeCheckAtDecomposed n h13 hpow).extract cfg 0 () i env
      = env.env.advice cfg.runningSum ((env.place i : ℕ) : ℤ) := by
  show eval env (AssignedCell.of i 0 cfg.runningSum : Var field Fp) = _
  simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice, Nat.add_zero]

end ChildBridges

/-- The composite input: the `y` cell. -/
structure Inputs (F : Type) where
  y : F
deriving ProvableStruct

/-- `k_0 = y[1..10]` (Rust `RangeConstrained::witness_short`, computed from `y`). -/
def k0Wit (y : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (readCell env y).val 1 9 : ℕ) : Fp)]

@[circuit_norm]
theorem k0Wit_eval (y : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((k0Wit y).eval env)[j] = ((bitrange (readCell env y).val 1 9 : ℕ) : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [k0Wit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- `k_2 = y[250..254]`. -/
def k2Wit (y : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (readCell env y).val 250 4 : ℕ) : Fp)]

@[circuit_norm]
theorem k2Wit_eval (y : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((k2Wit y).eval env)[j] = ((bitrange (readCell env y).val 250 4 : ℕ) : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [k2Wit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- `k_3 = y[254..255]` (witnessed inside the gate region). -/
def k3Wit (y : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[((bitrange (readCell env y).val 254 1 : ℕ) : Fp)]

@[circuit_norm]
theorem k3Wit_eval (y : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((k3Wit y).eval env)[j] = ((bitrange (readCell env y).val 254 1 : ℕ) : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [k3Wit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- `j = LSB + 2·k_0 + 2¹⁰·k_1` (Rust computes it from the `lsb`/`k_0`/`k_1` values;
`k_1 = y[10..250]`). -/
def jWit (wlsb : WitgenIR Fp 1) (y : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[(wlsb.eval env)[0] + ((bitrange (readCell env y).val 1 9 : ℕ) : Fp) * 2
      + ((bitrange (readCell env y).val 10 240 : ℕ) : Fp) * (1024 : Fp)]

@[circuit_norm]
theorem jWit_eval (wlsb : WitgenIR Fp 1) (y : AssignedCell Fp)
    (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((jWit wlsb y).eval env)[j]
      = (wlsb.eval env)[0] + ((bitrange (readCell env y).val 1 9 : ℕ) : Fp) * 2
        + ((bitrange (readCell env y).val 10 240 : ℕ) : Fp) * (1024 : Fp) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [jWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- `j' = j + 2¹³⁰ − t_P` (Rust `canon_bitshift_130`, computed from the `j` cell). -/
def jPrimeWit (jCell : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env jCell + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP]

@[circuit_norm]
theorem jPrimeWit_eval (jCell : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((jPrimeWit jCell).eval env)[j]
      = readCell env jCell + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [jPrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The gate child: the `YCanonicity` region bundle in its own layouter region, with the
canonical `k_3` program. -/
def gateChild (wlsb : WitgenIR Fp 1) (input : Inputs (AssignedCell Fp)) :
    FormalCircuit Fp YCanonicity.Config YCanonicity.Config YCanonicity.Row field :=
  (YCanonicity.bundle wlsb (k3Wit input.y)).toFormal "y canonicity"

private theorem gateChild_spec_eq (wlsb : WitgenIR Fp 1) (input : Inputs (AssignedCell Fp)) :
    (gateChild wlsb input).Spec = fun row (out : Fp) (wit : Fp × Fp) =>
      out = wit.1 ∧ (IsBool out →
        Halo2.Ironwood.NoteCommit.YCanonicity.Gate.Spec
          (YCanonicity.toDonor row out wit.2)) := rfl

private theorem gateChild_assumptions_eq (wlsb : WitgenIR Fp 1)
    (input : Inputs (AssignedCell Fp)) :
    (gateChild wlsb input).Assumptions = fun row =>
      row.j.val < 2 ^ 250 ∧ row.k0.val < 2 ^ 9 ∧ row.k2.val < 2 ^ 4 ∧
      row.z1J.val = row.j.val / 2 ^ 10 ∧
      row.z13J.val = row.j.val / 2 ^ 130 ∧
      ∃ lo : ℕ, lo < 2 ^ 130 ∧
        row.jPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * row.z13JPrime := rfl

private theorem gateChild_proverAssumptions_eq (wlsb : WitgenIR Fp 1)
    (input : Inputs (AssignedCell Fp)) :
    (gateChild wlsb input).ProverAssumptions = fun row (wit : Fp × Fp) _ =>
      IsBool wit.1 ∧
      Halo2.Ironwood.NoteCommit.YCanonicity.Gate.Spec
        (YCanonicity.toDonor row wit.1 wit.2) ∧
      row.jPrime = row.j + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP := rfl

private theorem gateChild_output (wlsb : WitgenIR Fp 1) (input : Inputs (AssignedCell Fp))
    (cfg : YCanonicity.Config) (row : Var YCanonicity.Row Fp) (i : RegionIndex) :
    (gateChild wlsb input).output cfg row i
      = AssignedCell.of i 0 (cfg.advices 6) := by
  show ((YCanonicity.bundle wlsb (k3Wit input.y)).synthesize cfg 0 row).output i = _
  simp only [YCanonicity.bundle, circuit_norm, RegionCircuit.output_bind, Nat.zero_add]

theorem gateChild_call_witnesses (wlsb : WitgenIR Fp 1)
    (input : Inputs (AssignedCell Fp)) (cfg : YCanonicity.Config)
    (row : Var YCanonicity.Row Fp) (i : RegionIndex) (place : RegionIndex → ℕ)
    (env : ProverEnvironment Fp) :
    ExtendsWitnesses place env (((gateChild wlsb input).call cfg row).operations i) i
      = RegionOperations.ExtendsWitnesses place i env
          (((YCanonicity.bundle wlsb (k3Wit input.y)).synthesize cfg 0 row).operations i)
 :=
  FormalRegionCircuit.toFormal_call_extendsWitnesses _ _ cfg row i place env

private theorem gateChild_extract_eq (wlsb : WitgenIR Fp 1)
    (input : Inputs (AssignedCell Fp)) (cfg : YCanonicity.Config)
    (row : Var YCanonicity.Row Fp) (i : RegionIndex) (env : Placed Environment Fp) :
    (gateChild wlsb input).extract cfg row i env
      = (eval env (AssignedCell.of i 0 (cfg.advices 6) : Var field Fp),
         eval env (AssignedCell.of i 0 (cfg.advices 9) : Var field Fp)) := rfl

def synth (wlsb : WitgenIR Fp 1) (gcfg : YCanonicity.Config)
    (lcfg : LookupRangeCheck.Config 10) (input : Inputs (AssignedCell Fp)) :
    Circuit Fp (Var field Fp) := do
  let k0 ← LookupRangeCheck.witnessShortCheck 10 9 lcfg (k0Wit input.y)
  let k2 ← LookupRangeCheck.witnessShortCheck 10 4 lcfg (k2Wit input.y)
  let jZs ← LookupRangeCheck.witnessCheckDecomposed lcfg (jWit wlsb input.y)
  let jpZs ← LookupRangeCheck.witnessCheck 10 13 false lcfg (jPrimeWit jZs.z0)
  (gateChild wlsb input).call gcfg
    { y := input.y, k0 := k0, k2 := k2, j := jZs.z0, z1J := jZs.z1, z13J := jZs.z13,
      jPrime := jpZs.z0, z13JPrime := jpZs.zLast }

theorem synth_regionCount (wlsb : WitgenIR Fp 1) (gcfg : YCanonicity.Config)
    (lcfg : LookupRangeCheck.Config 10) (input : Inputs (AssignedCell Fp))
    (i : RegionIndex) :
    Operations.regionCount ((synth wlsb gcfg lcfg input).operations i) = 5 := by
  simp only [synth, LookupRangeCheck.witnessShortCheck, LookupRangeCheck.witnessCheck,
    LookupRangeCheck.witnessCheckDecomposed, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]
  rw [FormalCircuit.call_regionCount]
  rfl

set_option maxRecDepth 4096 in
/-- Rust `y_canonicity` (`note_commit.rs:1962-2032`). Output is the witnessed `lsb` cell;
its reading is the extraction data. `Spec`: given the lsb cell's booleanity (constrained
outside, by the decompose gates on the copied cell), `lsb` is the low bit of `y` — the
donor composite payoff. -/
def circuit (wlsb : WitgenIR Fp 1) :
    FormalCircuit Fp (YCanonicity.Config × LookupRangeCheck.Config 10)
      (YCanonicity.Config × LookupRangeCheck.Config 10) Inputs field where
  name := "y canonicity"
  configure := pure

  synthesize := fun (gcfg, lcfg) input => synth wlsb gcfg lcfg input

  elaborated := fun (gcfg, lcfg) =>
    { output := fun input i => .of (i + 4) 0 (gcfg.advices 6)
      regionCount := fun _ => 5
      output_eq := by
        intro input i
        simp only [synth, LookupRangeCheck.witnessShortCheck, LookupRangeCheck.witnessCheck,
          LookupRangeCheck.witnessCheckDecomposed, circuit_norm]
        rfl
      regionCount_eq := fun input i => (synth_regionCount wlsb gcfg lcfg input i).symm }

  EnvAssumptions := fun (_, lcfg) env =>
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions _ := True

  Witness := field
  extract := fun (gcfg, _) _ i₀ env =>
    eval env (AssignedCell.of (i₀ + 4) 0 (gcfg.advices 6) : Var field Fp)

  Spec := fun input (out : Fp) (wit : Fp) =>
    out = wit ∧ (IsBool out → IsLowBit input.y out)

  ProverAssumptions := fun input (wit : Fp) _ => IsLowBit input.y wit

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [synth, LookupRangeCheck.witnessShortCheck, LookupRangeCheck.witnessCheck,
      LookupRangeCheck.witnessCheckDecomposed, circuit_norm] at hc
    obtain ⟨hK0, hK2, hDec, hJp, hGate⟩ := hc
    subcircuit_rw at hK0
    subcircuit_rw at hK2
    subcircuit_rw at hDec
    subcircuit_rw at hJp
    subcircuit_rw at hGate
    -- the four lookup children
    have hK0S := hK0 (by rw [short_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [short_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [short_spec_eq, short_output] at hK0S
    simp only [circuit_norm] at hK0S
    have hK2S := hK2 (by rw [short_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [short_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [short_spec_eq, short_output] at hK2S
    simp only [circuit_norm] at hK2S
    have hDecS := hDec (by rw [decomposed_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [decomposed_assumptions_eq]; trivial)
    rw [decomposed_spec_eq, decomposed_output] at hDecS
    simp only [circuit_norm, show (10 * 25 : ℕ) = 250 from by norm_num] at hDecS
    obtain ⟨hjz0, hjlt, hz1v, hz13v⟩ := hDecS
    have hJpS := hJp (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hJpS
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hJpS
    obtain ⟨hpz0, lo, hlo, htel⟩ := hJpS
    -- the gate child
    rw [FormalRegionCircuit.output_call, FormalRegionCircuit.output_call,
      decomposed_output, rangeCheckAt_output] at hGate
    simp only [gateChild_assumptions_eq, gateChild_spec_eq, gateChild_extract_eq,
      gateChild_output, circuit_norm] at hGate
    have hGSpec := hGate trivial
      ⟨by rw [hjz0]; exact hjlt, hK0S, hK2S,
       by rw [hjz0]; exact hz1v, by rw [hjz0]; exact hz13v,
       lo, hlo, by rw [hpz0]; exact htel⟩
    rw [show (i₀ + 2 + 2 : ℕ) = i₀ + 4 from rfl] at hGSpec
    refine ⟨trivial, fun hb => ?_⟩
    have hb' : IsBool (env.advice (cfg.1.advices 6) ((place (i₀ + 4) : ℕ) : ℤ)) := by
      rw [← h_output] at hb; exact hb
    have hD := hGSpec hb'
    simp only [YCanonicity.toDonor, Halo2.Ironwood.NoteCommit.YCanonicity.Gate.Spec]
      at hD
    rw [h_input] at hD
    rw [← h_output]
    exact hD.1

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [synth, LookupRangeCheck.witnessShortCheck, LookupRangeCheck.witnessCheck,
      LookupRangeCheck.witnessCheckDecomposed, circuit_norm, readCell] at hwit ⊢
    obtain ⟨⟨hWk0, hWk0rc⟩, ⟨hWk2, hWk2rc⟩, ⟨hWj, hWjrc⟩, ⟨hWjp, hWjprc⟩, hWgate⟩ := hwit
    subcircuit_rw
    -- the gate region's own witnesses (the `lsb`/`k_3` cells): project the call's single
    -- region chunk (defeq) and destructure it like the bundle's own completeness
    rw [gateChild_call_witnesses] at hWgate
    have hWgate' := hWgate
    simp only [YCanonicity.bundle, YCanonicity.gate, circuit_norm, readCell] at hWgate'
    obtain ⟨hgy, hglsb, hgk0, hgk2, hgk3, hgj, hgz1, hgz13, hgjp, hgz13p⟩ := hWgate'
    rw [h_input] at hWk0 hWk2 hWj hgk3
    rw [FormalRegionCircuit.output_call, decomposed_output] at hWjp
    simp only [circuit_norm, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
      Cell.of_column, Environment.get_advice] at hWjp
    -- the honest short-check values are genuine bit slices
    have hk0lt : (env.advice cfg.2.runningSum ((place i₀ : ℕ) : ℤ)).val < 2 ^ 9 := by
      rw [hWk0, cast_bitrange_val (by norm_num)]
      exact bitrange_lt _ _ _
    have hk0E : (show Fp from (LookupRangeCheck.shortRangeCheck 10 9).extract cfg.2 0 () i₀
        ({ place := place, env := env } : Placed ProverEnvironment Fp).toEnvironment).val
        < 2 ^ 9 := by
      rw [short_extract_eq]
      exact hk0lt
    have hk2lt : (env.advice cfg.2.runningSum ((place (i₀ + 1) : ℕ) : ℤ)).val < 2 ^ 4 := by
      rw [hWk2, cast_bitrange_val (by norm_num)]
      exact bitrange_lt _ _ _
    have hk2E : (show Fp from (LookupRangeCheck.shortRangeCheck 10 4).extract cfg.2 0 ()
        (i₀ + 1)
        ({ place := place, env := env } : Placed ProverEnvironment Fp).toEnvironment).val
        < 2 ^ 4 := by
      rw [short_extract_eq]
      exact hk2lt
    -- `lsb` is the low bit of `y` (the honest-prover precondition, on the witnessed cell)
    have hPA' : IsLowBit input_y
        (env.advice (cfg.1.advices 6) ((place (i₀ + 4) : ℕ) : ℤ)) := hPA
    have hlsb : env.advice (cfg.1.advices 6) ((place (i₀ + 4) : ℕ) : ℤ)
        = ((bitrange input_y.val 0 1 : ℕ) : Fp) := by
      rw [isLowBit_iff_mod_two.mp hPA',
        show bitrange input_y.val 0 1 = input_y.val % 2 from by simp [bitrange]]
    have htile : bitrange input_y.val 0 250
        = bitrange input_y.val 0 1 + 2 * bitrange input_y.val 1 9
          + 2 ^ 10 * bitrange input_y.val 10 240 := by
      rw [show (250 : ℕ) = 1 + 249 from rfl, Halo2.Ironwood.Specs.bitrange_add,
        show (249 : ℕ) = 9 + 240 from rfl, Halo2.Ironwood.Specs.bitrange_add]
      ring
    -- the honest `j` is the low 250 bits of `y`
    have hjeq : env.advice cfg.2.runningSum ((place (i₀ + 2) : ℕ) : ℤ)
        = ((bitrange input_y.val 0 250 : ℕ) : Fp) := by
      rw [hWj, ← hglsb, hlsb, htile]
      push_cast
      ring
    have hjval : (env.advice cfg.2.runningSum ((place (i₀ + 2) : ℕ) : ℤ)).val
        = bitrange input_y.val 0 250 := by
      rw [hjeq]
      exact cast_bitrange_val (by norm_num) _
    have hjlt : (env.advice cfg.2.runningSum ((place (i₀ + 2) : ℕ) : ℤ)).val
        < 2 ^ 250 := by
      rw [hjval]; exact bitrange_lt _ _ _
    have hjE : (show Fp from (LookupRangeCheck.rangeCheckAtDecomposed 25
          LookupRangeCheck.witnessCheckDecomposed._proof_1
          LookupRangeCheck.witnessCheckDecomposed._proof_2).extract cfg.2 0 () (i₀ + 2)
        ({ place := place, env := env } : Placed ProverEnvironment Fp).toEnvironment).val
        < 2 ^ (10 * 25) := by
      rw [decomposed_extract_eq]
      simp only [show (10 * 25 : ℕ) = 250 from by norm_num]
      exact hjlt
    -- replay the children contracts needed by the gate child
    obtain ⟨hK0S, -⟩ := h_spec_0
      (by rw [short_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [short_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [short_proverAssumptions_eq]; exact hk0E)
    rw [short_spec_eq, short_output] at hK0S
    simp only [circuit_norm] at hK0S
    obtain ⟨hK2S, -⟩ := h_spec_1
      (by rw [short_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [short_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [short_proverAssumptions_eq]; exact hk2E)
    rw [short_spec_eq, short_output] at hK2S
    simp only [circuit_norm] at hK2S
    obtain ⟨hDecS, hDecPS⟩ := h_spec_2
      (by rw [decomposed_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [decomposed_assumptions_eq]; trivial)
      (by rw [decomposed_proverAssumptions_eq]; exact hjE)
    rw [decomposed_spec_eq, decomposed_output] at hDecS
    simp only [circuit_norm, show (10 * 25 : ℕ) = 250 from by norm_num] at hDecS
    obtain ⟨hjz0, hjlt', hz1v, hz13v⟩ := hDecS
    obtain ⟨hJpS, hJpPS⟩ := h_spec_3
      (by rw [rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [rangeCheckAt_proverAssumptions_eq]; simp)
    rw [rangeCheckAt_spec_eq, rangeCheckAt_output] at hJpS
    rw [rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hJpPS
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hJpS hJpPS
    obtain ⟨hpz0, lo, hlo, htel⟩ := hJpS
    obtain ⟨hpz0P, hzLastP⟩ := hJpPS
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, trivial, ?_, ?_⟩
    · rw [short_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [short_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [short_proverAssumptions_eq]
      exact hk0E
    · rw [short_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [short_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [short_proverAssumptions_eq]
      exact hk2E
    · rw [decomposed_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [decomposed_assumptions_eq]
      trivial
    · rw [decomposed_proverAssumptions_eq]
      exact hjE
    · rw [rangeCheckAt_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [rangeCheckAt_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [rangeCheckAt_proverAssumptions_eq]
      simp
    · -- the gate child's rely-conditions (verifier view)
      rw [FormalRegionCircuit.output_call, FormalRegionCircuit.output_call,
        decomposed_output, rangeCheckAt_output]
      simp only [gateChild_assumptions_eq, circuit_norm]
      exact ⟨by rw [hjz0]; exact hjlt', hK0S, hK2S,
        by rw [hjz0]; exact hz1v, by rw [hjz0]; exact hz13v,
        lo, hlo, by rw [hpz0]; exact htel⟩
    · -- the gate child's honest-prover precondition
      rw [FormalRegionCircuit.output_call, FormalRegionCircuit.output_call,
        decomposed_output, rangeCheckAt_output]
      simp only [gateChild_proverAssumptions_eq, gateChild_extract_eq, circuit_norm]
      rw [h_input]
      refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hWjp⟩
      · -- `IsBool lsb`
        rw [hlsb, show ((bitrange input_y.val 0 1 : ℕ) : Fp)
            = ((input_y.val % 2 : ℕ) : Fp) from by
          rw [show bitrange input_y.val 0 1 = input_y.val % 2 from by simp [bitrange]]]
        exact nat_mod_two_isBool _
      · -- `IsLowBit y lsb`
        exact hPA'
      · -- `j` slice
        exact hjval
      · -- `k_0` slice
        rw [hWk0]
        exact cast_bitrange_val (by norm_num) _
      · -- `k_2` slice
        rw [hWk2]
        exact cast_bitrange_val (by norm_num) _
      · -- `k_3` slice
        rw [hgk3]
        exact cast_bitrange_val (by norm_num) _
      · -- `k_3 = 1 → z13_j' = 0`
        simp only [YCanonicity.toDonor]
        intro h1
        rw [show (i₀ + 2 + 2 : ℕ) = i₀ + 4 from rfl, hgk3] at h1
        rw [hzLastP, ← hpz0P, hWjp, hjeq]
        obtain ⟨-, hatp, -⟩ := high_bit_canonical (ZMod.val_lt input_y)
          (Halo2.Ironwood.NoteCommit.bit_one_of_eq rfl h1)
        rw [shifted_high_zero (by norm_num) (by norm_num)
          (by rw [cast_bitrange_val (by norm_num)]; exact hatp)]
        simp

end Halo2.Ironwood.NoteCommit.YCanonicityCheck
