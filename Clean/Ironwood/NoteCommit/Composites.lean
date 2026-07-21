import Clean.Ironwood.NoteCommit.Canonicity
import Clean.Ironwood.Utilities.LookupRangeCheck

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/note_commit.rs` — the per-input canonicity flows:
- `canon_bitshift_130` (lines 1804-1835): `lookup_config.witness_check(a', 13, false)` in
  its own `"Witness element"` region, witnessing `a' = a + 2^130 - t_P`.
- the gate regions (`"NoteCommit input g_d"` etc.): the per-input canonicity gates, one
  region each.
Phase-1 donors: `Clean/Orchard/Action/NoteCommit.lean`
(`NoteCommit.{Gd,Pkd,Rho,Psi}Canonicity` — Telescoped copy-check + gate).

Each composite is a two-child layouter `FormalCircuit`: the `witnessCheck` child pins the
shifted value's telescoped decomposition (the gate bundle's `∃ lo` rely-condition), the
gate bundle carries the semantic canonicity contract, and the shift equation itself is
the gate's own constraint (derived inside the gate bundle's soundness). `Spec` is the
donor composite's bit-slice payoff.
-/

namespace Halo2.Ironwood.NoteCommit

open Halo2.Ironwood (Fp)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Halo2.Ironwood.Specs (bitrange)
open Halo2.Ironwood.NoteCommit (high_bit_canonical shifted_high_zero bit_one_of_val_eq
  base_val_lt_tP_val tPNat)

section WitnessCheckBridges

variable (n : ℕ)

private theorem rangeCheckAt_output (cfg : LookupRangeCheck.Config 10) (i : RegionIndex) :
    (LookupRangeCheck.rangeCheckAt 10 n false).output cfg 0 () i
      = { z0 := .of i 0 cfg.runningSum, zLast := .of i n cfg.runningSum } := by
  show ((LookupRangeCheck.rangeCheckAt 10 n false).synthesize cfg 0 ()).output i = _
  simp only [LookupRangeCheck.rangeCheckAt, circuit_norm, RegionCircuit.output_bind,
    output_cellAt, Bool.false_eq_true, if_false, Nat.zero_add]

end WitnessCheckBridges

/-! ## `x(g_d)` canonicity (`gd_x_canonicity`, `note_commit.rs:1804-1835` + the
`"NoteCommit input g_d"` gate region) -/

namespace GdCanonicityCheck

/-- The composite inputs: the point coordinate, the subpiece cells (the `b1` bit cell is
the one witnessed by `DecomposeB`), and the 13-word Sinsemilla running-sum tail of `a`. -/
structure Inputs (F : Type) where
  gdX : F
  b0 : F
  b1 : F
  a : F
  z13A : F
deriving ProvableStruct

/-- The `a' = a + 2¹³⁰ − t_P` witness program (Rust `canon_bitshift_130`, computed from
`a`'s value). -/
def aPrimeWit (a : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env a + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP]

@[circuit_norm]
theorem aPrimeWit_eval (a : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((aPrimeWit a).eval env)[j] = readCell env a + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [aPrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The gate child: the `GdCanonicity` region bundle in its own layouter region. -/
def gateChild : FormalCircuit Fp GdCanonicity.Config GdCanonicity.Config GdCanonicity.Row unit :=
  GdCanonicity.bundle.toFormal "NoteCommit input g_d"

derive_contract_bridges gateChild := gateChild

/-- The synthesize body (Rust `gd_x_canonicity` flow): the `witness_check` of `a'`, then
the gate region with `a' = z_0` and `z13_a' = z_13` wired in. -/
def synth (gcfg : GdCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) : Circuit Fp Unit := do
  let aZs ← LookupRangeCheck.witnessCheck 10 13 false lcfg (aPrimeWit input.a)
  let _ ← gateChild.call gcfg
    { gdX := input.gdX, b0 := input.b0, b1 := input.b1, a := input.a,
      aPrime := aZs.z0, z13A := input.z13A, z13APrime := aZs.zLast }
  pure ()

/-- The region count of `synth`: the `witnessCheck` region and the gate child's region. -/
theorem synth_regionCount (gcfg : GdCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) (i : RegionIndex) :
    Operations.regionCount ((synth gcfg lcfg input).operations i) = 2 := by
  simp only [synth, LookupRangeCheck.witnessCheck, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

/-- Rust `gd_x_canonicity` (`note_commit.rs`): `witness_check(a', 13)` then the
`"NoteCommit input g_d"` gate region. `Spec` is the donor composite payoff:
`a`/`b0`/`b1` are the canonical bit slices of `x(g_d)`. -/
def circuit :
    FormalCircuit Fp (GdCanonicity.Config × LookupRangeCheck.Config 10)
      (GdCanonicity.Config × LookupRangeCheck.Config 10) Inputs unit where
  name := "NoteCommit input g_d (canonicity)"
  configure := pure

  synthesize := fun (gcfg, lcfg) input => synth gcfg lcfg input

  elaborated := fun (gcfg, lcfg) =>
    { output := fun _ _ => ()
      regionCount := fun _ => 2
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synth_regionCount gcfg lcfg input i).symm }

  EnvAssumptions := fun (_, lcfg) env =>
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions input :=
    IsBool input.b1 ∧ input.a.val < 2 ^ 250 ∧ input.b0.val < 2 ^ 4 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp)

  Spec input _ _ :=
    input.a.val = bitrange input.gdX.val 0 250 ∧
    input.b0.val = bitrange input.gdX.val 250 4 ∧
    input.b1.val = bitrange input.gdX.val 254 1

  ProverAssumptions input _ _ :=
    input.a.val = bitrange input.gdX.val 0 250 ∧
    input.b0.val = bitrange input.gdX.val 250 4 ∧
    input.b1.val = bitrange input.gdX.val 254 1

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, circuit_norm] at hc
    obtain ⟨hWC, hGate⟩ := hc
    subcircuit_rw at hWC
    -- the witnessCheck child: `z_0 = a'`-cell and the 130-bit telescoped decomposition
    have hWSpec := hWC
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hWSpec
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hWSpec
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hWSpec
    -- the gate child: discharge its rely-conditions, harvest the donor gate `Spec`
    rw [FormalRegionCircuit.output_call, rangeCheckAt_output] at hGate
    simp only [gateChild_assumptions_eq, gateChild_spec_eq, circuit_norm] at hGate
    have hGSpec := hGate trivial
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    simp only [GdCanonicity.toDonor, Halo2.Ironwood.NoteCommit.GdCanonicity.Gate.Spec] at hGSpec
    exact ⟨hGSpec.1, hGSpec.2.1, hGSpec.2.2.1⟩

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, Operations.regionCount, circuit_norm,
      readCell] at hwit ⊢
    obtain ⟨⟨hWaP, hWrc⟩, hWgate⟩ := hwit
    subcircuit_rw
    -- replay the witnessCheck child's contract for the gate child's preconditions
    obtain ⟨hChildSpec, hChildPS⟩ := h_spec_0
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]; simp)
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hChildSpec
    rw [LookupRangeCheck.rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hChildPS
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num]
      at hChildSpec hChildPS
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hChildSpec
    obtain ⟨hz0eqP, hzLast⟩ := hChildPS
    refine ⟨⟨?_, ?_, ?_⟩, trivial, ?_, ?_⟩
    · rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]
      simp
    · -- the gate child's rely-conditions (verifier view)
      rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_assumptions_eq, circuit_norm, h_input]
      exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    · -- the gate child's honest-prover precondition: the donor gate `Spec` + the shift
      rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_proverAssumptions_eq, circuit_norm]
      rw [h_input.2.2.2.1] at hWaP
      rw [h_input.1, h_input.2.1, h_input.2.2.1, h_input.2.2.2.1, h_input.2.2.2.2]
      simp only [GdCanonicity.toDonor, Halo2.Ironwood.NoteCommit.GdCanonicity.Gate.Spec]
      refine ⟨⟨hPA.1, hPA.2.1, hPA.2.2, ?_⟩, hWaP⟩
      -- honest tail of `a' = a + 2^130 - t_P`: with the top bit set, `a < t_P`, so the
      -- 130-bit shift stays below `2^130` and the running-sum tail vanishes
      intro h1
      rw [hzLast, ← hz0eqP, hWaP]
      obtain ⟨-, hatp, -⟩ := high_bit_canonical (ZMod.val_lt input_gdX)
        (bit_one_of_val_eq hPA.2.2 h1)
      rw [shifted_high_zero (by norm_num) (by norm_num) (by rw [hPA.1]; exact hatp)]
      simp

end GdCanonicityCheck

/-! ## `x(pk_d)` canonicity (`pkd_x_canonicity`, `note_commit.rs:1838-1876` + the
`"NoteCommit input pk_d"` gate region) -/

namespace PkdCanonicityCheck

structure Inputs (F : Type) where
  pkdX : F
  b3 : F
  c : F
  d0 : F
  z13C : F
deriving ProvableStruct

/-- The shifted-value witness program (Rust computes it from the pieces' values). -/
def b3CPrimeWit (b3 c : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env b3 + ((2 ^ 4 : ℕ) : Fp) * readCell env c + ((2 ^ 140 : ℕ) : Fp) - Halo2.Ironwood.tP]

@[circuit_norm]
theorem b3CPrimeWit_eval (b3 c : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((b3CPrimeWit b3 c).eval env)[j] = readCell env b3 + ((2 ^ 4 : ℕ) : Fp) * readCell env c + ((2 ^ 140 : ℕ) : Fp) - Halo2.Ironwood.tP := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [b3CPrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The gate child: the `PkdCanonicity` region bundle in its own layouter region. -/
def gateChild : FormalCircuit Fp PkdCanonicity.Config PkdCanonicity.Config PkdCanonicity.Row unit :=
  PkdCanonicity.bundle.toFormal "NoteCommit input pk_d"

derive_contract_bridges gateChild := gateChild

def synth (gcfg : PkdCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) : Circuit Fp Unit := do
  let zs ← LookupRangeCheck.witnessCheck 10 14 false lcfg (b3CPrimeWit input.b3 input.c)
  let _ ← gateChild.call gcfg
    { pkdX := input.pkdX, b3 := input.b3, d0 := input.d0, c := input.c,
      b3CPrime := zs.z0, z13C := input.z13C, z14B3CPrime := zs.zLast }
  pure ()

theorem synth_regionCount (gcfg : PkdCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) (i : RegionIndex) :
    Operations.regionCount ((synth gcfg lcfg input).operations i) = 2 := by
  simp only [synth, LookupRangeCheck.witnessCheck, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

def circuit :
    FormalCircuit Fp (PkdCanonicity.Config × LookupRangeCheck.Config 10)
      (PkdCanonicity.Config × LookupRangeCheck.Config 10) Inputs unit where
  name := "NoteCommit input pk_d (canonicity)"
  configure := pure

  synthesize := fun (gcfg, lcfg) input => synth gcfg lcfg input

  elaborated := fun (gcfg, lcfg) =>
    { output := fun _ _ => ()
      regionCount := fun _ => 2
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synth_regionCount gcfg lcfg input i).symm }

  EnvAssumptions := fun (_, lcfg) env =>
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions input :=
    IsBool input.d0 ∧ input.c.val < 2 ^ 250 ∧ input.b3.val < 2 ^ 4 ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp)

  Spec input _ _ :=
    input.b3.val = bitrange input.pkdX.val 0 4 ∧
    input.c.val = bitrange input.pkdX.val 4 250 ∧
    input.d0.val = bitrange input.pkdX.val 254 1

  ProverAssumptions input _ _ :=
    input.b3.val = bitrange input.pkdX.val 0 4 ∧
    input.c.val = bitrange input.pkdX.val 4 250 ∧
    input.d0.val = bitrange input.pkdX.val 254 1

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, circuit_norm] at hc
    obtain ⟨hWC, hGate⟩ := hc
    subcircuit_rw at hWC
    have hWSpec := hWC
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hWSpec
    simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hWSpec
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hWSpec
    rw [FormalRegionCircuit.output_call, rangeCheckAt_output] at hGate
    simp only [gateChild_assumptions_eq, gateChild_spec_eq, circuit_norm] at hGate
    have hGSpec := hGate trivial
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    simp only [PkdCanonicity.toDonor, Halo2.Ironwood.NoteCommit.PkdCanonicity.Gate.Spec] at hGSpec
    exact ⟨hGSpec.1, hGSpec.2.1, hGSpec.2.2.1⟩

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, Operations.regionCount, circuit_norm,
      readCell] at hwit ⊢
    obtain ⟨⟨hWaP, hWrc⟩, hWgate⟩ := hwit
    subcircuit_rw
    obtain ⟨hChildSpec, hChildPS⟩ := h_spec_0
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]; simp)
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hChildSpec
    rw [LookupRangeCheck.rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hChildPS
    simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num]
      at hChildSpec hChildPS
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hChildSpec
    obtain ⟨hz0eqP, hzLast⟩ := hChildPS
    refine ⟨⟨?_, ?_, ?_⟩, trivial, ?_, ?_⟩
    · rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]
      simp
    · rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_assumptions_eq, circuit_norm, h_input]
      exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    · rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_proverAssumptions_eq, circuit_norm]
      rw [h_input.2.1, h_input.2.2.1] at hWaP
      rw [h_input.1, h_input.2.1, h_input.2.2.1, h_input.2.2.2.1, h_input.2.2.2.2]
      simp only [PkdCanonicity.toDonor, Halo2.Ironwood.NoteCommit.PkdCanonicity.Gate.Spec]
      refine ⟨⟨hPA.1, hPA.2.1, hPA.2.2, ?_⟩, by rw [hWaP]; ring⟩
      intro h1
      rw [hzLast, ← hz0eqP, hWaP]
      have hbase_lt := base_val_lt_tP_val hPA.1 hPA.2.1 (ZMod.val_lt input_pkdX)
        (bit_one_of_val_eq hPA.2.2 h1) (by norm_num)
      rw [shifted_high_zero (by norm_num) (by norm_num) hbase_lt]
      simp

end PkdCanonicityCheck

/-! ## `rho` canonicity (`rho_canonicity`, `note_commit.rs:1879-1917` + the
`"NoteCommit input rho"` gate region) -/

namespace RhoCanonicityCheck

structure Inputs (F : Type) where
  rho : F
  e1 : F
  f : F
  g0 : F
  z13F : F
deriving ProvableStruct

/-- The shifted-value witness program (Rust computes it from the pieces' values). -/
def e1FPrimeWit (e1 f : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env e1 + ((2 ^ 4 : ℕ) : Fp) * readCell env f + ((2 ^ 140 : ℕ) : Fp) - Halo2.Ironwood.tP]

@[circuit_norm]
theorem e1FPrimeWit_eval (e1 f : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((e1FPrimeWit e1 f).eval env)[j] = readCell env e1 + ((2 ^ 4 : ℕ) : Fp) * readCell env f + ((2 ^ 140 : ℕ) : Fp) - Halo2.Ironwood.tP := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [e1FPrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The gate child: the `RhoCanonicity` region bundle in its own layouter region. -/
def gateChild : FormalCircuit Fp RhoCanonicity.Config RhoCanonicity.Config RhoCanonicity.Row unit :=
  RhoCanonicity.bundle.toFormal "NoteCommit input rho"

derive_contract_bridges gateChild := gateChild

def synth (gcfg : RhoCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) : Circuit Fp Unit := do
  let zs ← LookupRangeCheck.witnessCheck 10 14 false lcfg (e1FPrimeWit input.e1 input.f)
  let _ ← gateChild.call gcfg
    { rho := input.rho, e1 := input.e1, g0 := input.g0, f := input.f,
      e1FPrime := zs.z0, z13F := input.z13F, z14E1FPrime := zs.zLast }
  pure ()

theorem synth_regionCount (gcfg : RhoCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) (i : RegionIndex) :
    Operations.regionCount ((synth gcfg lcfg input).operations i) = 2 := by
  simp only [synth, LookupRangeCheck.witnessCheck, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

def circuit :
    FormalCircuit Fp (RhoCanonicity.Config × LookupRangeCheck.Config 10)
      (RhoCanonicity.Config × LookupRangeCheck.Config 10) Inputs unit where
  name := "NoteCommit input rho (canonicity)"
  configure := pure

  synthesize := fun (gcfg, lcfg) input => synth gcfg lcfg input

  elaborated := fun (gcfg, lcfg) =>
    { output := fun _ _ => ()
      regionCount := fun _ => 2
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synth_regionCount gcfg lcfg input i).symm }

  EnvAssumptions := fun (_, lcfg) env =>
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions input :=
    IsBool input.g0 ∧ input.f.val < 2 ^ 250 ∧ input.e1.val < 2 ^ 4 ∧
    input.z13F = ((input.f.val / 2 ^ 130 : ℕ) : Fp)

  Spec input _ _ :=
    input.e1.val = bitrange input.rho.val 0 4 ∧
    input.f.val = bitrange input.rho.val 4 250 ∧
    input.g0.val = bitrange input.rho.val 254 1

  ProverAssumptions input _ _ :=
    input.e1.val = bitrange input.rho.val 0 4 ∧
    input.f.val = bitrange input.rho.val 4 250 ∧
    input.g0.val = bitrange input.rho.val 254 1

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, circuit_norm] at hc
    obtain ⟨hWC, hGate⟩ := hc
    subcircuit_rw at hWC
    have hWSpec := hWC
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hWSpec
    simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num] at hWSpec
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hWSpec
    rw [FormalRegionCircuit.output_call, rangeCheckAt_output] at hGate
    simp only [gateChild_assumptions_eq, gateChild_spec_eq, circuit_norm] at hGate
    have hGSpec := hGate trivial
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    simp only [RhoCanonicity.toDonor, Halo2.Ironwood.NoteCommit.RhoCanonicity.Gate.Spec] at hGSpec
    exact ⟨hGSpec.1, hGSpec.2.1, hGSpec.2.2.1⟩

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, Operations.regionCount, circuit_norm,
      readCell] at hwit ⊢
    obtain ⟨⟨hWaP, hWrc⟩, hWgate⟩ := hwit
    subcircuit_rw
    obtain ⟨hChildSpec, hChildPS⟩ := h_spec_0
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]; simp)
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hChildSpec
    rw [LookupRangeCheck.rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hChildPS
    simp only [circuit_norm, show (10 * 14 : ℕ) = 140 from by norm_num]
      at hChildSpec hChildPS
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hChildSpec
    obtain ⟨hz0eqP, hzLast⟩ := hChildPS
    refine ⟨⟨?_, ?_, ?_⟩, trivial, ?_, ?_⟩
    · rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]
      simp
    · rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_assumptions_eq, circuit_norm, h_input]
      exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    · rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_proverAssumptions_eq, circuit_norm]
      rw [h_input.2.1, h_input.2.2.1] at hWaP
      rw [h_input.1, h_input.2.1, h_input.2.2.1, h_input.2.2.2.1, h_input.2.2.2.2]
      simp only [RhoCanonicity.toDonor, Halo2.Ironwood.NoteCommit.RhoCanonicity.Gate.Spec]
      refine ⟨⟨hPA.1, hPA.2.1, hPA.2.2, ?_⟩, by rw [hWaP]; ring⟩
      intro h1
      rw [hzLast, ← hz0eqP, hWaP]
      have hbase_lt := base_val_lt_tP_val hPA.1 hPA.2.1 (ZMod.val_lt input_rho)
        (bit_one_of_val_eq hPA.2.2 h1) (by norm_num)
      rw [shifted_high_zero (by norm_num) (by norm_num) hbase_lt]
      simp

end RhoCanonicityCheck

/-! ## `psi` canonicity (`psi_canonicity`, `note_commit.rs:1920-1958` + the
`"NoteCommit input psi"` gate region) -/

namespace PsiCanonicityCheck

structure Inputs (F : Type) where
  psi : F
  h0 : F
  g1 : F
  h1 : F
  g2 : F
  z13G : F
deriving ProvableStruct

/-- The shifted-value witness program (Rust computes it from the pieces' values). -/
def g1G2PrimeWit (g1 g2 : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[readCell env g1 + ((2 ^ 9 : ℕ) : Fp) * readCell env g2 + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP]

@[circuit_norm]
theorem g1G2PrimeWit_eval (g1 g2 : AssignedCell Fp) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((g1G2PrimeWit g1 g2).eval env)[j] = readCell env g1 + ((2 ^ 9 : ℕ) : Fp) * readCell env g2 + ((2 ^ 130 : ℕ) : Fp) - Halo2.Ironwood.tP := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [g1G2PrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The gate child: the `PsiCanonicity` region bundle in its own layouter region. -/
def gateChild : FormalCircuit Fp PsiCanonicity.Config PsiCanonicity.Config PsiCanonicity.Row unit :=
  PsiCanonicity.bundle.toFormal "NoteCommit input psi"

derive_contract_bridges gateChild := gateChild

def synth (gcfg : PsiCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) : Circuit Fp Unit := do
  let zs ← LookupRangeCheck.witnessCheck 10 13 false lcfg (g1G2PrimeWit input.g1 input.g2)
  let _ ← gateChild.call gcfg
    { psi := input.psi, h0 := input.h0, g1 := input.g1, h1 := input.h1, g2 := input.g2,
      g1G2Prime := zs.z0, z13G := input.z13G, z13G1G2Prime := zs.zLast }
  pure ()

theorem synth_regionCount (gcfg : PsiCanonicity.Config) (lcfg : LookupRangeCheck.Config 10)
    (input : Inputs (AssignedCell Fp)) (i : RegionIndex) :
    Operations.regionCount ((synth gcfg lcfg input).operations i) = 2 := by
  simp only [synth, LookupRangeCheck.witnessCheck, circuit_norm, Circuit.operations_bind,
    operations_assignRegion, Operations.regionCount]

def circuit :
    FormalCircuit Fp (PsiCanonicity.Config × LookupRangeCheck.Config 10)
      (PsiCanonicity.Config × LookupRangeCheck.Config 10) Inputs unit where
  name := "NoteCommit input psi (canonicity)"
  configure := pure

  synthesize := fun (gcfg, lcfg) input => synth gcfg lcfg input

  elaborated := fun (gcfg, lcfg) =>
    { output := fun _ _ => ()
      regionCount := fun _ => 2
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synth_regionCount gcfg lcfg input i).symm }

  EnvAssumptions := fun (_, lcfg) env =>
    LookupRangeCheck.TableLoaded 10 lcfg env.env ∧
    lcfg.qLookup.index ≠ lcfg.qRunning.index

  Assumptions input :=
    IsBool input.h1 ∧ input.g1.val < 2 ^ 9 ∧ input.g2.val < 2 ^ 240 ∧
    input.h0.val < 2 ^ 5 ∧
    input.z13G = (((input.g1.val + input.g2.val * 2 ^ 9) / 2 ^ 129 : ℕ) : Fp)

  Spec input _ _ :=
    input.g1.val = bitrange input.psi.val 0 9 ∧
    input.g2.val = bitrange input.psi.val 9 240 ∧
    input.h0.val = bitrange input.psi.val 249 5 ∧
    input.h1.val = bitrange input.psi.val 254 1

  ProverAssumptions input _ _ :=
    input.g1.val = bitrange input.psi.val 0 9 ∧
    input.g2.val = bitrange input.psi.val 9 240 ∧
    input.h0.val = bitrange input.psi.val 249 5 ∧
    input.h1.val = bitrange input.psi.val 254 1

  soundness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, circuit_norm] at hc
    obtain ⟨hWC, hGate⟩ := hc
    subcircuit_rw at hWC
    have hWSpec := hWC
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hWSpec
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num] at hWSpec
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hWSpec
    rw [FormalRegionCircuit.output_call, rangeCheckAt_output] at hGate
    simp only [gateChild_assumptions_eq, gateChild_spec_eq, circuit_norm] at hGate
    have hGSpec := hGate trivial
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    simp only [PsiCanonicity.toDonor, Halo2.Ironwood.NoteCommit.PsiCanonicity.Gate.Spec] at hGSpec
    exact ⟨hGSpec.1, hGSpec.2.1, hGSpec.2.2.1, hGSpec.2.2.2.1⟩

  completeness := by
    circuit_proof_start
    obtain ⟨hTable, hDistinct⟩ := _hE
    simp only [LookupRangeCheck.witnessCheck, Operations.regionCount, circuit_norm,
      readCell] at hwit ⊢
    obtain ⟨⟨hWaP, hWrc⟩, hWgate⟩ := hwit
    subcircuit_rw
    obtain ⟨hChildSpec, hChildPS⟩ := h_spec_0
      (by rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩)
      (by rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
      (by rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]; simp)
    rw [LookupRangeCheck.rangeCheckAt_spec_eq, rangeCheckAt_output] at hChildSpec
    rw [LookupRangeCheck.rangeCheckAt_proverSpec_eq, rangeCheckAt_output] at hChildPS
    simp only [circuit_norm, show (10 * 13 : ℕ) = 130 from by norm_num]
      at hChildSpec hChildPS
    obtain ⟨hz0eq, lo, hlo, htel⟩ := hChildSpec
    obtain ⟨hz0eqP, hzLast⟩ := hChildPS
    refine ⟨⟨?_, ?_, ?_⟩, trivial, ?_, ?_⟩
    · rw [LookupRangeCheck.rangeCheckAt_envAssumptions_eq]
      exact ⟨hTable, hDistinct⟩
    · rw [LookupRangeCheck.rangeCheckAt_assumptions_eq]
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    · rw [LookupRangeCheck.rangeCheckAt_proverAssumptions_eq]
      simp
    · rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_assumptions_eq, circuit_norm, h_input]
      exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, lo, hlo, by rw [hz0eq]; exact htel⟩
    · rw [FormalRegionCircuit.output_call, rangeCheckAt_output]
      simp only [gateChild_proverAssumptions_eq, circuit_norm]
      rw [h_input.2.2.1, h_input.2.2.2.2.1] at hWaP
      rw [h_input.1, h_input.2.1, h_input.2.2.1, h_input.2.2.2.1, h_input.2.2.2.2.1,
        h_input.2.2.2.2.2]
      simp only [PsiCanonicity.toDonor, Halo2.Ironwood.NoteCommit.PsiCanonicity.Gate.Spec]
      refine ⟨⟨hPA.1, hPA.2.1, hPA.2.2.1, hPA.2.2.2, ?_⟩, by rw [hWaP]; ring⟩
      intro h1
      rw [hzLast, ← hz0eqP, hWaP]
      have hbase_lt := base_val_lt_tP_val hPA.1 hPA.2.1 (ZMod.val_lt input_psi)
        (bit_one_of_val_eq hPA.2.2.2 h1) (by norm_num)
      rw [shifted_high_zero (by norm_num) (by norm_num) hbase_lt]
      simp

end PsiCanonicityCheck

end Halo2.Ironwood.NoteCommit
