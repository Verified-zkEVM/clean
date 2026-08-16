import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Defs
import Clean.Ironwood.Ecc.MulOverflowTheorems
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Utilities.LookupRangeCheck

/-!
The overflow check of variable-base scalar multiplication: given the scalar `alpha` and the
running sums `zs = [z_0, z_1, …, z_254, z_255]`, enforces the two facts that make the mul sound
against overflow of the 254-bit scalar decomposition:
- `recovery`: `z_0 = alpha + t_q` (the full running sum recovers the scalar plus the field
  modulus offset `t_q`);
- `canonicity`: witnessing `s = alpha + k_254·2^130` and decomposing its low 130 bits, the
  high tail `s_minus_lo_130` vanishes in the appropriate cases (`k_254 = 0`, or `z_130` is
  the top bit `2^124`), ruling out a non-canonical `alpha`.

The low 130 bits of `s` are decomposed by a `LookupRangeCheck` child (thirteen `K = 10`-bit
lookups).

Reference: `halo2_gadgets/src/ecc/chip/mul/overflow.rs`.
-/

namespace Zcash.Circuits.Ecc.MulOverflow

open Halo2
open Ecc (tQ)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- The number of `K`-bit words decomposing the low 130 bits of `s`. With `K = 10`,
`numWords = 13`. Kept as a def so the layout rows and the `2^{K·numWords} = 2^130` arithmetic
read symbolically. -/
def numWords (K : ℕ) : ℕ := 130 / K

/-! ## Config -/

structure Config (K : ℕ) where
  -- Selector to check z_0 = alpha + t_q (mod p).
  qOverflow : Selector
  -- 10-bit lookup table.
  lookupConfig : LookupRangeCheck.Config K
  -- Advice columns.
  adv0 : Column .advice
  adv1 : Column .advice
  adv2 : Column .advice

/-! ## The `q_mul_overflow` gate

Layout relative to the gate row `g` (`q_mul_overflow` enabled at `Rotation::cur`):

    | advices[0]        | advices[1]        | advices[2] |
    -----------------------------------------------------------
    | z_0   (g-1, prev) | k_254 (g-1, prev) |            |
    | z_130 (g,   cur)  | alpha (g,   cur)  | s (g, cur) |
    | eta   (g+1, next) | s_minus_lo_130 (g+1, next)     |

The five constraints, verbatim:
- `s_check`      : `s − (alpha + k_254·2^130)`
- `recovery`     : `z_0 − alpha − t_q`
- `lo_zero`      : `k_254·(z_130 − 2^124)`
- `s_minus_lo_130_check` : `k_254·s_minus_lo_130`
- `canonicity`   : `(1 − k_254)·(1 − z_130·eta)·s_minus_lo_130`
-/

/-- The overflow gate, a pure function of the config. Enabled at the middle row `g`;
reads `advices[0]/advices[1]` at `prev/cur/next` and `advices[2]` at `cur`. -/
def overflowGate (K : ℕ) (cfg : Config K) : Gate Fp :=
  let z0 : Expression Fp Query := queryAdvice cfg.adv0 (-1)   -- z_0   (prev)
  let z130 : Expression Fp Query := queryAdvice cfg.adv0 0     -- z_130 (cur)
  let eta : Expression Fp Query := queryAdvice cfg.adv0 1      -- eta   (next)
  let k254 : Expression Fp Query := queryAdvice cfg.adv1 (-1)  -- k_254 (prev)
  let alpha : Expression Fp Query := queryAdvice cfg.adv1 0    -- alpha (cur)
  let sMinusLo130 : Expression Fp Query := queryAdvice cfg.adv1 1  -- s_minus_lo_130 (next)
  let s : Expression Fp Query := queryAdvice cfg.adv2 0        -- s (cur)
  Gate.withSelector "overflow checks" cfg.qOverflow
    [z0, z130, eta, k254, alpha, sMinusLo130, s] <|
    let twoPow124 : Expression Fp Query := (2 ^ 124 : Fp)
    -- Rust builds `two_pow_130 = two_pow_124 * Constant(1 << 6)`: a PRODUCT of two `Constant`
    -- expressions, NOT a single `2^130` constant. We reproduce that AST exactly (`k_254 *
    -- two_pow_130` is then `product(k_254, product(2^124, 64))`), so the VK fixture matches. Both
    -- factors are `Expression.const`, so the `*` is an expression product (`mul`), erasing to
    -- `.product` — not `.scaled`.
    let twoPow130 : Expression Fp Query :=
      twoPow124 * (Expression.const (2 ^ 6 : Fp) : Expression Fp Query)
    let sCheck := s - (alpha + k254 * twoPow130)
    let recovery := z0 - alpha - (tQ : Fp)
    let loZero := k254 * (z130 - twoPow124)
    let sMinusLo130Check := k254 * sMinusLo130
    let canonicity := ((1 : Fp) - k254) * ((1 : Fp) - z130 * eta) * sMinusLo130
    [ ("s_check", sCheck), ("recovery", recovery), ("lo_zero", loZero),
      ("s_minus_lo_130_check", sMinusLo130Check), ("canonicity", canonicity) ]

@[circuit_norm, configure_selector_norm, keygen_norm, synthesis_summary_norm]
theorem overflowGate_selector (K : ℕ) (cfg : Config K) :
    (overflowGate K cfg).selector = cfg.qOverflow := rfl

/-- Enable equality on the three advice columns, allocate the `q_mul_overflow` selector, register
the overflow gate. The `lookup_config` is handed down by the chip assembly, already configured by
`LookupRangeCheck.configure`. -/
def configure (K : ℕ) (lookupConfig : LookupRangeCheck.Config K)
    (adv0 adv1 adv2 : Column .advice) : Configure Fp (Config K) := do
  enableEquality adv0.toAny
  enableEquality adv1.toAny
  enableEquality adv2.toAny
  let qOverflow ← selector
  let cfg : Config K := { qOverflow, lookupConfig, adv0, adv1, adv2 }
  createGate (overflowGate K cfg)
  return cfg

instance (K : ℕ) (lookupConfig : LookupRangeCheck.Config K)
    (adv0 adv1 adv2 : Column .advice) :
    ElaboratedConfigure (configure K lookupConfig adv0 adv1 adv2) := by
  unfold configure
  infer_instance

/-! ## Inputs / Output -/

/-- Verifier-visible inputs: the scalar `alpha` and the running-sum cells `z_0`, `z_130`,
`k_254 = z_254`, as already-assigned cells. -/
structure Inputs (F : Type) where
  -- The original scalar.
  alpha : F
  -- z_0, the full running sum.
  z0 : F
  -- z_130, the running sum after the high half.
  z130 : F
  -- k_254 = z_254, the top bit.
  k254 : F
deriving ProvableStruct

/-! ## Witness programs

`s` and `η` are the two witnessed cells, spelled over the Halo2-Clean witgen IR (`FExpr Fp`). -/

/-- The witness value of `s = alpha + k_254·2^130`. -/
def sWit (input : Inputs (AssignedCell Fp)) : WitgenIR Fp 1 :=
  .ofFExpr ((.expr input.alpha) + (.expr input.k254) * (.const (2 ^ 130 : Fp)))

/-- The witness value of `η = inv0(z_130)`, the `0⁻¹ = 0` field inverse. -/
def etaWit (input : Inputs (AssignedCell Fp)) : WitgenIR Fp 1 :=
  .ofFExpr (.inv (.expr input.z130))

/-! ## Faithful region structure

Three sibling regions at the layouter level, plus the copyCheck child call:

1. **witness-s region**: witness `s` at `advices[0]` row 0 of its own region.
2. **the copyCheck child**: `lookup_config.copy_check(s, num_words, false)` — a layouter-level
   range check that copies `s` into the running-sum column and decomposes its low 130 bits; its
   `zLast` output is `s_minus_lo_130`.
3. **the gate region**: enables `q_mul_overflow` and COPIES the six participating cells across
   regions — `z_0`, `z_130`, `k_254`, `alpha` (from the parent mul's running-sum region), `s`
   (from region 1), `s_minus_lo_130` (from the copyCheck child). `η = inv0(z_130)` is witnessed
   here.

The cross-region copies are `copyAdvice` of cells whose `regionIndex` is a *different* region —
the model supports this directly (`Cell` carries its region index; `copyAdvice`'s
`constrainEqual` reads the source at its own region's placement). -/

/-- The gate region body, a region-level circuit at row offset 0 of its own region. Enables the
overflow gate at row 1 (so the gate's prev/cur/next are rows 0/1/2) and copies in the six cells +
witnesses `η`. The `s` cell (region 1) and `sMinusLo130` cell (the copyCheck child) arrive as
arguments; the four running-sum cells come from `input`. -/
def gateRegion (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp))
    (sCell sMinusLo130 : AssignedCell Fp) : RegionCircuit Fp Unit := do
  -- z_0 (adv0 @ 0, gate prev), z_130 (adv0 @ 1, gate cur)
  let _z0 ← copyAdvice input.z0 cfg.adv0 0
  let _z130 ← copyAdvice input.z130 cfg.adv0 1
  -- η = inv0(z_130) at adv0 @ 2 (gate next)
  let _eta ← assignAdvice cfg.adv0 2 (etaWit input)
  -- k_254 (adv1 @ 0, gate prev), alpha (adv1 @ 1, gate cur)
  let _k254 ← copyAdvice input.k254 cfg.adv1 0
  let _alpha ← copyAdvice input.alpha cfg.adv1 1
  -- s_minus_lo_130 (adv1 @ 2, gate next)
  let _sMinusLo130 ← copyAdvice sMinusLo130 cfg.adv1 2
  -- s (adv2 @ 1, gate cur)
  let _s ← copyAdvice sCell cfg.adv2 1
  -- enable the overflow gate at the middle row (offset+1 = 1)
  (overflowGate K cfg).enable 1
  return ()

@[synthesis_summary_norm]
theorem gateRegion_synthesisSummary
    (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp))
    (sCell sMinusLo130 : AssignedCell Fp) (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((gateRegion K cfg input sCell sMinusLo130).operations region) =
      .ofColumns
        [.column .advice cfg.adv0.index,
          .column .advice cfg.adv0.index,
          .column .advice cfg.adv0.index,
          .column .advice cfg.adv1.index,
          .column .advice cfg.adv1.index,
          .column .advice cfg.adv1.index,
          .column .advice cfg.adv2.index,
          .selector cfg.qOverflow.index]
        3 0 := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [gateRegion, circuit_norm, synthesis_summary_norm,
      configure_selector_norm]
  · simp only [gateRegion, circuit_norm, synthesis_summary_norm]
    omega
  · simp only [gateRegion, circuit_norm, synthesis_summary_norm]
  · simp only [gateRegion, circuit_norm, synthesis_summary_norm]

/-- The layouter-level `overflow_check` body: the three faithful sibling regions plus the
copyCheck child. -/
def synthesize (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp)) :
    Circuit Fp Unit := do
  -- region 1: witness s = alpha + k_254·2^130 at advices[0] row 0
  let sCell ← assignRegion "s = alpha + k_254 ⋅ 2^130"
    (assignAdvice cfg.adv0 0 (sWit input))
  -- child copyCheck: decompose the low 130 bits of s
  let dec ← (LookupRangeCheck.copyCheck K (numWords K) false).call cfg.lookupConfig
    { element := sCell }
  -- region 3: the overflow-check gate region with cross-region copies
  let _ ← assignRegion "overflow check" (gateRegion K cfg input sCell dec.zLast)
  return ()

/-! ## Contract

`EnvAssumptions` states the table fact + selector distinctness over the *projected* child
sub-config `cfg.lookupConfig` — exactly the copyCheck child's `EnvAssumptions` on that config. -/

/-- The parent `EnvAssumptions`: the child's `TableLoaded` over the projected `lookupConfig`,
plus the selector distinctness the child needs. Definitionally the copyCheck child's
`EnvAssumptions` applied to `cfg.lookupConfig`. -/
def EnvAssumptions (K : ℕ) (cfg : Config K) (env : Placed Environment Fp) : Prop :=
  LookupRangeCheck.TableLoaded K cfg.lookupConfig env.env ∧
    cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

/-- The overflow-check contract, verifier view. `z_0` recovers `alpha + t_q`; `z_130` is `2^124`
unless `k_254 = 0`; and some split `s = s_lo + 2^130·s_hi` with `s_lo < 2^130` satisfies the two
canonicity disjunctions. -/
def Spec (input : Inputs Fp) : Prop :=
  input.z0 = input.alpha + (tQ : Fp) ∧
  (input.k254 = 0 ∨ input.z130 = (2 ^ 124 : Fp)) ∧
  ∃ (sHi : Fp) (sLo : ℕ), sLo < 2 ^ 130 ∧
    input.alpha + input.k254 * (2 ^ 130 : Fp) = (sLo : Fp) + (2 ^ 130 : Fp) * sHi ∧
    (input.k254 = 0 ∨ sHi = 0) ∧
    (input.k254 = 1 ∨ input.z130 ≠ 0 ∨ sHi = 0)

/-! ## Child contract-projection bridges (`rfl`, child stays folded)

Bridges exposing exactly the copyCheck child's contract fields without unfolding the bundle
literal. Since `copyCheck = rangeCheck.toFormal`, its contract fields are `rangeCheck`'s. -/

private theorem copyCheck_spec_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).Spec
      = fun input output _ =>
          output.z0 = input.element ∧
          (∃ lo : ℕ, lo < 2 ^ (K * numWords K) ∧
            input.element = (lo : Fp) + ((2 ^ (K * numWords K) : ℕ) : Fp) * output.zLast) ∧
          (false = true → output.zLast = 0 ∧ input.element.val < 2 ^ (K * numWords K)) := rfl

private theorem copyCheck_assumptions_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).Assumptions
      = fun _ => 2 ^ (K * numWords K) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD := rfl

private theorem copyCheck_envAssumptions_eq (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.copyCheck K (numWords K) false).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded K cfg env.env ∧ cfg.qLookup.index ≠ cfg.qRunning.index) :=
  rfl

private theorem copyCheck_proverAssumptions_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).ProverAssumptions
      = fun input _ _ => (false = true → input.element.val < 2 ^ (K * numWords K)) := rfl

/-- The copyCheck child's `ProverSpec` (C6): the honest nat decomposition of the tail. -/
private theorem copyCheck_proverSpec_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).ProverSpec
      = fun input output _ _ =>
          output.zLast = ((input.element.val / 2 ^ (K * numWords K) : ℕ) : Fp) :=
  rfl

/-! ## The gadget bundle

`overflow_check` at the layouter level, three faithful sibling regions. Parameterized by `K` and
the arithmetic bridge `K · numWords K = 130`. -/

/-- The region count of `synthesize`: region 1 (witness s), the copyCheck child (1 region), and
region 3 (gate) — three regions, independent of the starting index. -/
theorem synthesize_regionCount (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp))
    (i : RegionIndex) :
    Operations.regionCount ((synthesize K cfg input).operations i) = 3 := by
  simp only [synthesize, circuit_norm, operations_assignRegion, Operations.regionCount_append,
    Operations.regionCount]

def circuitSynthesisSummary (K : ℕ) (cfg : Config K)
    : FloorPlanner.SynthesisSummary :=
  (FloorPlanner.SynthesisSummary.ofRegion
      (.ofColumns [.column .advice cfg.adv0.index] 1 0)).combine
    ((LookupRangeCheck.copyCheckSynthesisSummary
        K (numWords K) false cfg.lookupConfig).combine
      (FloorPlanner.SynthesisSummary.ofRegion
        (.ofColumns
          [.column .advice cfg.adv0.index,
            .column .advice cfg.adv0.index,
            .column .advice cfg.adv0.index,
            .column .advice cfg.adv1.index,
            .column .advice cfg.adv1.index,
            .column .advice cfg.adv1.index,
            .column .advice cfg.adv2.index,
            .selector cfg.qOverflow.index]
          3 0)))

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_tableRowExtent_eq (K : ℕ) (cfg : Config K) :
    (circuitSynthesisSummary K cfg).tableRowExtent = 0 := by
  simp only [circuitSynthesisSummary,
    LookupRangeCheck.copyCheckSynthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem circuitSynthesisSummary_instanceRowExtent_eq (K : ℕ) (cfg : Config K) :
    (circuitSynthesisSummary K cfg).instanceRowExtent = 0 := by
  simp only [circuitSynthesisSummary,
    LookupRangeCheck.copyCheckSynthesisSummary,
    synthesis_summary_norm]

/-- The overflow checker uses selectors and advice columns and performs no table load. -/
@[synthesis_summary_norm]
theorem circuitSynthesisSummary_hasNoFixedWrites (K : ℕ) (cfg : Config K) :
    (circuitSynthesisSummary K cfg).HasNoFixedWrites := by
  simp only [circuitSynthesisSummary,
    FloorPlanner.SynthesisSummary.hasNoFixedWrites_combine,
    FloorPlanner.SynthesisSummary.hasNoFixedWrites_ofRegion,
    FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns,
    LookupRangeCheck.copyCheckSynthesisSummary_hasNoFixedWrites]
  simp

def circuit (K : ℕ) (hKW : K * numWords K = 130) :
    FormalCircuit Fp (LookupRangeCheck.Config K × Column .advice × Column .advice ×
      Column .advice) (Config K) Inputs unit where
  name := "overflow checks"

  configure := fun (lookupConfig, adv0, adv1, adv2) => configure K lookupConfig adv0 adv1 adv2

  synthesize cfg input := synthesize K cfg input

  elaborated :=
    { keygenRequirements :=
        { lookups input _ := [LookupRangeCheck.rangeCheckLookup K input.1]
          permutationColumns input _ := [input.1.runningSum]
          inputCells _ _ input :=
            [input.alpha.cell, input.z0.cell,
              input.z130.cell, input.k254.cell] }
      registered := by
        keygen_registration
      output _ _ _ := ()
      regionCount _ := 3
      synthesisSummary cfg _ _ := circuitSynthesisSummary K cfg
      copyCellsAssigned := by
        intro configInput counts hconfig input i
        simp only [synthesize, circuit_norm]
        unfold Operations.CopyCellsAssigned
        rw [Operations.copyCellsAssignedFrom_region_iff]
        refine ⟨by keygen_registration, ?_⟩
        apply Operations.CopyCellsAssignedFrom.append
        · keygen_registration
        · have hdec := LookupRangeCheck.copyCheck_output_cells_assigned
            K (numWords K) false
            ((configure K configInput.1 configInput.2.1 configInput.2.2.1
              configInput.2.2.2).output counts).lookupConfig
            { element := AssignedCell.of i 0
                ((configure K configInput.1 configInput.2.1 configInput.2.2.1
                  configInput.2.2.2).output counts).adv0 }
            (i + 1)
          rw [← (LookupRangeCheck.copyCheck K (numWords K) false).call_operations]
            at hdec
          simp only [gateRegion, circuit_norm, keygen_norm, keygen_spine]
          simp_all
      output_eq := by intro _ _ _; rfl
      regionCount_eq := fun cfg input i => (synthesize_regionCount K cfg input i).symm
      synthesisSummary_eq := by
        intro _ _ _
        simp only [circuitSynthesisSummary, synthesize,
          circuit_norm, synthesis_summary_norm, configure_selector_norm] }

  EnvAssumptions cfg env := EnvAssumptions K cfg env

  Assumptions _ :=
    2 ^ (K * numWords K) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD

  Spec input _ _ := Spec input

  ProverAssumptions input _ _ := Spec input

  -- ══ Soundness ══
  soundness := by
    circuit_proof_start2 [LookupRangeCheck.copyCheck, gateRegion, overflowGate, Spec,
      EnvAssumptions]
    -- the child decomposition: s = lo + 2^{K·numWords}·zLast, lo < 2^{K·numWords}
    specialize dec_spec env_assumptions assumptions
    obtain ⟨-, lo, hlo, hDecomp⟩ := dec_spec
    obtain ⟨hCz0, hCz130, hCk254, hCalpha, hCsml, hCs,
      hSCheck, hRecovery, hLoZero, hSMLcheck, hCanon⟩ := region_0
    rw [hKW] at hDecomp hlo
    rw [show (((2 ^ 130 : ℕ) : Fp)) = (2 ^ 130 : Fp) from by norm_num] at hDecomp
    simp_all only
    refine ⟨?_, ?_, ?_⟩
    · -- recovery: z_0 = alpha + t_q
      linear_combination hRecovery
    · -- k_254 = 0 ∨ z_130 = 2^124
      rcases mul_eq_zero.mp hLoZero with h | h
      · exact Or.inl h
      · exact Or.inr (by
          rw [show (2 ^ 124 : Fp) = (2 : Fp) ^ 124 from by norm_num]
          linear_combination sub_eq_zero.mp h)
    · -- the canonicity existential: sHi = the child's zLast value, sLo = lo
      use AssignedCell.eval place env dec_zLast, lo, hlo
      refine ⟨?_, ?_, ?_⟩
      · -- alpha + k_254·2^130 = lo + 2^130·zLast, via s_check + the s copy + the decomposition
        linear_combination -hSCheck
      · -- k_254 = 0 ∨ zLast = 0
        exact mul_eq_zero.mp hSMLcheck
      · -- k_254 = 1 ∨ z_130 ≠ 0 ∨ zLast = 0
        rcases mul_eq_zero.mp hCanon with hK | hRest
        · rcases mul_eq_zero.mp hK with hK1 | hEta
          · exact Or.inl (by linear_combination -hK1)
          · refine Or.inr (Or.inl ?_)
            intro hz
            rw [hz, zero_mul] at hEta
            exact zero_ne_one (by linear_combination -hEta)
        · exact Or.inr (Or.inr hRest)

  -- ══ Completeness ══
  completeness := by
    circuit_proof_start2 [LookupRangeCheck.copyCheck, gateRegion, overflowGate, Spec,
      EnvAssumptions, sWit, etaWit]
    use ⟨env_assumptions, assumptions⟩
    -- the child's constraints and honest facts arrive through the engine's
    -- strengthened goal position (the `EnvA ∧ A ∧ PA` bundle) and `dec_spec`
    obtain ⟨hChildSpec, hChildPS⟩ := dec_spec env_assumptions assumptions
    obtain ⟨-, lo, hlo, hDecompV⟩ := hChildSpec
    obtain ⟨hWz0, hWz130, hWeta, hWk254, hWalpha, hWsml, hWs2⟩ := region_1
    obtain ⟨hRec, hLoZ, sHi, sLo, hsLo_lt, hkey, hHiZ, hEtaSpec⟩ := prover_assumptions
    rw [hKW] at hDecompV hlo hChildPS
    rw [show (((2 ^ 130 : ℕ) : Fp)) = (2 ^ 130 : Fp) from by norm_num] at hDecompV
    -- the honest s cell: `sCell`'s eval is the region-i₀ advice read, with the witnessed value
    have hsval : AssignedCell.eval place env.toEnvironment sCell
        = input_alpha + input_k254 * 2 ^ 130 := by
      rw [← sCell_eq]
      simp only [circuit_norm]
      rw [region_0]
    -- `sHi = 0 → child zLast = 0`: with `sHi = 0` the honest `Spec` pins `s = ↑sLo < 2^130`
    have hCard130 : 2 ^ 130 < PALLAS_BASE_CARD := by
      norm_num [PALLAS_BASE_CARD]
    have hzLastZero : sHi = 0 → AssignedCell.eval place env.toEnvironment dec_zLast = 0 := by
      intro hsHi0
      rw [hChildPS]
      have hsVal : (AssignedCell.eval place env.toEnvironment sCell).val < 2 ^ 130 := by
        have hs_eq : AssignedCell.eval place env.toEnvironment sCell = (sLo : Fp) := by
          rw [hsval, hkey, hsHi0]; ring
        rw [hs_eq, ZMod.val_natCast_of_lt (lt_trans hsLo_lt hCard130)]
        exact hsLo_lt
      rw [Nat.div_eq_of_lt hsVal, Nat.cast_zero]
    have h2124 : (2 ^ 124 : Fp) = (2 : Fp) ^ 124 := by norm_num
    refine ⟨hWz0, hWz130, hWk254, hWalpha, hWsml, hWs2, ?_, ?_, ?_, ?_, ?_⟩
    · -- s_check: the s cell = alpha_gate + k254_gate·2^130
      rw [hWs2, hsval, hWalpha, hWk254]; ring
    · -- recovery: z_0 − alpha − t_q = 0
      rw [hWz0, hWalpha]
      rw [← sub_eq_zero] at hRec
      linear_combination hRec
    · -- lo_zero: k254·(z130 − 2^124) = 0
      rw [hWk254, hWz130]
      rcases hLoZ with h | h
      · rw [h]; ring
      · rw [h, h2124]; ring
    · -- s_minus_lo_130_check: k254·zLast = 0
      rw [hWk254, hWsml]
      rcases hHiZ with h | h
      · rw [h]; ring
      · rw [hzLastZero h]; ring
    · -- canonicity: (1 − k254)·(1 − z130·η)·zLast = 0, η = inv0(z130)
      rw [hWk254, hWz130, hWeta, hWsml]
      rcases hEtaSpec with h | hz | h
      · rw [h]; ring
      · rw [mul_inv_cancel₀ hz]; ring
      · rw [hzLastZero h]; ring

/-- The overflow circuit exposes its reduced layouter footprint. -/
@[synthesis_summary_norm]
theorem circuit_synthesisSummary_eq (K : ℕ) (hKW : K * numWords K = 130)
    (cfg : Config K) (input : Var Inputs Fp) (region : RegionIndex) :
    (circuit K hKW).elaborated.synthesisSummary cfg input region =
      circuitSynthesisSummary K cfg := rfl

@[keygen_norm]
theorem circuit_inputCells (K : ℕ) (hKW : K * numWords K = 130)
    {cfg : Config K} (configured : (circuit K hKW).Configured cfg)
    (input : Var Inputs Fp) :
    configured.inputCells input =
      [input.alpha.cell, input.z0.cell, input.z130.cell, input.k254.cell] := rfl

end MulOverflow

end Zcash.Circuits.Ecc
