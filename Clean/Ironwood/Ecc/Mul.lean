import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.MulTheorems
import Clean.Ironwood.Ecc.MulAssignTheorems
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulIncomplete
import Clean.Ironwood.Ecc.MulComplete
import Clean.Ironwood.Ecc.MulOverflow

/-!
Variable-base scalar multiplication: computes `[alpha] base` where `alpha : Fp` is a Pallas
base-field element. The working scalar `k = alpha.val + t_q` is decomposed MSB-first into 255
bits and processed as: `acc = [2]base` via complete addition; the running sum `z` starts at 0;
the `hi` incomplete half (125 double-and-add steps, bits `k_254..k_130`); the `lo` incomplete
half (126 steps, bits `k_129..k_4`); three complete-addition bits `k_3..k_1`; the LSB step `k_0`
(the `q_mul_lsb` gate) and a final complete addition; and the overflow check on `z_0`, `z_130`,
`k_254`.

Soundness rests on `2^254 + t_q ≡ 0 (mod q)`: the double-and-add accumulates
`[2^254 + k] base = [alpha] base`.

Reference: `halo2_gadgets/src/ecc/chip/mul.rs`.
-/

open ProvableType.Halo2
  (eval_field eval_field_prover eval_field' eval_field_prover' eval_cells eval_cells_prover
    eval_fields_cells)
open ProvableStruct.Halo2 (eval_var_eq_eval eval_var_eq_eval_prover)

namespace Zcash.Circuits.Ecc.Mul

open Halo2
open Ecc.Mul.Decompose (m_bounds)
open Ecc.Mul.Incomplete.DoubleAndAdd (accScalar zRunValue)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)
open Ecc.MulIncomplete (BitsHint kBitsWindow kBitsWindow_eq_kBits
  kBitsWindow_as_kBits kBitsWindow_zero)

/-! ## Config -/

structure Config where
  -- Selector used to check switching logic on LSB.
  qMulLsb : Selector
  -- Configuration used in complete addition.
  addConfig : Add.Config
  -- Configuration used for the `hi` bits of the scalar.
  hiConfig : MulIncomplete.Config
  -- Configuration used for the `lo` bits of the scalar.
  loConfig : MulIncomplete.Config
  -- Configuration used for the complete-addition part of the double-and-add algorithm.
  completeConfig : MulComplete.Config
  -- Configuration used to check for overflow.
  overflowConfig : MulOverflow.Config 10

/-! ## The `q_mul_lsb` gate

    | x_p    | y_p    | z_complete |
    -----------------------------------
    | x_p    | y_p    | z_1        |   ← q_mul_lsb enabled here
    | base_x | base_y | z_0        |

`k_0 = z_0 − 2·z_1`, `bool_check = k_0(k_0−1)`, and the correction point is pinned by
`lsb_x = ternary(k_0, x_p, x_p − base_x)`, `lsb_y = ternary(k_0, y_p, y_p + base_y)`:
`k_0 = 0 ⇒ (x_p, y_p) = (base_x, −base_y)` (i.e. `−base`), `k_0 = 1 ⇒ (x_p, y_p) = (0, 0)`. -/

/-- The `q_mul_lsb` gate, a pure function of the config columns. Reads `z_complete` at
`cur`/`next` (`z_1`, `z_0`), `add.xP`/`add.yP` at `cur` (`x_p`, `y_p`) and `next`
(`base_x`, `base_y`). -/
def lsbGate (cfg : Config) : Gate Fp :=
  let z1 : Expression Fp Query := queryAdvice cfg.completeConfig.zComplete 0   -- z_1
  let z0 : Expression Fp Query := queryAdvice cfg.completeConfig.zComplete 1   -- z_0
  let xP : Expression Fp Query := queryAdvice cfg.addConfig.xP 0               -- x_p
  let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP 0               -- y_p
  let baseX : Expression Fp Query := queryAdvice cfg.addConfig.xP 1            -- base_x
  let baseY : Expression Fp Query := queryAdvice cfg.addConfig.yP 1            -- base_y
  Gate.withSelector "LSB check" cfg.qMulLsb [z1, z0, xP, yP, baseX, baseY] <|
    let lsb := z0 - z1 * (2 : Fp)
    -- `lsb · (1 − lsb)`, with the `1` on the left of the subtraction to match the compiled gate
    -- AST.
    let boolCheck := lsb * ((1 : Fp) - lsb)
    let lsbX := lsb * xP + ((1 : Fp) - lsb) * (xP - baseX)
    let lsbY := lsb * yP + ((1 : Fp) - lsb) * (yP + baseY)
    [ ("bool_check", boolCheck), ("lsb_x", lsbX), ("lsb_y", lsbY) ]

/-! ## Configure -/

/-- Instantiates the two incomplete configs from the shared 10-advice bundle, delegates to each
child's `configure`, allocates `q_mul_lsb`, and registers the LSB gate. `advices i` is
`advices[i]` of the 10-column bundle; `lookupConfig` is the range-check config; `addConfig` is
built by the chip and handed down. -/
def configure (addConfig : Add.Config) (lookupConfig : LookupRangeCheck.Config 10)
    (advices : Fin 10 → Column .advice) : Configure Fp Config := do
  -- hi_config: z=9, xA=3, xP=0, yP=1, λ1=4, λ2=5
  let hiConfig ← MulIncomplete.configure (advices 9) (advices 3) (advices 0) (advices 1)
    (advices 4) (advices 5)
  -- lo_config: z=6, xA=7, xP=0, yP=1, λ1=8, λ2=2
  let loConfig ← MulIncomplete.configure (advices 6) (advices 7) (advices 0) (advices 1)
    (advices 8) (advices 2)
  -- complete_config: zComplete=9, shared addConfig
  let completeConfig ← MulComplete.configure (advices 9) addConfig
  -- overflow_config: advices 6,7,8, lookupConfig
  let overflowConfig ← MulOverflow.configure 10 lookupConfig (advices 6) (advices 7) (advices 8)
  let qMulLsb ← selector
  let cfg : Config :=
    { qMulLsb, addConfig, hiConfig, loConfig, completeConfig, overflowConfig }
  createGate (lsbGate cfg)
  return cfg

instance (addConfig : Add.Config) (lookupConfig : LookupRangeCheck.Config 10)
    (advices : Fin 10 → Column .advice) :
    ElaboratedConfigure (configure addConfig lookupConfig advices) := by
  unfold configure
  infer_instance

/-! ## Inputs / Output -/

structure Inputs (F : Type) where
  -- The scalar to multiply by.
  alpha : F
  -- The non-identity base point.
  base : Point F
deriving ProvableStruct

/-! ## Row-span offsets

The main region's phases (init, hi, lo, complete, LSB) are composed at fixed region-relative
row offsets. Hi and lo run side by side: both `double_and_add` start at the same row, on
disjoint column sets, sharing only `x_p`/`y_p` (the base point, written with equal values by
both halves). The complete-round phase follows, and the LSB step's base row is the last
complete round's row. The overflow check is not in the main region: it runs at the layouter
level in three sibling regions after the main region closes. -/

/-- The offset advance from the shared incomplete-half start row to the complete phase (the lo
half is the taller of the two side-by-side halves). -/
def loSpan : ℕ := 128
/-- Rows from `offComp` to the LSB base row: the last complete round's `z` cell
(`comp.zs[2]`) sits at `offComp + 2·2 + 2 = offComp + 6`, and the LSB step is based there. -/
def compSpan : ℕ := 6

/-- Init complete addition at the region's first row. -/
def offInit : ℕ := 0
/-- Hi half, one row after the init add's input row (`z_init` and the hi `z` copy live here). -/
def offHi : ℕ := 1
/-- Lo half — side by side with hi (same starting row, disjoint columns bar `xP`/`yP`). -/
def offLo : ℕ := offHi
/-- Complete rounds. -/
def offComp : ℕ := offLo + loSpan
/-- LSB step. -/
def offLsb : ℕ := offComp + compSpan

/-! ## Child contract-projection bridges

Exposes each child's contract fields (`Spec`, `Assumptions`, etc.) as `rfl`-bridges, so the
composition consumes them without unfolding the child bundle literal. -/

-- The six contract-projection bridges for the `Add.add` child (`add_spec_eq`,
-- `add_assumptions_eq`, `add_envAssumptions_eq`, `add_proverAssumptions_eq`, `add_proverSpec_eq`).
derive_contract_bridges add := Add.add

-- The hi/lo/comp bundles are parametrized by the bit-window offset `w`; `derive_contract_bridges`
-- takes an explicit binder and generalizes the emitted bridges over it.
derive_contract_bridges hi (w : ℕ) := MulIncomplete.double_and_add 124 w
derive_contract_bridges lo (w : ℕ) := MulIncomplete.double_and_add 125 w
derive_contract_bridges comp (w : ℕ) := MulComplete.assign_region 3 w

/-- `K · numWords K = 130` at `K = 10`. Discharges the MulOverflow bridge. -/
theorem hKW10 : (10 : ℕ) * MulOverflow.numWords 10 = 130 := by
  simp only [MulOverflow.numWords]

derive_contract_bridges ov := MulOverflow.circuit 10 hKW10

/-! ## The scalar bits

The working scalar `k = alpha.val + t_q`, MSB-first (`kBits`). There is no `BitsHint` parameter:
the children receive the `alpha` cell in their `Inputs` plus a window offset (`hi` = 0, `lo` = 125,
`complete` = 251 — the global index of each phase's first bit) and derive their bits from the cell
inside their witness closures. The LSB step below derives `k_0 = kBits alpha 254` the same way. The
verifier `Spec` existentially recovers a matching sequence per child. -/

/-! ## Synthesize

The `assign_region` body as a sequence of child `.call`s at the threaded phase offsets, plus
`z_init`, the LSB step, and the final recombination. -/

/-! ## Contract

`Assumptions`: the base is on-curve (hence a non-identity Pallas point). `EnvAssumptions`
aggregates the children's env-facts (only the overflow lookup has a nontrivial one) over the
parent's stored sub-config. `Spec`: `output = alpha.val • base`. -/

/-- The base is on-curve. (The overflow child additionally needs the field-capacity bound
`2^130·2^130 < |Fp|`, which is discharged by `norm_num` at `K = 10`, so it is not carried as
a caller obligation — see `soundness`.) -/
def Assumptions (input : Inputs Fp) : Prop :=
  (input.base : Point Fp).OnCurve

/-- The parent env-assumptions: the overflow child's `TableLoaded` + selector distinctness,
over the parent's stored `overflowConfig`. Aggregates the children's (`Add`, both
`MulIncomplete`, `MulComplete` all have trivial `EnvAssumptions`). -/
def EnvAssumptions (cfg : Config) (env : Placed Environment Fp) : Prop :=
  MulOverflow.EnvAssumptions 10 cfg.overflowConfig env

/-- The circuit computes the variable-base scalar multiplication `[alpha] base`, with the
identity encoded as `(0, 0)` coordinates. -/
def Spec (input : Inputs Fp) (output : Point Fp) : Prop :=
  output = input.alpha.val • input.base

/-! ## Value algebra

The running-sum/canonicity machinery (`chainNat_*`, `chain_cast`, `accScalar_closed`,
`k_canonical`, `m_bounds`, `cells_kNat`, `z0_cell_value`, `nsmul_step`, `neg_add_nsmul`). -/

/-! ## Point-level scalar-multiple algebra

The `SWPoint`-level step/negation/identity algebra, transported to `Point Fp` `nsmul` through the
`toSW` bridge (`Point.ext_toSW_iff`/`toSW_add`/`toSW_nsmul`/`toSW_neg`/`toSW_zero`). -/

section PointAlgebra
open CompElliptic.CurveForms.ShortWeierstrass (SWPoint)
open CompElliptic.Curves.Pasta
open Point (ext_toSW_iff toSW_add toSW_neg toSW_zero toSW_nsmul
  valid_add valid_neg valid_zero valid_nsmul nsmul_add_nsmul nsmul_eq_zero_iff)

/-- `P + P = 2 • P` at the `Point` level. -/
private theorem point_two_nsmul {P : Point Fp} (hP : P.OnCurve) : P + P = 2 • P := by
  have hPv : P.Valid := Or.inl hP
  apply (ext_toSW_iff (valid_add hPv hPv) (valid_nsmul hPv 2)).mpr
  rw [toSW_add hPv hPv, toSW_nsmul hPv 2, two_nsmul]

/-- One double-and-add complete step at the `Point` level. -/
private theorem point_step_nsmul {P : Point Fp} (hP : P.OnCurve) (a : ℕ) (ha : 1 ≤ a)
    (bit : Bool) :
    a • P + ((if bit then P else -P) + a • P)
      = (2 * a + (if bit then 1 else 0) * 2 - 1) • P := by
  have hPv : P.Valid := Or.inl hP
  cases bit
  · -- bit = false: the step point is −P
    simp only [Bool.false_eq_true, if_false]
    apply (ext_toSW_iff
      (valid_add (valid_nsmul hPv a) (valid_add (valid_neg hPv) (valid_nsmul hPv a)))
      (valid_nsmul hPv _)).mpr
    rw [toSW_add (valid_nsmul hPv a) (valid_add (valid_neg hPv) (valid_nsmul hPv a)),
      toSW_add (valid_neg hPv) (valid_nsmul hPv a), toSW_neg hPv,
      toSW_nsmul hPv a, toSW_nsmul hPv]
    simpa using Ecc.Mul.nsmul_step (P.toSW hPv) a ha false
  · -- bit = true: the step point is P
    simp only [if_true]
    apply (ext_toSW_iff
      (valid_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)))
      (valid_nsmul hPv _)).mpr
    rw [toSW_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)),
      toSW_add hPv (valid_nsmul hPv a),
      toSW_nsmul hPv a, toSW_nsmul hPv]
    simpa using Ecc.Mul.nsmul_step (P.toSW hPv) a ha true

/-- `-P + m•P = (m−1)•P` at the `Point` level. -/
private theorem point_neg_add_nsmul {P : Point Fp} (hP : P.OnCurve) {m : ℕ} (hm : 1 ≤ m) :
    -P + m • P = (m - 1) • P := by
  have hPv : P.Valid := Or.inl hP
  apply (ext_toSW_iff (valid_add (valid_neg hPv) (valid_nsmul hPv m))
    (valid_nsmul hPv _)).mpr
  rw [toSW_add (valid_neg hPv) (valid_nsmul hPv m), toSW_neg hPv, toSW_nsmul hPv m,
    toSW_nsmul hPv]
  exact Ecc.Mul.neg_add_nsmul (P.toSW hPv) hm

/-- `0 + Q = Q` at the `Point` level, for valid `Q`. -/
private theorem point_zero_add {Q : Point Fp} (hQ : Q.Valid) : (0 : Point Fp) + Q = Q := by
  apply (ext_toSW_iff (valid_add valid_zero hQ) hQ).mpr
  rw [toSW_add valid_zero hQ, toSW_zero, _root_.zero_add]

/-- `Q + 0 = Q` at the `Point` level, for valid `Q`. -/
private theorem point_add_zero {Q : Point Fp} (hQ : Q.Valid) : Q + (0 : Point Fp) = Q := by
  apply (ext_toSW_iff (valid_add hQ valid_zero) hQ).mpr
  rw [toSW_add hQ valid_zero, toSW_zero, _root_.add_zero]

/-- Reducing the scalar by the group order: `(a + q)•P = a•P` (`[q]P = 0`). -/
private theorem point_card_reduce {P : Point Fp} (hP : P.OnCurve) (a : ℕ) :
    (a + PALLAS_SCALAR_CARD) • P = a • P := by
  rw [← nsmul_add_nsmul hP a PALLAS_SCALAR_CARD,
    (nsmul_eq_zero_iff hP PALLAS_SCALAR_CARD).mpr dvd_rfl,
    point_add_zero (valid_nsmul (Or.inl hP) a)]

/-- `accScalar` stays positive from a positive start. -/
private theorem accScalar_one_le {m : ℕ} (h1 : 1 ≤ m) (bits : ℕ → Bool) :
    ∀ b, 1 ≤ accScalar m bits b
  | 0 => h1
  | b + 1 => by
    have ih := accScalar_one_le h1 bits b
    show 1 ≤ 2 * accScalar m bits b + (if bits b then 1 else 0) * 2 - 1
    cases bits b
    · simp
      omega
    · simp

/-- `MulComplete.stepBasePoint` is `±base` (the `Point` negation is `y`-negation). -/
private theorem stepBasePoint_eq (P : Point Fp) (bit : Bool) :
    MulComplete.stepBasePoint P bit = if bit then P else -P := by
  cases bit <;> rfl

/-- The complete-rounds accumulator chain computes double-and-add on `Point` multiples:
starting from `[m]P`, after `b` rounds it holds `[accScalar m bits b]P` (at the `Point` level
via `point_step_nsmul`). -/
private theorem accPoint_nsmul {P : Point Fp} (hP : P.OnCurve) (m : ℕ) (hm : 1 ≤ m)
    (bits : ℕ → Bool) :
    ∀ b, MulComplete.accPoint P (m • P) bits b = accScalar m bits b • P
  | 0 => rfl
  | b + 1 => by
    have ih := accPoint_nsmul hP m hm bits b
    have h1 := accScalar_one_le hm bits b
    show MulComplete.stepPoint P (MulComplete.accPoint P (m • P) bits b) (bits b) = _
    rw [ih]
    show accScalar m bits b • P
        + (MulComplete.stepBasePoint P (bits b) + accScalar m bits b • P) = _
    rw [stepBasePoint_eq]
    exact point_step_nsmul hP _ h1 (bits b)

end PointAlgebra

/-! ## Output-record and cell-eval bridges -/

/-- Literal-eval bridge for `MulComplete.Output 3` (verifier view; the `acc` field may be a
symbolic term). -/
private theorem completeOutput_eval_literal (place : RegionIndex → ℕ)
    (env : Environment Fp) (acc : Point (AssignedCell Fp))
    (zs : Vector (AssignedCell Fp) 3) :
    ProvableStruct.Halo2.eval place env
        ({ acc := acc, zs := zs } : MulComplete.Output 3 (AssignedCell Fp))
      = { acc := ProvableType.Halo2.eval place env acc,
          zs := ProvableType.Halo2.eval (M := fields 3) place env zs } := by
  simp only [circuit_norm, explicit_provable_type, ProvableType.Halo2.eval_fields_cells]

/-! ## Prover-side bridge duplicates (completeness)

The same record/cell eval bridges over `Placed ProverEnvironment` (the honest-witness side).
The children's verifier-`Spec` facts arrive at `env.toEnvironment` and reuse the verifier
bridges; only the `ProverSpec`/witness facts need these. Both sides meet at the same
`env.env.toEnvironment.advice` reads. -/

/-- The cell-reading scalar program's prover value is the cell's value. -/
private theorem fexpr_expr_eval_prover (env : Placed ProverEnvironment Fp)
    (c : AssignedCell Fp) :
    Witgen.MOver.eval (F := Fp) (V := AssignedCell Fp) (value := field) env
      (pure (.expr c) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) = eval env c := by
  simp only [circuit_norm, Witgen.MOver.eval, Witgen.eval_field, Witgen.FExprOver.eval]

/-- The two eval flavors agree on a cell-valued point (both are the advice reads). -/
private theorem point_eval_toEnv (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (v : Point (AssignedCell Fp)) :
    eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) v
      = eval (⟨place, env⟩ : Placed ProverEnvironment Fp) v := by
  rcases v with ⟨x, y⟩
  simp [circuit_norm]

/-- The LSB bit program's prover value: `kBitsWindow` of the scalar cell's value. -/
private theorem kBitWindowExpr_expr_eval (env : Placed ProverEnvironment Fp)
    (c : AssignedCell Fp) (w i : ℕ) :
    Witgen.BExprOver.eval { env := env } (MulComplete.kBitWindowExpr (.expr c) w i)
      = kBitsWindow (readCell env c) w i := by
  have h := congrFun (MulComplete.bexprsVal_kBitWindowExpr (.expr c) w { env := env }) i
  simp only [MulComplete.bexprsVal] at h
  rw [h]
  simp only [circuit_norm, readCell, AssignedCell.eval]

/-- Prover-side componentwise eval of `Add.Inputs`. -/
private theorem addInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : Add.Inputs (AssignedCell Fp)) = { p := eval env p, q := eval env q } := by
  simp only [circuit_norm, ProvableType.Halo2.eval_cells_prover, ProvableType.Halo2.eval_cells]

/-- Split a `zChain` into the start equation and the step family (the shape
`chain_cast` consumes). -/
private theorem zChain_split {n : ℕ} {zin : Fp} {zs : Vector Fp (n + 1)} {bits : ℕ → Bool}
    (h : MulIncomplete.zChain zin zs bits) :
    zs[0] = 2 * zin + (if bits 0 then 1 else 0) ∧
    ∀ b : Fin n, zs[b.val + 1]'(by omega)
      = 2 * zs[b.val]'(by omega) + (if bits (b.val + 1) then 1 else 0) := by
  constructor
  · have h0 := h ⟨0, by omega⟩
    simpa using h0
  · intro b
    have hb := h ⟨b.val + 1, by omega⟩
    simp only [Fin.getElem_fin] at hb
    rw [dif_neg (show ¬ (b.val + 1 = 0) by omega)] at hb
    simpa using hb

/-- Prover-side `acc`-component of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_acc_prover (env : Placed ProverEnvironment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).acc
      = eval env acc := by
  rw [ProvableStruct.Halo2.eval_var_eq_eval_prover, completeOutput_eval_literal,
    ProvableType.Halo2.eval_cells_prover]

/-! ## Composition ergonomics

Input-record eval decompositions (`hiInputs_eval_eq` &c.) fire under `rw` but not under
`simp only` on engine-produced eval terms — the instance spelling differs from a
locally-elaborated one, so every decomposition site below is a `rw`. -/

/-- Eval of a `MulIncomplete.Inputs` record (componentwise; the scalar slot is a prover
hint, its verifier value is trivial). Stated over a whole var — a mixed-record literal
admits no `Eval`-synthesizable ascription — so use sites `rw` it and the literal's
projections reduce definitionally. -/
theorem hiInputs_eval_eq (env : Placed Environment Fp) (v : Var MulIncomplete.Inputs Fp) :
    eval env v
      = { alpha := (), base := eval env (v.base : Point (AssignedCell Fp)),
          acc := eval env (v.acc : Point (AssignedCell Fp)),
          z := eval env (v.z : AssignedCell Fp) } := by
  simp only [circuit_norm]

/-- Verifier: an abstract point-output var's coordinate-evals reassemble to its whole-point eval
(`Point.ofCoords (eval env o.x, eval env o.y) ≡ eval env o`), so an entering accumulator threaded
through the opaque local `o` lands on the whole-point value equation. `rfl` by `ProvableType`-eval
unfolding (`Point` is a two-field `Var`). -/
theorem point_var_eval_eq (env : Placed Environment Fp) (o : Var Point Fp) :
    eval env o = ({ x := eval env o.x, y := eval env o.y } : Point Fp) := by
  simp only [circuit_norm, explicit_provable_type]

/-- Prover view of `point_var_eval_eq`. -/
theorem point_var_eval_eq_prover (env : Placed ProverEnvironment Fp) (o : Var Point Fp) :
    eval env o = ({ x := eval env o.x, y := eval env o.y } : Point Fp) := by
  simp only [circuit_norm, explicit_provable_type]

/-! ## The gadget bundle

The working-scalar bits are derived from the `alpha` cell (`kBitsWindow`, windows 0/125/251 for
hi/lo/complete and the LSB read); the verifier `Spec` recovers a matching sequence via the
children's existential specs plus the canonicity argument. -/

-- The main region's composed do-block is one nested-bind term ~5 children deep; naive `.output`
-- reduction can explode the unifier at the complete-phase/final-add value-bookkeeping sites. Both
-- bundle proofs run `abstract_outputs` (after `provable_type_simp`, before `subcircuit_rw`): every
-- child output becomes an opaque `x_gen_out_j` local, so each chained chunk input (the complete
-- chunk's hi→lo input, the final add's complete-output input) is shallow by construction.
-- Downstream `rw`/`simp` sees the shallow local; the concrete child output is recovered via the
-- `h_gen_out_j` equations only where a single child `.output` must be reduced. The raw main-region
-- output feeding the overflow chunk is abstracted too (`x_gen_out_4` in completeness).
/-- The main region's outputs: the result point and the three running-sum cells the
overflow check consumes (`z_0` the full sum, `z_130` the hi chain, `k_254` the top bit). -/
structure MainOutputs (F : Type) where
  result : Point F
  z0 : F
  z130 : F
  k254 : F
deriving ProvableStruct

/-- The main double-and-add region as a bundle. `Spec` is the pre-overflow seam: some bit
families drive the three chained double-and-add phases plus the constraint-forced LSB, the
running-sum cells carry their chain values, and the result is the assembled scalar
multiple `[2^254 + 2·K + k₀] base`. The overflow contract then rules out the non-canonical
readings (`mul.soundness`). -/
def mainCircuit : FormalRegionCircuit Fp Config Config Inputs MainOutputs where
  configure := pure

  synthesize cfg _ input := do
    let acc ← Add.add.call cfg.addConfig offInit ⟨input.base, input.base⟩
    let zInit ← assignAdvice cfg.hiConfig.z offHi (.ofFExpr (.const 0))
    constrainConstant zInit 0
    let hi ← (MulIncomplete.double_and_add 124 0).call cfg.hiConfig offHi
      ⟨(pure (.expr input.alpha) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)),
        input.base, acc, zInit⟩
    let z130 ← cellAt cfg.hiConfig.z (offHi + 1 + 124)
    let k254 ← cellAt cfg.hiConfig.z (offHi + 1)
    let lo ← (MulIncomplete.double_and_add 125 125).call cfg.loConfig offLo
      ⟨(pure (.expr input.alpha) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)),
        input.base, hi.acc, z130⟩
    let zLo ← cellAt cfg.loConfig.z (offLo + 1 + 125)
    let comp ← (MulComplete.assign_region 3 251).call cfg.completeConfig offComp
      ⟨(pure (.expr input.alpha) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)),
        input.base, lo.acc.x, lo.acc.y, zLo⟩
    let z1 ← cellAt cfg.completeConfig.zComplete (offComp + 2 * 2 + 2)
    let z0 ← assignAdvice cfg.completeConfig.zComplete (offLsb + 1)
      (.ofFExpr (.add (.mul (.const 2) (.expr z1))
        (.ite (MulComplete.kBitWindowExpr (.expr input.alpha) 254 0) (.const 1) (.const 0))))
    let _bx ← copyAdvice input.base.x cfg.addConfig.xP (offLsb + 1)
    let _by ← copyAdvice input.base.y cfg.addConfig.yP (offLsb + 1)
    let corrX ← assignAdvice cfg.addConfig.xP offLsb
      (.ofFExpr (.ite (MulComplete.kBitWindowExpr (.expr input.alpha) 254 0)
        (.const 0) (.expr input.base.x)))
    let corrY ← assignAdvice cfg.addConfig.yP offLsb
      (.ofFExpr (.ite (MulComplete.kBitWindowExpr (.expr input.alpha) 254 0)
        (.const 0) (Witgen.FExprOver.neg (.expr input.base.y))))
    (lsbGate cfg).enable offLsb
    let result ← Add.add.call cfg.addConfig offLsb
      ⟨{ x := corrX, y := corrY }, comp.acc⟩
    return { result, z0, z130, k254 }

  elaborated :=
    { keygenRequirements :=
        { configLawful cfg :=
            Add.add.Configured cfg.addConfig ×
              (MulIncomplete.double_and_add 124 0).Configured cfg.hiConfig ×
              (MulIncomplete.double_and_add 125 125).Configured cfg.loConfig ×
              (MulComplete.assign_region 3 251).Configured cfg.completeConfig
          gates cfg configured :=
            [lsbGate cfg] ++ configured.1.gates ++ configured.2.1.gates ++
              configured.2.2.1.gates ++ configured.2.2.2.gates
          lookups _ configured :=
            configured.1.lookups ++ configured.2.1.lookups ++
              configured.2.2.1.lookups ++ configured.2.2.2.lookups
          permutationColumns _ configured :=
            configured.1.permutationColumns ++ configured.2.1.permutationColumns ++
              configured.2.2.1.permutationColumns ++ configured.2.2.2.permutationColumns
          inputPermutationColumns _ _ input :=
            [input.base.x.cell.column, input.base.y.cell.column] }
      registered := by
        keygen_registration
      output cfg _ _ self :=
        { result :=
            { x := .of self (offLsb + 1) cfg.addConfig.xQR
              y := .of self (offLsb + 1) cfg.addConfig.yQR }
          z0 := .of self (offLsb + 1) cfg.completeConfig.zComplete
          z130 := .of self (offHi + 1 + 124) cfg.hiConfig.z
          k254 := .of self (offHi + 1) cfg.hiConfig.z }
      output_eq := by
        intro _ _ _ _
        simp only [circuit_norm, keygen_output_norm] }

  Assumptions input := (input.base : Point Fp).OnCurve

  Spec input out _ :=
    ∃ (bitsHi bitsLo bitsC : ℕ → Bool) (k0 : Bool),
      out.k254 = (if bitsHi 0 then 1 else 0) ∧
      out.z130 = ((chainNat 0 bitsHi 125 : ℕ) : Fp) ∧
      out.z0 = ((2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3
          + (if k0 then 1 else 0) : ℕ) : Fp) ∧
      out.result = (2 ^ 254 + 2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3
          + (if k0 then 1 else 0)) • (input.base : Point Fp) ∧
      (out.result : Point Fp).Valid

  ProverAssumptions input _ _ := (input.base : Point Fp).OnCurve

  -- honest cell values: the three running sums read off the honest scalar (`kNat`).
  -- (No honest result-value clause: the parent's completeness needs only the cells, for
  -- the overflow child's honest `Spec`.)
  ProverSpec input out _ _ :=
    out.z0 = ((kNat input.alpha : ℕ) : Fp) ∧
    out.z130 = ((kNat input.alpha / 2 ^ 130 : ℕ) : Fp) ∧
    out.k254 = ((kNat input.alpha / 2 ^ 254 : ℕ) : Fp)

  soundness := by
    circuit_proof_start2 [Add.add, MulIncomplete.double_and_add, MulComplete.assign_region,
      lsbGate]
    have hbaseV : ({ x := input_base_x, y := input_base_y } : Point Fp).Valid := Or.inl assumptions
    -- init add: acc = base + base = [2]base
    obtain ⟨hAccV, hAcc2⟩ := acc_spec hbaseV
    rw [point_two_nsmul assumptions] at hAcc2
    -- hi half: ∃ bitsHi, RoundInvariant 125
    obtain ⟨bitsHi, hHiRI⟩ := hi_spec assumptions
    simp only [MulIncomplete.RoundInvariant] at hHiRI
    obtain ⟨hHiChain, hHiAccCl⟩ := hHiRI
    obtain ⟨hHiZ0, hHiZstep⟩ := zChain_split hHiChain
    -- the hi running-sum chain, as chainNat casts (entering z = 0 by `region_0`)
    have hHiCells := chain_cast (n := 124) _ _ 0 bitsHi (by rw [region_0, Nat.cast_zero])
      hHiZ0 hHiZstep
    -- the hi accumulator: [accScalar 2 bitsHi 125] • base
    have hHiOut := hHiAccCl 2 (by rw [hAcc2]) (le_refl 2) (by norm_num)
    -- the hi z-cell 124 (= z₁₃₀) and z-cell 0 (= k₂₅₄), as chainNat casts on the output cells
    have hHiZ124 := hHiCells 124 (by omega)
    rw [← hi_eq] at hHiZ124
    simp only [keygen_output_norm] at hHiZ124
    simp only [circuit_norm, Vector.getElem_ofFn] at hHiZ124
    have hK254v := hHiCells 0 (by omega)
    rw [← hi_eq] at hK254v
    simp only [keygen_output_norm] at hK254v
    simp only [circuit_norm, Vector.getElem_ofFn] at hK254v
    -- the output cells (`output_eq` components)
    obtain ⟨⟨hOResX, hOResY⟩, hOZ0, hOZ130, hOK254⟩ := output_eq
    have hResult : eval (⟨place, env⟩ : Placed Environment Fp) result =
        ({ x := output_result_x, y := output_result_y } : Point Fp) := by
      rw [← result_eq]
      simp only [keygen_output_norm, circuit_norm, hOResX, hOResY]
    -- the hi accumulator at its concrete cells
    rw [← hi_eq] at hHiOut
    simp only [keygen_output_norm] at hHiOut
    simp only [circuit_norm] at hHiOut
    -- lo half: ∃ bitsLo, RoundInvariant 126 with entering z = z₁₃₀, entering acc = hi.acc
    obtain ⟨bitsLo, hLoRI⟩ := lo_spec assumptions
    simp only [MulIncomplete.RoundInvariant] at hLoRI
    obtain ⟨hLoChain, hLoAccCl⟩ := hLoRI
    obtain ⟨hLoZ0, hLoZstep⟩ := zChain_split hLoChain
    -- the lo chain continues the hi chain
    have hLoCells := chain_cast (n := 125) _ _ (chainNat 0 bitsHi 125) bitsLo
      (by rw [hOZ130.symm.trans hHiZ124]) hLoZ0 hLoZstep
    -- the lo accumulator, entering at m = accScalar 2 bitsHi 125
    have hmB := m_bounds bitsHi bitsLo
    have hLoOut := hLoAccCl (accScalar 2 bitsHi 125)
      (by rw [← hi_eq]
          simp only [keygen_output_norm]
          simp only [circuit_norm]
          exact hHiOut)
      hmB.1 hmB.2.1
    rw [← lo_eq] at hLoOut
    simp only [keygen_output_norm] at hLoOut
    simp only [circuit_norm] at hLoOut
    -- complete rounds: ∃ bitsC, RoundInvariant 3 with entering acc = lo.acc
    have hM2pos : 1 ≤ accScalar (accScalar 2 bitsHi 125) bitsLo 126 := hmB.2.2.1
    rw [← lo_eq] at comp_spec
    simp only [keygen_output_norm, circuit_norm] at comp_spec
    obtain ⟨bitsC, hCompRI⟩ := comp_spec
      ⟨by rw [hLoOut]; exact Point.valid_nsmul hbaseV _, hbaseV⟩
    simp only [MulComplete.RoundInvariant] at hCompRI
    obtain ⟨hCompChain, hCompAccCl⟩ := hCompRI
    -- the complete-phase accumulator: [accScalar M₂ bitsC 3] • base, valid
    obtain ⟨hCompAccV, hCompAccEq⟩ := hCompAccCl
      (by rw [hLoOut]; exact Point.valid_nsmul hbaseV _) hbaseV
    rw [hLoOut, accPoint_nsmul assumptions _ hM2pos bitsC 3] at hCompAccEq
    -- the complete-phase z-chain, continued from the lo chain
    have hLoZ125 := hLoCells 125 (by omega)
    rw [← lo_eq] at hLoZ125
    simp only [keygen_output_norm] at hLoZ125
    simp only [circuit_norm, Vector.getElem_ofFn] at hLoZ125
    have hCompZ0 := hCompChain ⟨0, by omega⟩
    simp only [if_pos] at hCompZ0
    have hCompCells := chain_cast (n := 2) _ _
      (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC
      (by rw [hLoZ125]) hCompZ0
      (fun b => by
        have h := hCompChain ⟨b.val + 1, by omega⟩
        simpa using h)
    -- z₁ (= comp zs[2]) as a chainNat cast on its concrete cell
    have hz1cast := hCompCells 2 (by omega)
    rw [← comp_eq] at hz1cast
    simp only [keygen_output_norm] at hz1cast
    simp only [circuit_norm, Vector.getElem_ofFn] at hz1cast
    have hz1read : env.advice cfg.completeConfig.zComplete ((place self + offLsb : ℕ) : ℤ)
        = ((chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 : ℕ) : Fp) := by
      rw [show (offLsb : ℕ) = offComp + (2 * 2 + 2) from by simp only [offLsb, compSpan]]
      exact hz1cast
    -- the LSB gate: constraint-forced bit and correction point
    obtain ⟨hBool, hLsbX, hLsbY⟩ := region_3
    rw [region_1] at hLsbX
    rw [region_2] at hLsbY
    -- the final add's `q` summand and the comp accumulator, at the shared spelling
    rw [← comp_eq] at result_spec
    simp only [keygen_output_norm, circuit_norm] at result_spec
    rw [← comp_eq] at hCompAccV hCompAccEq
    simp only [keygen_output_norm, circuit_norm] at hCompAccV hCompAccEq
    -- the accumulated-scalar closed forms
    have hM3pos : 1 ≤ accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 :=
      accScalar_one_le hM2pos bitsC 3
    have hm1 : accScalar 2 bitsHi 125 = 2 ^ 125 + 2 * chainNat 0 bitsHi 125 + 1 := by
      rw [accScalar_closed 2 (by norm_num) bitsHi 125]
      norm_num
    have hm2 : accScalar (accScalar 2 bitsHi 125) bitsLo 126
        = 2 ^ 251 + 2 * chainNat (chainNat 0 bitsHi 125) bitsLo 126 + 1 := by
      rw [accScalar_closed _ (by rw [hm1]; omega) bitsLo 126, hm1,
        chainNat_offset (chainNat 0 bitsHi 125) bitsLo 126]
      norm_num
      omega
    have hm3 : accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3
        = 2 ^ 254 + 2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3
          + 1 := by
      rw [accScalar_closed _ (by rw [hm2]; omega) bitsC 3, hm2,
        chainNat_offset (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3]
      norm_num
      omega
    -- k₂₅₄ = the top bit
    have hK254bit : output_k254 = (if bitsHi 0 then (1 : Fp) else 0) := by
      rw [← hOK254, hK254v]
      rw [show ((chainNat 0 bitsHi 1 : ℕ) : Fp) = (if bitsHi 0 then 1 else 0) from by
        simp only [chainNat]; cases bitsHi 0 <;> simp]
    -- ── the LSB case split ──
    rcases mul_eq_zero.mp hBool with hk0 | hk1
    · -- k₀ = 0: the correction point is −base, the result is [M₃ − 1]•base
      refine ⟨bitsHi, bitsLo, bitsC, false, hK254bit, hOZ130.symm.trans hHiZ124, ?_, ?_, ?_⟩
      · -- z₀ = 2·z₁ + 0
        push_cast
        rw [hz1read] at hk0
        linear_combination hk0
      · -- result = [2^254 + 2K + 0]•base
        have hcx : env.advice cfg.addConfig.xP ((place self + offLsb : ℕ) : ℤ)
            = input_base_x := by
          linear_combination hLsbX - input_base_x * hk0
        have hcy : env.advice cfg.addConfig.yP ((place self + offLsb : ℕ) : ℤ)
            = -input_base_y := by
          linear_combination hLsbY + input_base_y * hk0
        obtain ⟨hResV, hResEq⟩ := result_spec
          ⟨by rw [hcx, hcy]; exact Point.valid_neg hbaseV, hCompAccV⟩
        rw [hcx, hcy, show ({ x := input_base_x, y := -input_base_y } : Point Fp)
              = -({ x := input_base_x, y := input_base_y } : Point Fp) from rfl,
          hCompAccEq, point_neg_add_nsmul assumptions hM3pos] at hResEq
        rw [← hResult]
        rw [hResEq]
        congr 1
        rw [hm3]
        simp
      · -- validity
        obtain ⟨hResV, -⟩ := result_spec
          ⟨by rw [show env.advice cfg.addConfig.xP ((place self + offLsb : ℕ) : ℤ)
                  = input_base_x from by linear_combination hLsbX - input_base_x * hk0,
                show env.advice cfg.addConfig.yP ((place self + offLsb : ℕ) : ℤ)
                  = -input_base_y from by linear_combination hLsbY + input_base_y * hk0]
              exact Point.valid_neg hbaseV, hCompAccV⟩
        rw [← hResult]
        exact hResV
    · -- k₀ = 1: the correction point is the identity, the result is [M₃]•base
      refine ⟨bitsHi, bitsLo, bitsC, true, hK254bit, hOZ130.symm.trans hHiZ124, ?_, ?_, ?_⟩
      · -- z₀ = 2·z₁ + 1
        push_cast
        simp only [if_true]
        rw [hz1read] at hk1
        linear_combination -hk1
      · have hcx : env.advice cfg.addConfig.xP ((place self + offLsb : ℕ) : ℤ) = 0 := by
          linear_combination hLsbX + input_base_x * hk1
        have hcy : env.advice cfg.addConfig.yP ((place self + offLsb : ℕ) : ℤ) = 0 := by
          linear_combination hLsbY - input_base_y * hk1
        obtain ⟨hResV, hResEq⟩ := result_spec
          ⟨by rw [hcx, hcy]; exact Point.valid_zero, hCompAccV⟩
        rw [hcx, hcy, show ({ x := 0, y := 0 } : Point Fp) = (0 : Point Fp) from rfl,
          hCompAccEq, point_zero_add (Point.valid_nsmul hbaseV _)] at hResEq
        rw [← hResult]
        rw [hResEq]
        congr 1
      · obtain ⟨hResV, -⟩ := result_spec
          ⟨by rw [show env.advice cfg.addConfig.xP ((place self + offLsb : ℕ) : ℤ) = 0 from by
                  linear_combination hLsbX + input_base_x * hk1,
                show env.advice cfg.addConfig.yP ((place self + offLsb : ℕ) : ℤ) = 0 from by
                  linear_combination hLsbY - input_base_y * hk1]
              exact Point.valid_zero, hCompAccV⟩
        rw [← hResult]
        exact hResV
  completeness := by
    circuit_proof_start2 [Add.add, MulIncomplete.double_and_add, MulComplete.assign_region,
      lsbGate]
    have hOnC : ({ x := input_base_x, y := input_base_y } : Point Fp).OnCurve := assumptions
    have hbaseV : ({ x := input_base_x, y := input_base_y } : Point Fp).Valid := Or.inl hOnC
    -- the honest working-scalar bits, as a local opaque constant
    obtain ⟨bits, hbits⟩ : ∃ b : BitsHint, b = kBits input_alpha := ⟨_, rfl⟩
    have hW0 : kBitsWindow input_alpha 0 = bits := by
      rw [kBitsWindow_zero, hbits]
    have hW251 : kBitsWindow input_alpha 251 = fun i => bits (251 + i) := by
      rw [kBitsWindow_as_kBits, hbits]
    have hBF0 : MulIncomplete.bitsFrom input_alpha 0 = bits := by
      funext j
      show kBitsWindow input_alpha 0 (0 + j) = bits j
      rw [Nat.zero_add]
      exact congrFun hW0 j
    have hBF125 : MulIncomplete.bitsFrom input_alpha 125 = fun i => bits (125 + i) := by
      funext j
      exact congrFun hW0 (125 + j)
    -- the LSB bit closure value: `bits 254`
    have hlsb : Witgen.BExprOver.eval { env := (⟨place, env⟩ : Placed ProverEnvironment Fp) }
        (MulComplete.kBitWindowExpr (Witgen.FExprOver.expr input_var_alpha) 254 0)
        = bits 254 := by
      rw [kBitWindowExpr_expr_eval, kBitsWindow_eq_kBits, hbits]
      congr 1
      exact input_eq.1
    rw [hlsb] at region_1 region_4 region_5
    obtain ⟨⟨hOResX, hOResY⟩, hOZ0, hOZ130, hOK254⟩ := output_eq
    -- init add: acc = [2]base (honest view)
    obtain ⟨hAccV, hAccEq⟩ := acc_spec hbaseV
    have hAcc2 : eval (⟨place, env⟩ : Placed ProverEnvironment Fp) acc
        = 2 • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      rw [← point_eval_toEnv, ← point_two_nsmul hOnC]
      exact hAccEq
    -- hi half: honest RoundInvariant over `bits`
    obtain ⟨-, hHiPS⟩ := hi_spec hOnC ⟨hOnC, 2, hAcc2, le_refl 2, by norm_num⟩
    have halphap : eval (⟨place, env⟩ : Placed ProverEnvironment Fp) input_var_alpha
        = input_alpha := by
      have h := input_eq.1
      simp only [circuit_norm] at h ⊢
      exact h
    simp only [MulIncomplete.RoundInvariant, hBF0] at hHiPS
    obtain ⟨hHiChain, hHiAccCl⟩ := hHiPS
    obtain ⟨hHiZ0, hHiZstep⟩ := zChain_split hHiChain
    have hentry : env.advice cfg.hiConfig.z ((place self + offHi : ℕ) : ℤ)
        = ((0 : ℕ) : Fp) := by
      rw [region_0]
      norm_num
    have hHiCells := chain_cast (n := 124) _ _ 0 bits hentry hHiZ0 hHiZstep
    have hHiOut := hHiAccCl 2 (by rw [hAcc2]) (le_refl 2) (by norm_num)
    rw [← hi_eq] at hHiOut
    simp only [keygen_output_norm] at hHiOut
    simp only [circuit_norm] at hHiOut
    have hHiZ124 := hHiCells 124 (by omega)
    rw [← hi_eq] at hHiZ124
    simp only [keygen_output_norm] at hHiZ124
    simp only [circuit_norm, Vector.getElem_ofFn] at hHiZ124
    have hHiZtop := hHiCells 0 (by omega)
    rw [← hi_eq] at hHiZtop
    simp only [keygen_output_norm] at hHiZtop
    simp only [circuit_norm, Vector.getElem_ofFn] at hHiZtop
    -- lo half: honest RoundInvariant, chained
    have hmB := m_bounds bits (fun i => bits (125 + i))
    have hHiAccP : eval (⟨place, env⟩ : Placed ProverEnvironment Fp) hi.acc
        = accScalar 2 bits 125 • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      rw [← hi_eq]
      simp only [keygen_output_norm, circuit_norm]
      exact hHiOut
    obtain ⟨-, hLoPS⟩ := lo_spec hOnC ⟨hOnC, accScalar 2 bits 125, hHiAccP, hmB.1, hmB.2.1⟩
    simp only [MulIncomplete.RoundInvariant, hBF125] at hLoPS
    obtain ⟨hLoChain, hLoAccCl⟩ := hLoPS
    obtain ⟨hLoZ0, hLoZstep⟩ := zChain_split hLoChain
    have hLoCells := chain_cast (n := 125) _ _ (chainNat 0 bits 125) (fun i => bits (125 + i))
      (by rw [← hOZ130]; exact hHiZ124) hLoZ0 hLoZstep
    have hLoOut := hLoAccCl (accScalar 2 bits 125) (by rw [hHiAccP]) hmB.1 hmB.2.1
    rw [← lo_eq] at hLoOut
    simp only [keygen_output_norm] at hLoOut
    simp only [circuit_norm] at hLoOut
    have hLoZ125 := hLoCells 125 (by omega)
    rw [← lo_eq] at hLoZ125
    simp only [keygen_output_norm] at hLoZ125
    simp only [circuit_norm, Vector.getElem_ofFn] at hLoZ125
    -- complete rounds: honest RoundInvariant
    rw [← lo_eq] at comp_spec
    simp only [keygen_output_norm, circuit_norm] at comp_spec
    obtain ⟨hCompSpecV, hCompPS⟩ := comp_spec
      ⟨by rw [hLoOut]; exact Point.valid_nsmul hbaseV _, hbaseV⟩
      ⟨by rw [hLoOut]; exact Point.valid_nsmul hbaseV _, hbaseV⟩
    obtain ⟨bitsC', hCompRIv⟩ := hCompSpecV
    simp only [MulComplete.RoundInvariant] at hCompRIv
    obtain ⟨-, hCompAccClv⟩ := hCompRIv
    obtain ⟨hCompAccVv, -⟩ := hCompAccClv
      (by rw [hLoOut]; exact Point.valid_nsmul hbaseV _) hbaseV
    simp only [MulComplete.RoundInvariant, hW251] at hCompPS
    obtain ⟨hCompChain, -⟩ := hCompPS
    have hCompZ0 := hCompChain ⟨0, by omega⟩
    simp only [if_pos] at hCompZ0
    have hCompCells := chain_cast (n := 2) _ _
      (chainNat (chainNat 0 bits 125) (fun i => bits (125 + i)) 126) (fun i => bits (251 + i))
      (by rw [hLoZ125]) hCompZ0
      (fun b => by
        have h := hCompChain ⟨b.val + 1, by omega⟩
        simpa using h)
    have hz1cast := hCompCells 2 (by omega)
    rw [← comp_eq] at hz1cast
    simp only [keygen_output_norm] at hz1cast
    simp only [circuit_norm, Vector.getElem_ofFn] at hz1cast
    -- the honest chain values, `kBits`-driven
    have hck := cells_kNat input_alpha
    rw [hbits] at hHiZtop hHiZ124 hz1cast
    rw [hck.1] at hHiZtop
    rw [hck.2.1] at hHiZ124
    rw [hck.2.2] at hz1cast
    -- the honest z₀ value
    rw [hz1cast, hbits] at region_1
    have hz0v : output_z0 = ((kNat input_alpha : ℕ) : Fp) := by
      refine z0_cell_value input_alpha rfl ?_
      exact region_1
    -- ── assemble: premise bundles + parent constraints + the honest cell values ──
    rw [← lo_eq, ← comp_eq]
    simp only [keygen_output_norm, circuit_norm]
    rw [← comp_eq] at hCompAccVv
    simp only [keygen_output_norm, circuit_norm] at hCompAccVv
    have hz1read : env.advice cfg.completeConfig.zComplete ((place self + offLsb : ℕ) : ℤ)
        = ((kNat input_alpha / 2 : ℕ) : Fp) := by
      rw [show (offLsb : ℕ) = offComp + (2 * 2 + 2) from by simp only [offLsb, compSpan]]
      exact hz1cast
    -- k₀ = z₀ − 2·z₁ splits off the honest LSB
    have hsplit : ((kNat input_alpha : ℕ) : Fp)
        = 2 * ((kNat input_alpha / 2 : ℕ) : Fp) + (if bits 254 then 1 else 0) := by
      rw [hbits]
      rw [show kBits input_alpha 254 = decide (kNat input_alpha % 2 = 1) from by
        unfold kBits; norm_num]
      rw [show ((kNat input_alpha : ℕ) : Fp)
        = ((2 * (kNat input_alpha / 2) + kNat input_alpha % 2 : ℕ) : Fp) from by
          congr 1; omega]
      push_cast
      rcases Nat.mod_two_eq_zero_or_one (kNat input_alpha) with h | h <;>
        rw [h] <;> simp
    rw [hbits] at region_4 region_5
    refine ⟨⟨hbaseV, region_0,
      ⟨hOnC, hOnC, 2, hAcc2, le_refl 2, by norm_num⟩,
      ⟨hOnC, hOnC, accScalar 2 bits 125, hHiAccP, hmB.1, hmB.2.1⟩,
      ⟨by rw [hLoOut]; exact Point.valid_nsmul hbaseV _, hbaseV⟩,
      region_2, region_3, ⟨?_, ?_, ?_⟩, ?_, hCompAccVv⟩,
      hz0v, by rw [← hOZ130]; exact hHiZ124, by rw [← hOK254]; exact hHiZtop⟩
    · -- bool_check on the honest bit
      rw [hz0v, hz1read, hsplit, hbits]
      rcases Bool.dichotomy (kBits input_alpha 254) with h | h <;>
        simp only [h, Bool.false_eq_true, if_false, if_true] <;> ring
    · -- x-switch on the honest correction point
      rw [hz0v, hz1read, hsplit, hbits, region_4, region_2]
      rcases Bool.dichotomy (kBits input_alpha 254) with h | h <;>
        simp only [h, Bool.false_eq_true, if_false, if_true] <;> ring
    · -- y-switch on the honest correction point
      rw [hz0v, hz1read, hsplit, hbits, region_5, region_3]
      rcases Bool.dichotomy (kBits input_alpha 254) with h | h <;>
        simp only [h, Bool.false_eq_true, if_false, if_true] <;> ring
    · -- the honest correction point is valid (identity or −base)
      rw [region_4, region_5]
      rcases Bool.dichotomy (kBits input_alpha 254) with h | h <;> rw [h]
      · simp only [Bool.false_eq_true, if_false]
        rw [show ({ x := input_base_x, y := -input_base_y } : Point Fp)
              = -{ x := input_base_x, y := input_base_y } from rfl]
        exact Point.valid_neg hbaseV
      · simp only [if_true]
        exact Point.valid_zero

@[keygen_output_norm]
theorem mainCircuit_output (cfg : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    (mainCircuit.toFormal "variable-base scalar mul").output cfg input self =
      { result :=
          { x := .of self (offLsb + 1) cfg.addConfig.xQR
            y := .of self (offLsb + 1) cfg.addConfig.yQR }
        z0 := .of self (offLsb + 1) cfg.completeConfig.zComplete
        z130 := .of self (offHi + 1 + 124) cfg.hiConfig.z
        k254 := .of self (offHi + 1) cfg.hiConfig.z } := by
  rfl

derive_contract_bridges main := mainCircuit.toFormal "variable-base scalar mul"

/-- The scalar-decomposition and recombination assembly, at the layouter level: the whole
double-and-add convergence runs in one region (the `mainCircuit` bundle), and the overflow
check runs after that region closes as a separate layouter-level `overflow_check` of three
sibling regions. The `z_0`/`z_130`/`k_254` cells cross into the overflow regions as copies.
Returns `[alpha] base`. -/
def synthesize (cfg : Config) (input : Var Inputs Fp) :
    Circuit Fp (Var Point Fp) := do
  -- the main double-and-add region
  let m ← (mainCircuit.toFormal "variable-base scalar mul").call cfg input
  -- the overflow check after the main region closes, at layouter level
  let _ov ← (MulOverflow.circuit 10 hKW10).call cfg.overflowConfig
    ⟨input.alpha, m.z0, m.z130, m.k254⟩
  return m.result

/-- The region count of `synthesize`: the main double-and-add region (1) plus the overflow
check's three sibling regions (`MulOverflow.circuit`'s regionCount, 3) = 4. -/
private theorem synthesize_regionCount (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.regionCount ((synthesize cfg input).operations i) = 4 := by
  simp only [synthesize, circuit_norm]

@[keygen_norm]
def keygenRequirements :
    KeygenRequirements Fp
      (Add.Config × LookupRangeCheck.Config 10 × (Fin 10 → Column .advice))
      (Var Inputs Fp) where
  configLawful input := Add.add.Configured input.1
  gates _ configured := configured.gates
  lookups input configured :=
    LookupRangeCheck.rangeCheckLookup 10 input.2.1 :: configured.lookups
  permutationColumns input configured :=
    ([input.2.1.runningSum, input.2.2 3, input.2.2 0,
      input.2.2 1, input.2.2 7] : List AnyColumn) ++ configured.permutationColumns
  inputPermutationColumns _ _ input :=
    [input.alpha.cell.column, input.base.x.cell.column, input.base.y.cell.column]

@[keygen_norm]
private theorem doubleAndAddRequirements_gates
    (n w : ℕ) (z xA xP yP lambda1 lambda2 : Column .advice)
    :
    (MulIncomplete.double_and_add n w).keygenRequirements.gates
      (z, xA, xP, yP, lambda1, lambda2) () = [] := by
  rfl

@[keygen_norm]
private theorem doubleAndAddRequirements_lookups
    (n w : ℕ) (z xA xP yP lambda1 lambda2 : Column .advice)
    :
    (MulIncomplete.double_and_add n w).keygenRequirements.lookups
      (z, xA, xP, yP, lambda1, lambda2) () = [] := by
  rfl

@[keygen_norm]
private theorem doubleAndAdd_configure
    (n w : ℕ) (z xA xP yP lambda1 lambda2 : Column .advice) :
    (MulIncomplete.double_and_add n w).configure
      (z, xA, xP, yP, lambda1, lambda2) =
        MulIncomplete.configure z xA xP yP lambda1 lambda2 := by
  rfl

@[keygen_norm]
private theorem completeRequirements_gates
    (numBits w : ℕ) (zComplete : Column .advice) (addConfig : Add.Config)
    (hconfig : Add.add.Configured addConfig) :
    (MulComplete.assign_region numBits w).keygenRequirements.gates
      (zComplete, addConfig) hconfig = hconfig.gates := by
  rfl

@[keygen_norm]
private theorem completeRequirements_lookups
    (numBits w : ℕ) (zComplete : Column .advice) (addConfig : Add.Config)
    (hconfig : Add.add.Configured addConfig) :
    (MulComplete.assign_region numBits w).keygenRequirements.lookups
      (zComplete, addConfig) hconfig = hconfig.lookups := by
  rfl

@[keygen_norm]
private theorem complete_configure
    (numBits w : ℕ) (zComplete : Column .advice) (addConfig : Add.Config) :
    (MulComplete.assign_region numBits w).configure (zComplete, addConfig) =
      MulComplete.configure zComplete addConfig := by
  rfl

@[keygen_configured]
private def mainConfigured
    (configInput :
      Add.Config × LookupRangeCheck.Config 10 × (Fin 10 → Column .advice))
    (counts : ConfigureCounts)
    (hconfig : keygenRequirements.configLawful configInput) :
    (mainCircuit.toFormal "variable-base scalar mul").Configured
      ((configure configInput.1 configInput.2.1 configInput.2.2).output counts) := by
  let advices := configInput.2.2
  let hiProgram :=
    MulIncomplete.configure (advices 9) (advices 3) (advices 0)
      (advices 1) (advices 4) (advices 5)
  let loProgram :=
    MulIncomplete.configure (advices 6) (advices 7) (advices 0)
      (advices 1) (advices 8) (advices 2)
  let completeProgram := MulComplete.configure (advices 9) configInput.1
  apply FormalCircuit.Configured.ofPure
  · refine ⟨hconfig, ?_, ?_, ?_⟩
    · exact FormalRegionCircuit.Configured.ofOutput
        (MulIncomplete.double_and_add 124 0)
        (advices 9, advices 3, advices 0, advices 1, advices 4, advices 5)
        counts ()
    · exact FormalRegionCircuit.Configured.ofOutput
        (MulIncomplete.double_and_add 125 125)
        (advices 6, advices 7, advices 0, advices 1, advices 8, advices 2)
        (hiProgram.finalCounts counts) ()
    · exact FormalRegionCircuit.Configured.ofOutput
        (MulComplete.assign_region 3 251) (advices 9, configInput.1)
        (loProgram.finalCounts (hiProgram.finalCounts counts)) hconfig
  · rfl

@[keygen_configured]
private def overflowConfigured
    (configInput :
      Add.Config × LookupRangeCheck.Config 10 × (Fin 10 → Column .advice))
    (counts : ConfigureCounts) :
    (MulOverflow.circuit 10 hKW10).Configured
      ((configure configInput.1 configInput.2.1 configInput.2.2).output
        counts).overflowConfig := by
  let advices := configInput.2.2
  let hiProgram :=
    MulIncomplete.configure (advices 9) (advices 3) (advices 0)
      (advices 1) (advices 4) (advices 5)
  let loProgram :=
    MulIncomplete.configure (advices 6) (advices 7) (advices 0)
      (advices 1) (advices 8) (advices 2)
  let completeProgram := MulComplete.configure (advices 9) configInput.1
  exact FormalCircuit.Configured.ofOutput
    (MulOverflow.circuit 10 hKW10)
    (configInput.2.1, advices 6, advices 7, advices 8)
    (completeProgram.finalCounts
      (loProgram.finalCounts (hiProgram.finalCounts counts))) ()

/-- Variable-base scalar multiplication by a base-field element: `[alpha] base`. A
layouter-level `FormalCircuit`: the main double-and-add region plus the overflow check's three
sibling regions after it. No `BitsHint` parameter — the working-scalar bits are derived from the
`alpha` cell inside the witness IR. -/
def mul :
    FormalCircuit Fp
      (Add.Config × LookupRangeCheck.Config 10 × (Fin 10 → Column .advice))
      Config Inputs Point where
  name := "variable-base scalar mul"

  configure := fun (addConfig, lookupConfig, advices) =>
    configure addConfig lookupConfig advices

  synthesize cfg input := synthesize cfg input

  elaborated :=
    { keygenRequirements
      registered := by
        intro configInput counts hconfig input i
        simp only [synthesize, Circuit.operations_bind, Circuit.operations_pure,
          Operations.KeygenRegistered.append, Operations.KeygenRegistered.nil,
          and_true]
        constructor
        · apply FormalCircuit.call_keygenRegistered _ _
            (mainConfigured configInput counts hconfig)
          · intro gate hgate
            simp only [mainConfigured, FormalCircuit.Configured.ofPure_gates,
              FormalRegionCircuit.toFormal_keygenRequirements, mainCircuit,
              FormalRegionCircuit.keygenRequirements,
              ElaboratedRegionCircuit.keygenRequirements] at hgate
            simp only [FormalRegionCircuit.Configured.gates,
              doubleAndAddRequirements_gates, completeRequirements_gates,
              FormalRegionCircuit.keygenRequirements, keygen_norm, configure,
              keygenRequirements] at hgate ⊢
            aesop
          · intro argument hargument
            simp only [mainConfigured, FormalCircuit.Configured.ofPure_lookups,
              FormalRegionCircuit.toFormal_keygenRequirements, mainCircuit,
              FormalRegionCircuit.keygenRequirements,
              ElaboratedRegionCircuit.keygenRequirements] at hargument
            simp only [FormalRegionCircuit.Configured.lookups,
              doubleAndAddRequirements_lookups, completeRequirements_lookups,
              FormalRegionCircuit.keygenRequirements, keygen_norm, configure,
              keygenRequirements] at hargument ⊢
            aesop
          · intro column hcolumn
            simp only [mainConfigured,
              FormalCircuit.Configured.ofPure_permutationColumns,
              FormalRegionCircuit.toFormal_keygenRequirements, mainCircuit,
              FormalRegionCircuit.keygenRequirements,
              ElaboratedRegionCircuit.keygenRequirements] at hcolumn
            simp only [FormalRegionCircuit.Configured.permutationColumns,
              FormalRegionCircuit.keygenRequirements,
              ElaboratedRegionCircuit.keygenRequirements,
              MulIncomplete.double_and_add, MulComplete.assign_region,
              keygen_norm, configure, keygenRequirements] at hcolumn ⊢
            aesop
          · intro column hcolumn
            simp only [mainConfigured,
              FormalCircuit.Configured.ofPure_inputPermutationColumns,
              FormalRegionCircuit.toFormal_keygenRequirements, mainCircuit,
              FormalRegionCircuit.keygenRequirements,
              ElaboratedRegionCircuit.keygenRequirements, keygen_norm,
              keygenRequirements] at hcolumn ⊢
            aesop
        · apply FormalCircuit.call_keygenRegistered _ _
            (overflowConfigured configInput counts)
          · intro gate hgate
            simp only [keygen_norm, configure, overflowConfigured,
              keygenRequirements,
              FormalCircuit.Configured.gates, FormalCircuit.keygenRequirements,
              MulOverflow.circuit, ElaboratedCircuit.keygenRequirements] at hgate ⊢
            aesop
          · intro argument hargument
            simp only [keygen_norm, configure, overflowConfigured,
              keygenRequirements,
              FormalCircuit.Configured.lookups, FormalCircuit.keygenRequirements,
              MulOverflow.circuit, ElaboratedCircuit.keygenRequirements] at hargument ⊢
            aesop
          · intro column hcolumn
            simp only [keygen_norm, configure, overflowConfigured,
              keygenRequirements,
              FormalCircuit.Configured.permutationColumns,
              FormalCircuit.keygenRequirements, MulOverflow.circuit,
              ElaboratedCircuit.keygenRequirements] at hcolumn ⊢
            aesop
          · intro column hcolumn
            simp only [keygen_norm, configure, overflowConfigured,
              FormalCircuit.Configured.inputPermutationColumns,
              FormalCircuit.keygenRequirements, MulOverflow.circuit,
              ElaboratedCircuit.keygenRequirements, keygen_output_norm] at hcolumn
            rcases hcolumn with rfl | hcolumn | hcolumn
            · apply List.mem_append_right
              simp only [keygenRequirements, List.mem_cons, true_or]
            · subst column
              apply List.mem_append_left
              apply List.mem_append_right
              rw [MulComplete.configure_output_zComplete]
              have hcolumn := MulComplete.configure_output_zComplete_mem_permutationRequests
                (configInput.2.2 9) configInput.1
                  ((MulIncomplete.configure (configInput.2.2 6) (configInput.2.2 7)
                    (configInput.2.2 0) (configInput.2.2 1) (configInput.2.2 8)
                    (configInput.2.2 2)).finalCounts
                      ((MulIncomplete.configure (configInput.2.2 9) (configInput.2.2 3)
                        (configInput.2.2 0) (configInput.2.2 1) (configInput.2.2 4)
                        (configInput.2.2 5)).finalCounts counts))
              unfold configure
              apply Configure.mem_permutationRequests_delta_bind_right
              apply Configure.mem_permutationRequests_delta_bind_right
              apply Configure.mem_permutationRequests_delta_bind_left
              exact hcolumn
            · subst column
              apply List.mem_append_left
              apply List.mem_append_right
              have hcolumn : (configInput.2.2 9).toAny ∈
                  ((MulIncomplete.configure (configInput.2.2 9) (configInput.2.2 3)
                    (configInput.2.2 0) (configInput.2.2 1) (configInput.2.2 4)
                    (configInput.2.2 5)).delta counts).permutationRequests := by
                unfold MulIncomplete.configure
                apply Configure.mem_permutationRequests_delta_bind_left
                exact Configure.mem_permutationRequests_delta_enableEquality _ _
              unfold configure
              apply Configure.mem_permutationRequests_delta_bind_left
              exact hcolumn
      output cfg _ self :=
        { x := .of self (offLsb + 1) cfg.addConfig.xQR
          y := .of self (offLsb + 1) cfg.addConfig.yQR }
      regionCount _ := 4
      output_eq := by
        intro _ _ _
        unfold synthesize
        rw [Circuit.output_bind, FormalCircuit.output_call', Circuit.output_bind,
          Circuit.output_pure, mainCircuit_output]
      regionCount_eq := fun cfg input i => (synthesize_regionCount cfg input i).symm }

  EnvAssumptions cfg env := EnvAssumptions cfg env

  Assumptions input := Assumptions input

  Spec input output _ := Spec input output

  -- honest-prover precondition: base on-curve (the working-scalar bits are DERIVED from the
  -- alpha cell — nothing to assume about them).
  ProverAssumptions input _ _ :=
    (input.base : Point Fp).OnCurve

  -- The honest-side output-value guarantee is deliberately `True`: the verifier-facing
  -- `Spec` (proven in `soundness`) is the correctness carrier, and no parent consumes `mul`
  -- as a child yet. A future chip-level caller needing the honest output value can
  -- strengthen this to `Spec` and extend `completeness` with the honest point algebra
  -- (the same ladder as the `soundness` finish, over the witness values).
  ProverSpec _ _ _ _ := True

  -- ══ Soundness ══
  -- Layouter peel (main region + the MulOverflow chunk), the six child chunks consumed via
  -- `subcircuit_rw`, the LSB gate, and the canonicity finish.
  soundness := by
    circuit_proof_start2 [mainCircuit, MulOverflow.circuit, Spec, Assumptions,
      EnvAssumptions]
    simp only [main_spec_eq, main_assumptions_eq, main_envAssumptions_eq] at m_spec
    obtain ⟨bitsHi, bitsLo, bitsC, k0, hK254, hZ130, hZ0, hResEq, hResV⟩ :=
      m_spec trivial assumptions
    have hmResult := congrArg MainOutputs.result m_eq
    rw [mainCircuit_output] at hmResult
    simp only at hmResult
    have hResult :
        eval (⟨place, env⟩ : Placed Environment Fp) m_result =
          ({ x := output_x, y := output_y } : Point Fp) := by
      rw [← hmResult, Point.eval_eq]
      simp only [circuit_norm, output_eq.1, output_eq.2]
    have hOvSpec := ov_spec env_assumptions
      (by constructor <;> norm_num [MulOverflow.numWords, PALLAS_BASE_CARD])
    rw [show (MulOverflow.Spec = fun input => input.z0 = input.alpha + (tQ : Fp) ∧
        (input.k254 = 0 ∨ input.z130 = (2 ^ 124 : Fp)) ∧
        ∃ (sHi : Fp) (sLo : ℕ), sLo < 2 ^ 130 ∧
          input.alpha + input.k254 * (2 ^ 130 : Fp) = (sLo : Fp) + (2 ^ 130 : Fp) * sHi ∧
          (input.k254 = 0 ∨ sHi = 0) ∧
          (input.k254 = 1 ∨ input.z130 ≠ 0 ∨ sHi = 0)) from rfl] at hOvSpec
    obtain ⟨hOvZ0, hOvDisj2, hOvEx⟩ := hOvSpec
    -- ── the canonicity ladder ──
    have hZhiLt : chainNat 0 bitsHi 125 < 2 ^ 125 :=
      lt_of_lt_of_le (chainNat_lt 0 bitsHi 125) (by norm_num)
    have hCloLt : chainNat 0 bitsLo 126 < 2 ^ 126 :=
      lt_of_lt_of_le (chainNat_lt 0 bitsLo 126) (by norm_num)
    have hCcLt : chainNat 0 bitsC 3 < 2 ^ 3 :=
      lt_of_lt_of_le (chainNat_lt 0 bitsC 3) (by norm_num)
    -- the canonicity argument: the witnessed scalar is α + t_q over ℕ
    have hKpart : ∀ k0n : ℕ, k0n ≤ 1 →
        ((2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 + k0n : ℕ) : Fp)
          = input_alpha + tQ →
        2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 + k0n
          = ZMod.val input_alpha + tQNat := by
      intro k0n hk0le hcong
      refine k_canonical (R := 2 ^ 4 * chainNat 0 bitsLo 126 + 2 * chainNat 0 bitsC 3 + k0n)
        hK254 hZ130 hZhiLt ?_ ?_ ?_ hcong hOvDisj2 hOvEx
      · intro hf
        have h := chainNat_msb bitsHi 124
        rw [hf] at h
        have h2 := chainNat_lt 0 (fun i => bitsHi (i + 1)) 124
        norm_num at h h2 ⊢
        omega
      · have h1 := hCloLt
        have h2 := hCcLt
        norm_num at h1 h2 ⊢
        omega
      · have h1 := chainNat_offset (chainNat 0 bitsHi 125) bitsLo 126
        have h2 := chainNat_offset (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3
        norm_num at h1 h2 ⊢
        omega
    -- the final scalar identity: [2^254 + k]•base = [α]•base
    have hOnC : ({ x := input_base_x, y := input_base_y } : Point Fp).OnCurve := assumptions
    have hfin : ∀ s : ℕ, s = 2 ^ 254 + ZMod.val input_alpha + tQNat →
        s • ({ x := input_base_x, y := input_base_y } : Point Fp)
          = ZMod.val input_alpha • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      intro s hs
      have hq : PALLAS_SCALAR_CARD = 2 ^ 254 + tQNat := by
        norm_num [PALLAS_SCALAR_CARD, tQNat]
      rw [hs, show 2 ^ 254 + ZMod.val input_alpha + tQNat
          = ZMod.val input_alpha + PALLAS_SCALAR_CARD from by rw [hq]; ring]
      exact point_card_reduce hOnC _
    -- ── assemble ──
    rcases Bool.dichotomy k0 with hk | hk <;> rw [hk] at hZ0 hResEq <;>
      simp only [Bool.false_eq_true, if_false, if_true] at hZ0 hResEq
    · -- k₀ = 0
      have hK := hKpart 0 (by omega) (by
        push_cast
        push_cast at hZ0
        rw [← hZ0]
        linear_combination hOvZ0)
      rw [← hResult, hResEq]
      exact hfin _ (by omega)
    · -- k₀ = 1
      have hK := hKpart 1 (by omega) (by
        push_cast
        push_cast at hZ0
        rw [← hZ0]
        linear_combination hOvZ0)
      rw [← hResult, hResEq]
      exact hfin _ (by omega)

  completeness := by
    circuit_proof_start2 [mainCircuit, MulOverflow.circuit, Spec, Assumptions,
      EnvAssumptions]
    simp only [main_envAssumptions_eq, main_assumptions_eq, main_proverAssumptions_eq,
      main_proverSpec_eq] at m_spec ⊢
    -- the honest running-sum cells, from the main bundle's `ProverSpec`
    obtain ⟨hz0v, hz130v, hk254v⟩ :=
      (m_spec trivial assumptions prover_assumptions).2
    refine ⟨⟨trivial, assumptions, prover_assumptions⟩, env_assumptions,
      ⟨by norm_num [MulOverflow.numWords, PALLAS_BASE_CARD],
       by norm_num [MulOverflow.numWords, PALLAS_BASE_CARD]⟩, ?_⟩
    rw [hz0v, hz130v, hk254v]
    exact Ecc.Mul.overflow_spec_honest input_alpha rfl rfl rfl

derive_contract_bridges mul := mul

end Zcash.Circuits.Ecc.Mul
