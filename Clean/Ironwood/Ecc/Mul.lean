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

namespace Halo2.Ironwood.Ecc.Mul

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc (tQ)
open Halo2.Ironwood.Ecc.Mul (tQNat kNat kBits chainNat chainNat_lt chainNat_offset chainNat_msb
  chain_cast accScalar_closed k_canonical cells_kNat z0_cell_value)
open Halo2.Ironwood.Ecc.Mul.Decompose (m_bounds)
open Halo2.Ironwood.Ecc.Mul.Incomplete.DoubleAndAdd (accScalar zRunValue)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)
open Halo2.Ironwood.Ecc.MulIncomplete (BitsHint kBitsWindow kBitsWindow_eq_kBits
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
def lsbGate (cfg : Config) : Gate Fp where
  name := "LSB check"
  selector := cfg.qMulLsb
  constraints :=
    let z1 : Expression Fp Query := queryAdvice cfg.completeConfig.zComplete 0   -- z_1
    let z0 : Expression Fp Query := queryAdvice cfg.completeConfig.zComplete 1   -- z_0
    let xP : Expression Fp Query := queryAdvice cfg.addConfig.xP 0               -- x_p
    let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP 0               -- y_p
    let baseX : Expression Fp Query := queryAdvice cfg.addConfig.xP 1            -- base_x
    let baseY : Expression Fp Query := queryAdvice cfg.addConfig.yP 1            -- base_y
    let lsb := z0 - z1 * (2 : Fp)
    -- `lsb · (1 − lsb)`, with the `1` on the left of the subtraction to match the compiled gate
    -- AST.
    let boolCheck := lsb * ((1 : Fp) - lsb)
    let lsbX := lsb * xP + ((1 : Fp) - lsb) * (xP - baseX)
    let lsbY := lsb * yP + ((1 : Fp) - lsb) * (yP + baseY)
    Constraints.withSelector cfg.qMulLsb
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

/-- The main-region body (everything before the layouter-level overflow check): the init add,
hi/lo/complete double-and-adds, the LSB step, and the final recombination, in one `assign_region`.
Returns the result point together with the three running-sum cells the overflow check copies into
its own region: `z0` (the LSB row full sum), `hi.zs[124]` (= z_130), `hi.zs[0]` (= k_254). -/
def mainRegion (cfg : Config) (input : Var Inputs Fp) :
    RegionCircuit Fp (Var Point Fp × AssignedCell Fp × AssignedCell Fp × AssignedCell Fp) := do
  -- 1. acc = [2]base  (init complete addition)
  let acc ← Add.add.call cfg.addConfig offInit
    ⟨input.base, input.base⟩
  -- 2. z_init = 0: the running-sum start, the constant 0 on the hi config's `z` column at the hi
  --    phase's start row. The hi half copies this same cell into its own `z` at `offHi`.
  let zInit ← assignAdvice cfg.hiConfig.z offHi
    (.ofFExpr (.const 0))
  constrainConstant zInit 0
  -- 3. hi half: 125 double-and-add bits k_254..k_130, bit window 0
  let hi ← (MulIncomplete.double_and_add 124 0).call cfg.hiConfig offHi
    ⟨(pure (.expr input.alpha) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)), input.base, acc, zInit⟩
  -- 4. lo half: 126 double-and-add bits k_129..k_4, bit window 125, running sum chained
  let lo ← (MulIncomplete.double_and_add 125 125).call cfg.loConfig
    offLo ⟨(pure (.expr input.alpha) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)), input.base, hi.acc, hi.zs[124]⟩
  -- 5. complete rounds: k_3..k_1, bit window 251
  let comp ← (MulComplete.assign_region 3 251).call cfg.completeConfig
    offComp ⟨(pure (.expr input.alpha) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)), input.base, lo.acc.x, lo.acc.y, lo.zs[125]⟩
  -- 6. the LSB step k_0 = kBits alpha 254, derived from the scalar cell
  let z1 := comp.zs[2]
  -- z_0 = 2·z_1 + k_0 on the z_complete column at the LSB base row (the bit condition is
  -- the LSB's reading program on the scalar cell, `MulComplete.kBitWindowExpr` at 254)
  let z0 ← assignAdvice cfg.completeConfig.zComplete (offLsb + 1)
    (.ofFExpr (.add (.mul (.const 2) (.expr z1))
      (.ite (MulComplete.kBitWindowExpr (.expr input.alpha) 254 0) (.const 1) (.const 0))))
  -- copy base_x, base_y into the LSB gate window (next row)
  let _bx ← copyAdvice input.base.x cfg.addConfig.xP (offLsb + 1)
  let _by ← copyAdvice input.base.y cfg.addConfig.yP (offLsb + 1)
  -- the correction point (base_x, ±base_y) or identity, witnessed on add.xP/add.yP (cur row)
  let corrX ← assignAdvice cfg.addConfig.xP offLsb
    (.ofFExpr (.ite (MulComplete.kBitWindowExpr (.expr input.alpha) 254 0)
      (.const 0) (.expr input.base.x)))
  let corrY ← assignAdvice cfg.addConfig.yP offLsb
    (.ofFExpr (.ite (MulComplete.kBitWindowExpr (.expr input.alpha) 254 0)
      (.const 0) (Witgen.FExprOver.neg (.expr input.base.y))))
  -- the q_mul_lsb gate at the LSB base row
  (lsbGate cfg).enable offLsb
  -- the final complete addition: result = corr + acc
  let result ← Add.add.call cfg.addConfig offLsb
    ⟨{ x := corrX, y := corrY }, comp.acc⟩
  return (result, z0, hi.zs[124], hi.zs[0])

/-- The scalar-decomposition and recombination assembly, at the layouter level: the whole
double-and-add convergence runs in one `assign_region`, and the overflow check runs after that
region closes as a separate layouter-level `overflow_check` of three sibling regions. The
`z_0`/`z_130`/`k_254` cells cross into the overflow regions as copies. Returns `[alpha] base`. -/
def synthesize (cfg : Config) (input : Var Inputs Fp) :
    Circuit Fp (Var Point Fp) := do
  -- the main double-and-add region
  let ⟨result, z0, z130, k254⟩ ← assignRegion "variable-base scalar mul" (mainRegion cfg input)
  -- the overflow check after the main region closes, at layouter level
  let _ov ← (MulOverflow.circuit 10 hKW10).call cfg.overflowConfig
    ⟨input.alpha, z0, z130, k254⟩
  return result

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

/-- The honest running-sum cells satisfy the overflow-check contract (`overflow_spec_honest` at
the `MulOverflow.Spec` record — same formula, defeq). -/
private theorem overflow_spec_honest' (alpha : Fp) {z0v z130v k254v : Fp}
    (hz0v : z0v = ((kNat alpha : ℕ) : Fp))
    (h130 : z130v = ((kNat alpha / 2 ^ 130 : ℕ) : Fp))
    (h254 : k254v = ((kNat alpha / 2 ^ 254 : ℕ) : Fp)) :
    MulOverflow.Spec { alpha := alpha, z0 := z0v, z130 := z130v, k254 := k254v } :=
  Halo2.Ironwood.Ecc.Mul.overflow_spec_honest alpha hz0v h130 h254

/-! ## Point-level scalar-multiple algebra

The `SWPoint`-level step/negation/identity algebra, transported to `Point Fp` `nsmul` through the
`toSW` bridge (`Halo2.Ironwood.Point.ext_toSW_iff`/`toSW_add`/`toSW_nsmul`/`toSW_neg`/`toSW_zero`). -/

section PointAlgebra
open CompElliptic.CurveForms.ShortWeierstrass (SWPoint)
open CompElliptic.Curves.Pasta
open Halo2.Ironwood.Point (ext_toSW_iff toSW_add toSW_neg toSW_zero toSW_nsmul
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
    simpa using Halo2.Ironwood.Ecc.Mul.nsmul_step (P.toSW hPv) a ha false
  · -- bit = true: the step point is P
    simp only [if_true]
    apply (ext_toSW_iff
      (valid_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)))
      (valid_nsmul hPv _)).mpr
    rw [toSW_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)),
      toSW_add hPv (valid_nsmul hPv a),
      toSW_nsmul hPv a, toSW_nsmul hPv]
    simpa using Halo2.Ironwood.Ecc.Mul.nsmul_step (P.toSW hPv) a ha true

/-- `-P + m•P = (m−1)•P` at the `Point` level. -/
private theorem point_neg_add_nsmul {P : Point Fp} (hP : P.OnCurve) {m : ℕ} (hm : 1 ≤ m) :
    -P + m • P = (m - 1) • P := by
  have hPv : P.Valid := Or.inl hP
  apply (ext_toSW_iff (valid_add (valid_neg hPv) (valid_nsmul hPv m))
    (valid_nsmul hPv _)).mpr
  rw [toSW_add (valid_neg hPv) (valid_nsmul hPv m), toSW_neg hPv, toSW_nsmul hPv m,
    toSW_nsmul hPv]
  exact Halo2.Ironwood.Ecc.Mul.neg_add_nsmul (P.toSW hPv) hm

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

/-! ## Output-record and cell-eval bridges

The children's `.call … .output self` records reduce lazily, by `rfl`, to record literals of
`AssignedCell.of` cells; eval decomposes componentwise on those literals. -/

/-- The `MulIncomplete` bundle's output record, reduced (`cellAt`/`cellVec` cells at their
fixed region-local rows). -/
private theorem incomplete_call_output (n : ℕ) (w : ℕ)
    (cfg : MulIncomplete.Config) (off : ℕ) (inp : Var MulIncomplete.Inputs Fp)
    (self : RegionIndex) :
    ((MulIncomplete.double_and_add n w).call cfg off inp).output self
      = { acc := { x := .of self (off + n + 2) cfg.xA,
                   y := .of self (off + n + 2) cfg.lambda1 },
          zs := Vector.ofFn (fun i => .of self (off + 1 + i.val) cfg.z) } := by
  rw [FormalRegionCircuit.output_call]; rfl

/-- The `MulComplete` bundle's output `zs` cells at their fixed rows (the `acc` field is
never reduced, per the whnf discipline). -/
private theorem complete_call_output_zs (w : ℕ) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    (((MulComplete.assign_region 3 w).call cfg off inp).output self).zs
      = Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) := by
  rw [FormalRegionCircuit.output_call]; rfl

/-- The `Add` bundle's output point cells (`x_qr`/`y_qr` at `offset + 1`). -/
private theorem add_call_output (cfg : Add.Config) (off : ℕ) (inp : Var Add.Inputs Fp)
    (self : RegionIndex) :
    (Add.add.call cfg off inp).output self
      = { x := .of self (off + 1) cfg.xQR, y := .of self (off + 1) cfg.yQR } := by
  rw [FormalRegionCircuit.output_call]; rfl

/-- Literal-eval bridge for `MulIncomplete.Output` (verifier view). -/
private theorem incompleteOutput_eval_literal {n : ℕ} (place : RegionIndex → ℕ)
    (env : Environment Fp) (xA yA : AssignedCell Fp)
    (zs : Vector (AssignedCell Fp) (n + 1)) :
    ProvableStruct.eval place env
        ({ acc := { x := xA, y := yA }, zs := zs }
          : MulIncomplete.Output (n + 1) (AssignedCell Fp))
      = { acc := { x := AssignedCell.eval place env xA, y := AssignedCell.eval place env yA },
          zs := ProvableType.eval (M := fields (n + 1)) place env zs } := by
  with_unfolding_all rfl

/-- Literal-eval bridge for `MulComplete.Output 3` (verifier view; the `acc` field may be a
symbolic term). -/
private theorem completeOutput_eval_literal (place : RegionIndex → ℕ)
    (env : Environment Fp) (acc : Point (AssignedCell Fp))
    (zs : Vector (AssignedCell Fp) 3) :
    ProvableStruct.eval place env
        ({ acc := acc, zs := zs } : MulComplete.Output 3 (AssignedCell Fp))
      = { acc := ProvableType.eval place env acc,
          zs := ProvableType.eval (M := fields 3) place env zs } := by
  with_unfolding_all rfl

/-- Elementwise read of an evaluated cell vector. -/
private theorem fieldsEval_getElem {w : ℕ} (place : RegionIndex → ℕ) (env : Environment Fp)
    (zs : Vector (AssignedCell Fp) w) (i : ℕ) (hi : i < w) :
    (ProvableType.eval (M := fields w) place env zs)[i]
      = AssignedCell.eval place env (zs[i]) := by
  simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements,
    Vector.getElem_map]

/-- `Cell.eval` of an `AssignedCell.of` cell's `.cell` (the `constrainConstant` constraint
form): the advice read at its region-local row. -/
private theorem cell_eval_of (place : RegionIndex → ℕ) (env : Environment Fp)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    Cell.eval place env ((AssignedCell.of self row col : AssignedCell Fp)).cell
      = env.advice col ((place self + row : ℕ) : ℤ) := by
  simp only [Cell.eval, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice]

/-- `Cell.eval` of a bare `Cell.of` (the `constrainEqual` constraint form). -/
private theorem cellOf_eval (place : RegionIndex → ℕ) (env : Environment Fp)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    Cell.eval place env (Cell.of self row col)
      = env.advice col ((place self + row : ℕ) : ℤ) := by
  simp only [Cell.eval, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
    Environment.get_advice]

/-- `AssignedCell.eval` of an `AssignedCell.of` cell: the advice read at its region-local
row. -/
private theorem assignedCell_eval_of (place : RegionIndex → ℕ) (env : Environment Fp)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    AssignedCell.eval place env (AssignedCell.of self row col)
      = env.advice col ((place self + row : ℕ) : ℤ) := by
  simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]

/-- Plain-`.output` spelling of `incomplete_call_output` (the composition iff's form). -/
private theorem incomplete_output_eq (n : ℕ) (w : ℕ)
    (cfg : MulIncomplete.Config) (off : ℕ) (inp : Var MulIncomplete.Inputs Fp)
    (self : RegionIndex) :
    (MulIncomplete.double_and_add n w).output cfg off inp self
      = { acc := { x := .of self (off + n + 2) cfg.xA,
                   y := .of self (off + n + 2) cfg.lambda1 },
          zs := Vector.ofFn (fun i => .of self (off + 1 + i.val) cfg.z) } := rfl

/-- The `MulComplete` bundle's output record, full form: the `acc` field is the (symbolic,
never-reduced) loop output, the `zs` are the fixed-row cells. -/
private theorem complete_output_eq (w : ℕ) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    (MulComplete.assign_region 3 w).output cfg off inp self
      = { acc := (MulComplete.loop cfg inp (MulComplete.kBitWindowProg inp.alpha w) off 3).output self,
          zs := Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) } := rfl

/-- `.call` spelling of `complete_output_eq`. -/
private theorem complete_call_output_eq (w : ℕ) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    ((MulComplete.assign_region 3 w).call cfg off inp).output self
      = { acc := (MulComplete.loop cfg inp (MulComplete.kBitWindowProg inp.alpha w) off 3).output self,
          zs := Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) } := by
  rw [FormalRegionCircuit.output_call]; rfl

/-- Plain-`.output` spelling of `complete_call_output_zs`. -/
private theorem complete_output_zs_eq (w : ℕ) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    ((MulComplete.assign_region 3 w).output cfg off inp self).zs
      = Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) := rfl

/-- Plain-`.output` spelling of `add_call_output`. -/
private theorem add_output_eq (cfg : Add.Config) (off : ℕ) (inp : Var Add.Inputs Fp)
    (self : RegionIndex) :
    Add.add.output cfg off inp self
      = { x := .of self (off + 1) cfg.xQR, y := .of self (off + 1) cfg.yQR } := rfl

/-! ## `mainRegion` output projections

The main region returns `(result, z0, z_130, k_254)`; the layouter-level MulOverflow call's
input record carries the last three as `.output` projections. These bridges land them on their
named cells. -/

/-- The main region's `z0` output cell: the LSB-row full-sum assign
(`zComplete @ offLsb + 1`). -/
private theorem mainRegion_output_z0 (cfg : Config) (input : Var Inputs Fp)
    (i : RegionIndex) :
    ((mainRegion cfg input).output i).2.1
      = AssignedCell.of i (offLsb + 1) cfg.completeConfig.zComplete := rfl

/-- The main region's `z_130` output cell: the hi half's `zs[124]` (`z @ offHi + 1 + 124`).
Reduced lazily via `circuit_norm`, landing on the `hi` child's `.output`, then
`incomplete_call_output` and the `zs[124]` index — this never forces the whole nested-bind term
at once. -/
private theorem mainRegion_output_z130 (cfg : Config) (input : Var Inputs Fp)
    (i : RegionIndex) :
    ((mainRegion cfg input).output i).2.2.1
      = AssignedCell.of i (offHi + 1 + 124) cfg.hiConfig.z := by
  simp only [mainRegion, circuit_norm]
  rw [incomplete_call_output]
  simp only [Vector.getElem_ofFn]

/-- The main region's `k_254` output cell: the hi half's `zs[0]` (the top bit,
`z @ offHi + 1 + 0`). Same lazy bind-by-bind route as `mainRegion_output_z130`. -/
private theorem mainRegion_output_k254 (cfg : Config) (input : Var Inputs Fp)
    (i : RegionIndex) :
    ((mainRegion cfg input).output i).2.2.2
      = AssignedCell.of i (offHi + 1 + 0) cfg.hiConfig.z := by
  simp only [mainRegion, circuit_norm]
  rw [incomplete_call_output]
  simp only [Vector.getElem_ofFn]

/-- Eval of an `AssignedCell.of` cell (`Eval` level): the advice read at its row. -/
private theorem eval_of (env : Placed Environment Fp) (self : RegionIndex) (row : ℕ)
    (col : Column .advice) :
    eval env (AssignedCell.of self row col : AssignedCell Fp)
      = env.env.advice col ((env.place self + row : ℕ) : ℤ) := by
  rw [ProvableType.eval_field, assignedCell_eval_of]

/-- `zs`-component read of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_zs_getElem {n : ℕ} (env : Placed Environment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) (i : ℕ)
    (hi : i < n + 1) :
    (eval env ({ acc := { x := xA, y := yA }, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [incompleteOutput_eval_literal]
  show (ProvableType.eval (M := fields (n + 1)) env.place env.env zs)[i] = _
  rw [fieldsEval_getElem env.place env.env zs i hi, ProvableType.eval_field]

/-- `acc`-components of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_acc {n : ℕ} (env : Placed Environment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) :
    (eval env ({ acc := { x := xA, y := yA }, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).acc
      = { x := eval env xA, y := eval env yA } := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [incompleteOutput_eval_literal]
  show Point.mk _ _ = _
  rw [ProvableType.eval_field, ProvableType.eval_field]

/-- `acc`-component of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_acc (env : Placed Environment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).acc
      = eval env acc := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [completeOutput_eval_literal, ProvableType.eval_cells]

/-- `zs`-component read of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_zs_getElem (env : Placed Environment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) (i : ℕ)
    (hi : i < 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [completeOutput_eval_literal]
  show (ProvableType.eval (M := fields 3) env.place env.env zs)[i] = _
  rw [fieldsEval_getElem env.place env.env zs i hi, ProvableType.eval_field]

/-- Componentwise eval of a `MulComplete.Inputs` record (the scalar slot is a prover hint,
its verifier value is trivial). Stated over a whole var — a mixed-record literal admits no
`Eval`-synthesizable ascription — so use sites `rw` it and the literal's projections reduce
definitionally. -/
private theorem compInputs_eval_eq (env : Placed Environment Fp)
    (v : Var MulComplete.Inputs Fp) :
    eval env v
      = { alpha := (), base := eval env (v.base : Point (AssignedCell Fp)),
          xA := eval env (v.xA : AssignedCell Fp), yA := eval env (v.yA : AssignedCell Fp),
          z := eval env (v.z : AssignedCell Fp) } := by
  with_unfolding_all rfl

/-- Componentwise eval of a `MulOverflow.Inputs` record literal. -/
private theorem ovInputs_eval_eq (env : Placed Environment Fp)
    (alpha z0 z130 k254 : AssignedCell Fp) :
    eval env (⟨alpha, z0, z130, k254⟩ : Var MulOverflow.Inputs Fp)
      = { alpha := eval env alpha, z0 := eval env z0, z130 := eval env z130,
          k254 := eval env k254 } := by
  simp only [circuit_norm]

/-! ## Prover-side bridge duplicates (completeness)

The same record/cell eval bridges over `Placed ProverEnvironment` (the honest-witness side).
The children's verifier-`Spec` facts arrive at `env.toEnvironment` and reuse the verifier
bridges; only the `ProverSpec`/witness facts need these. Both sides meet at the same
`env.env.toEnvironment.advice` reads. -/

/-- Prover-side `eval_of`. -/
private theorem eval_of_prover (env : Placed ProverEnvironment Fp) (self : RegionIndex)
    (row : ℕ) (col : Column .advice) :
    eval env (AssignedCell.of self row col : AssignedCell Fp)
      = env.env.toEnvironment.advice col ((env.place self + row : ℕ) : ℤ) := by
  rw [ProvableType.eval_field_prover, assignedCell_eval_of]

/-- Prover-side componentwise eval of `MulIncomplete.Inputs` (the scalar slot holds the
reading program; its prover value is the program's evaluation). Stated over a whole var —
a mixed-record literal admits no `Eval`-synthesizable ascription — so use sites `rw` it
and the literal's projections reduce definitionally. -/
private theorem hiInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (v : Var MulIncomplete.Inputs Fp) :
    eval env v
      = { alpha := Witgen.MOver.eval (F := Fp) (V := AssignedCell Fp) (value := field) env v.alpha,
          base := eval env (v.base : Point (AssignedCell Fp)),
          acc := eval env (v.acc : Point (AssignedCell Fp)),
          z := eval env (v.z : AssignedCell Fp) } := by
  with_unfolding_all rfl

/-- The cell-reading scalar program's prover value is the cell's value. -/
private theorem fexpr_expr_eval_prover (env : Placed ProverEnvironment Fp)
    (c : AssignedCell Fp) :
    Witgen.MOver.eval (F := Fp) (V := AssignedCell Fp) (value := field) env
      (pure (.expr c) : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) = eval env c := by
  with_unfolding_all rfl

/-- The LSB bit program's prover value: `kBitsWindow` of the scalar cell's value. -/
private theorem kBitWindowExpr_expr_eval (env : Placed ProverEnvironment Fp)
    (c : AssignedCell Fp) (w i : ℕ) :
    Witgen.BExprOver.eval { env := env } (MulComplete.kBitWindowExpr (.expr c) w i)
      = kBitsWindow (readCell env c) w i := by
  have h := congrFun (MulComplete.bexprsVal_kBitWindowExpr (.expr c) w { env := env }) i
  simp only [MulComplete.bexprsVal] at h
  rw [h]
  with_unfolding_all rfl

/-- Prover-side componentwise eval of `MulComplete.Inputs` (the scalar slot holds the
reading program; its prover value is the program's evaluation). Whole-var, like
`hiInputs_eval_eq_prover`. -/
private theorem compInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (v : Var MulComplete.Inputs Fp) :
    eval env v
      = { alpha := Witgen.MOver.eval (F := Fp) (V := AssignedCell Fp) (value := field) env v.alpha,
          base := eval env (v.base : Point (AssignedCell Fp)),
          xA := eval env (v.xA : AssignedCell Fp), yA := eval env (v.yA : AssignedCell Fp),
          z := eval env (v.z : AssignedCell Fp) } := by
  with_unfolding_all rfl

/-- Prover-side `alpha`-projection of an evaluated `MulIncomplete.Inputs` record — the
scalar program's evaluation, the landing for the children's derived-bit facts
(`kBitsWindow (…).alpha w` → `kBitsWindow (alpha value) w`, via `fexpr_expr_eval_prover`
once the projection reduces on a `.expr`-wrapped cell). -/
private theorem hiInputs_alpha_prover (env : Placed ProverEnvironment Fp)
    (v : Var MulIncomplete.Inputs Fp) :
    (eval env v).alpha = Witgen.MOver.eval (F := Fp) (V := AssignedCell Fp) (value := field) env v.alpha := by
  rw [hiInputs_eval_eq_prover]

/-- Prover-side `alpha`-projection of an evaluated `MulComplete.Inputs` record — the
scalar program's evaluation. -/
private theorem compInputs_alpha_prover (env : Placed ProverEnvironment Fp)
    (v : Var MulComplete.Inputs Fp) :
    (eval env v).alpha = Witgen.MOver.eval (F := Fp) (V := AssignedCell Fp) (value := field) env v.alpha := by
  rw [compInputs_eval_eq_prover]

/-- Prover-side componentwise eval of `MulOverflow.Inputs`. -/
private theorem ovInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (alpha z0 z130 k254 : AssignedCell Fp) :
    eval env (⟨alpha, z0, z130, k254⟩ : Var MulOverflow.Inputs Fp)
      = { alpha := eval env alpha, z0 := eval env z0, z130 := eval env z130,
          k254 := eval env k254 } := by
  simp only [circuit_norm]

/-- Prover-side componentwise eval of `Add.Inputs`. -/
private theorem addInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : Add.Inputs (AssignedCell Fp)) = { p := eval env p, q := eval env q } := by
  simp only [circuit_norm, ProvableType.eval_cells_prover, ProvableType.eval_cells]

/-- Prover-side `zs`-component read of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_zs_getElem_prover {n : ℕ} (env : Placed ProverEnvironment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) (i : ℕ)
    (hi : i < n + 1) :
    (eval env ({ acc := { x := xA, y := yA }, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval_prover]
  rw [incompleteOutput_eval_literal]
  show (ProvableType.eval (M := fields (n + 1)) env.place env.env.toEnvironment zs)[i] = _
  rw [fieldsEval_getElem env.place env.env.toEnvironment zs i hi,
    ProvableType.eval_field_prover]

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

/-- Prover-side `acc`-components of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_acc_prover {n : ℕ} (env : Placed ProverEnvironment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) :
    (eval env ({ acc := { x := xA, y := yA }, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).acc
      = { x := eval env xA, y := eval env yA } := by
  rw [ProvableStruct.eval_var_eq_eval_prover, incompleteOutput_eval_literal]
  show Point.mk _ _ = _
  rw [ProvableType.eval_field_prover, ProvableType.eval_field_prover]

/-- Prover-side `acc`-component of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_acc_prover (env : Placed ProverEnvironment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).acc
      = eval env acc := by
  rw [ProvableStruct.eval_var_eq_eval_prover, completeOutput_eval_literal,
    ProvableType.eval_cells_prover]

/-- Prover-side `zs`-component read of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_zs_getElem_prover (env : Placed ProverEnvironment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) (i : ℕ)
    (hi : i < 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval_prover, completeOutput_eval_literal]
  show (ProvableType.eval (M := fields 3) env.place env.env.toEnvironment zs)[i] = _
  rw [fieldsEval_getElem env.place env.env.toEnvironment zs i hi,
    ProvableType.eval_field_prover]

/-! ## Composition ergonomics

Input-record eval decompositions (`hiInputs_eval_eq` &c.) fire under `rw` but not under
`simp only` on engine-produced eval terms — the instance spelling differs from a
locally-elaborated one, so every decomposition site below is a `rw`. -/

/-- Eval of an `Add.Inputs` pair built from two points (componentwise). -/
theorem addInputs_eval_eq (env : Placed Environment Fp) (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : Add.Inputs (AssignedCell Fp)) = { p := eval env p, q := eval env q } := by
  simp only [circuit_norm, ProvableType.eval_cells]

/-- Eval of a `MulIncomplete.Inputs` record (componentwise; the scalar slot is a prover
hint, its verifier value is trivial). Stated over a whole var — a mixed-record literal
admits no `Eval`-synthesizable ascription — so use sites `rw` it and the literal's
projections reduce definitionally. -/
theorem hiInputs_eval_eq (env : Placed Environment Fp) (v : Var MulIncomplete.Inputs Fp) :
    eval env v
      = { alpha := (), base := eval env (v.base : Point (AssignedCell Fp)),
          acc := eval env (v.acc : Point (AssignedCell Fp)),
          z := eval env (v.z : AssignedCell Fp) } := by
  with_unfolding_all rfl

/-- Verifier: an abstract point-output var's coordinate-evals reassemble to its whole-point eval
(`Point.ofCoords (eval env o.x, eval env o.y) ≡ eval env o`), so an entering accumulator threaded
through the opaque local `o` lands on the whole-point value equation. `rfl` by `ProvableType`-eval
unfolding (`Point` is a two-field `Var`). -/
theorem point_var_eval_eq (env : Placed Environment Fp) (o : Var Point Fp) :
    eval env o = ({ x := eval env o.x, y := eval env o.y } : Point Fp) := by
  with_unfolding_all rfl

/-- Prover view of `point_var_eval_eq`. -/
theorem point_var_eval_eq_prover (env : Placed ProverEnvironment Fp) (o : Var Point Fp) :
    eval env o = ({ x := eval env o.x, y := eval env o.y } : Point Fp) := by
  with_unfolding_all rfl

/-! ## The gadget bundle

The working-scalar bits are derived from the `alpha` cell (`kBitsWindow`, windows 0/125/251 for
hi/lo/complete and the LSB read); the verifier `Spec` recovers a matching sequence via the
children's existential specs plus the canonicity argument. -/

/-- The region count of `synthesize`: the main double-and-add region (1) plus the overflow
check's three sibling regions (`MulOverflow.circuit`'s regionCount, 3) = 4. -/
private theorem synthesize_regionCount (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.regionCount ((synthesize cfg input).operations i) = 4 := by
  simp only [synthesize, circuit_norm, operations_assignRegion,
    Operations.regionCount]

-- The main region's composed do-block is one nested-bind term ~5 children deep; naive `.output`
-- reduction can explode the unifier at the complete-phase/final-add value-bookkeeping sites. Both
-- bundle proofs run `abstract_outputs` (after `provable_type_simp`, before `subcircuit_rw`): every
-- child output becomes an opaque `x_gen_out_j` local, so each chained chunk input (the complete
-- chunk's hi→lo input, the final add's complete-output input) is shallow by construction.
-- Downstream `rw`/`simp` sees the shallow local; the concrete child output is recovered via the
-- `h_gen_out_j` equations only where a single child `.output` must be reduced. The raw main-region
-- output feeding the overflow chunk is abstracted too (`x_gen_out_4` in completeness).
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

  elaborated cfg :=
    { output := fun input i => (synthesize cfg input).output i
      regionCount := fun _ => 4
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synthesize_regionCount cfg input i).symm }

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
    -- `circuit_proof_start` intros + destructures `output`; since this layouter's own output is
    -- the opaque composed `synthesize.output`, not a cell literal, it leaves `h_output` as the
    -- whole-point equation the manual peel below consumes. `synthesize`/`mainRegion` are
    -- deliberately not unfolded here — that would inflate the state into the deep composed term;
    -- `synthesize` is unfolded manually at `hc` only, below.
    circuit_proof_start
    -- Reassemble the split `place`/`env` into a `Placed` value (named `env` again), since
    -- `subcircuit_rw`'s `*_placed` lemmas key on a single common `penv : Placed …`.
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env := ⟨⟨place, env⟩, rfl, rfl⟩
    -- ── peel the faithful layouter structure: the MAIN REGION (index i₀) and the layouter-level
    -- MulOverflow chunk (its three sibling regions at i₀+1..i₀+3) ──
    try simp only [synthesize, circuit_norm] at hc
    obtain ⟨hMain, hOv⟩ := hc
    -- ── peel the main region (bind/append/per-op only — never whole-goal circuit_norm) ──
    simp only [mainRegion,
      RegionCircuit.operations_bind,
      operations_assignAdvice, operations_copyAdvice, operations_enable,
      operations_constrainConstant, RegionOperations.constraints_append] at hMain
    obtain ⟨hInit, _hZinitW, hZconst, hHi, hLo, hComp, _hZ0W, hBxC, hByC, _hCxW, _hCyW,
      hGate, hFin, -⟩ := hMain
    -- ▸▸ make every child output opaque: the chained chunk inputs (comp's hi→lo entering, the
    --    final add's comp-acc entering) become shallow locals `x_gen_out_j`, and each weakened
    --    chunk's Spec speaks the local. ◂◂
    abstract_outputs
    obtain ⟨hIalpha, hBxIn, hByIn⟩ := h_input
    -- ── the base point: cells and value ──
    have hbX : eval env input_var_base_x = input_base_x := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hBxIn
    have hbY : eval env input_var_base_y = input_base_y := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hByIn
    have halpha : eval env input_var_alpha = input_alpha := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hIalpha
    have hbaseEval : eval env ({ x := input_var_base_x, y := input_var_base_y }
        : Point (AssignedCell Fp)) = { x := input_base_x, y := input_base_y } := by
      rw [Point.eval_eq, hbX, hbY]
    have hOnC : ({ x := input_base_x, y := input_base_y } : Point Fp).OnCurve := hA
    have hbaseV : ({ x := input_base_x, y := input_base_y } : Point Fp).Valid := Or.inl hOnC
    -- ▸▸ engine site 1: init add ⇒ acc = base + base = [2]base ◂◂
    subcircuit_rw at hInit
    simp only [add_spec_eq, add_assumptions_eq, add_envAssumptions_eq] at hInit
    have hInitIn : eval env (⟨{ x := input_var_base_x, y := input_var_base_y },
          { x := input_var_base_x, y := input_var_base_y }⟩ : Var Add.Inputs Fp)
        = (⟨{ x := input_base_x, y := input_base_y },
            { x := input_base_x, y := input_base_y }⟩ : Add.Inputs Fp) := by
      rw [addInputs_eval_eq, hbaseEval]
    obtain ⟨hAccV, hAccEq⟩ := hInit trivial (by rw [hInitIn]; exact ⟨hbaseV, hbaseV⟩)
    rw [hInitIn] at hAccEq
    -- init output on the local: `hAccEq : eval env x_gen_out_0 = base + base` (engine emitted the
    -- weakened `hInit` Spec over `x_gen_out_0`). Keep both a whole-point form (`hAcc2Pt`, for
    -- entering-accumulator collapse) and the raw-cell form (`hAcc2`).
    have hAcc2Pt : eval env x_gen_out_0
        = 2 • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      rw [← point_two_nsmul hOnC]; exact hAccEq
    have hAcc2 : eval env (Add.add.output cfg.addConfig offInit
          ⟨{ x := input_var_base_x, y := input_var_base_y },
            { x := input_var_base_x, y := input_var_base_y }⟩ i₀)
        = 2 • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      rw [← h_gen_out_0] at hAcc2Pt; exact hAcc2Pt
    rw [add_output_eq, Point.eval_eq, eval_of, eval_of] at hAcc2
    -- ── z_init = 0 (the `constrainConstant` constraint) ──
    simp only [RegionOperations.constraints_cons, RegionOperations.constraints_nil,
      RegionOperation.constraints_constrainConstant, output_assignAdvice, and_true] at hZconst
    rw [cell_eval_of] at hZconst
    -- ▸▸ engine site 2: hi half ⇒ ∃ bitsHi, RoundInvariant 124 ◂◂
    subcircuit_rw at hHi
    simp only [hi_spec_eq, hi_assumptions_eq, hi_envAssumptions_eq] at hHi
    obtain ⟨bitsHi, hHiRI⟩ := hHi trivial (by
      rw [hiInputs_eval_eq]
      show (eval env ({ x := input_var_base_x, y := input_var_base_y }
        : Point (AssignedCell Fp))).OnCurve
      rw [hbaseEval]; exact hOnC)
    simp only [MulIncomplete.RoundInvariant] at hHiRI
    obtain ⟨hHiChain, hHiAccCl⟩ := hHiRI
    obtain ⟨hHiZ0, hHiZstep⟩ := zChain_split hHiChain
    -- the hi running-sum chain, as chainNat casts
    have hHiCells := chain_cast (n := 124) _ _ 0 bitsHi
      (by
        rw [hiInputs_eval_eq]
        simp only [output_assignAdvice, Nat.cast_zero]
        rw [eval_of]
        exact hZconst)
      hHiZ0 hHiZstep
    -- the hi accumulator: [accScalar 2 bitsHi 125] • base
    have hHiOut := hHiAccCl 2
      (by
        rw [hiInputs_eval_eq]
        show eval env x_gen_out_0
          = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))
        rw [hbaseEval]
        exact hAcc2Pt)
      (le_refl 2) (by norm_num)
    rw [← h_gen_out_1, incomplete_output_eq, incompleteOutput_acc,
      hiInputs_eval_eq] at hHiOut
    simp only [eval_of] at hHiOut
    rw [hbaseEval] at hHiOut
    -- ▸▸ engine site 3: lo half ⇒ ∃ bitsLo, RoundInvariant 125 ◂◂
    subcircuit_rw at hLo
    simp only [lo_spec_eq, lo_assumptions_eq, lo_envAssumptions_eq] at hLo
    obtain ⟨bitsLo, hLoRI⟩ := hLo trivial (by
      rw [hiInputs_eval_eq]
      show (eval env ({ x := input_var_base_x, y := input_var_base_y }
        : Point (AssignedCell Fp))).OnCurve
      rw [hbaseEval]; exact hOnC)
    simp only [MulIncomplete.RoundInvariant] at hLoRI
    obtain ⟨hLoChain, hLoAccCl⟩ := hLoRI
    obtain ⟨hLoZ0, hLoZstep⟩ := zChain_split hLoChain
    -- the hi z-cell 124 (= z₁₃₀), as a chainNat cast on its advice read (hi output local; recover)
    have hHiZ124 := hHiCells 124 (by omega)
    rw [← h_gen_out_1, incomplete_output_eq,
      incompleteOutput_zs_getElem env _ _ _ 124 (by omega)] at hHiZ124
    simp only [Vector.getElem_ofFn, eval_of] at hHiZ124
    -- the lo chain continues the hi chain (hi z-cell 124 entering, via `← h_gen_out_1`)
    have hLoCells := chain_cast (n := 125) _ _ (chainNat 0 bitsHi 125) bitsLo
      (by
        rw [hiInputs_eval_eq]
        rw [← h_gen_out_1, incomplete_output_eq]
        simp only [Vector.getElem_ofFn, Halo2.ProvableType.eval_field', assignedCell_eval_of]
        exact hHiZ124)
      hLoZ0 hLoZstep
    -- the lo accumulator, entering at m = accScalar 2 bitsHi 125 (hi output, via `← h_gen_out_1`)
    have hmB := m_bounds bitsHi bitsLo
    have hLoOut := hLoAccCl (accScalar 2 bitsHi 125)
      (by
        rw [hiInputs_eval_eq]
        show eval env x_gen_out_1.acc
          = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))
        rw [← h_gen_out_1, incomplete_output_eq]
        show eval env (Point.mk _ _) = _
        rw [Point.eval_eq, eval_of, eval_of, hbaseEval]
        exact hHiOut)
      hmB.1 hmB.2.1
    rw [← h_gen_out_2, incomplete_output_eq, incompleteOutput_acc,
      hiInputs_eval_eq] at hLoOut
    simp only [eval_of] at hLoOut
    rw [hbaseEval] at hLoOut
    -- ▸▸ engine site 4: complete rounds ⇒ ∃ bitsC, RoundInvariant 3 ◂◂
    subcircuit_rw at hComp
    simp only [comp_spec_eq, comp_assumptions_eq, comp_envAssumptions_eq] at hComp
    have hM2pos : 1 ≤ accScalar (accScalar 2 bitsHi 125) bitsLo 126 := hmB.2.2.1
    -- the lo output accumulator is a valid point ([M₂] • base)
    have hLoOutV : Point.Valid (Point.ofCoords
        (env.env.advice cfg.loConfig.xA
          ((env.place i₀ + (offLo + 125 + 2) : ℕ) : ℤ),
         env.env.advice cfg.loConfig.lambda1
          ((env.place i₀ + (offLo + 125 + 2) : ℕ) : ℤ))) := by
      show (Point.mk _ _).Valid
      rw [hLoOut]
      exact Halo2.Ironwood.Point.valid_nsmul hbaseV _
    -- The complete chunk's chained hi→lo input projections use the shallow lo-output local
    -- `x_gen_out_2`, and its output uses `x_gen_out_3`.
    -- Comp entering: recover the concrete lo output (`← h_gen_out_2`) to reduce its coords to cells;
    -- comp output: recover the concrete complete output (`← h_gen_out_3`) for `complete_output_eq`.
    obtain ⟨bitsC, hCompRI⟩ := hComp trivial (by
      rw [compInputs_eval_eq, ← h_gen_out_2, incomplete_output_eq]
      simp only [Halo2.ProvableType.eval_field', assignedCell_eval_of]
      rw [hbaseEval]
      exact ⟨hLoOutV, hbaseV⟩)
    simp only [MulComplete.RoundInvariant] at hCompRI
    obtain ⟨hCompChain, hCompAccCl⟩ := hCompRI
    -- the complete-phase accumulator: valid and = [accScalar M₂ bitsC 3] • base
    obtain ⟨hCompAccV, hCompAccEq⟩ := hCompAccCl
      (by
        rw [compInputs_eval_eq, ← h_gen_out_2, incomplete_output_eq]
        simp only [Halo2.ProvableType.eval_field', assignedCell_eval_of]
        exact hLoOutV)
      (by
        rw [compInputs_eval_eq]
        show Point.Valid (eval env ({ x := input_var_base_x, y := input_var_base_y }
          : Point (AssignedCell Fp)))
        rw [hbaseEval]; exact hbaseV)
    -- the complete input's `base` and entering-`acc` components (concrete, via `← h_gen_out_2`)
    have hLoOutRec : (Point.mk
          (env.env.advice cfg.loConfig.xA
            ((env.place i₀ + (offLo + 1 + 125 + 1) : ℕ) : ℤ))
          (env.env.advice cfg.loConfig.lambda1
            ((env.place i₀ + (offLo + 1 + (125 + 1)) : ℕ) : ℤ)) : Point Fp)
        = accScalar (accScalar 2 bitsHi 125) bitsLo 126
          • ({ x := input_base_x, y := input_base_y } : Point Fp) := hLoOut
    -- `hCompAccEq : output.acc = accPoint input.base ⟨input.xA,input.yA⟩ bitsC 3`, over the comp
    -- output/input. Recover the concrete comp output (`← h_gen_out_3`) for `complete_output_eq`;
    -- reduce the comp input eval (`compInputs_eval_eq`) — its base is `input.base` (→ `hbaseEval`),
    -- its entering acc is the lo output `x_gen_out_2` (→ `hLoOutRec` via `← h_gen_out_2`).
    rw [← h_gen_out_3, complete_output_eq, completeOutput_acc] at hCompAccEq hCompAccV
    rw [compInputs_eval_eq, ← h_gen_out_2, incomplete_output_eq] at hCompAccEq
    simp only [Halo2.ProvableType.eval_field', assignedCell_eval_of] at hCompAccEq
    rw [hbaseEval, hLoOutRec, accPoint_nsmul hOnC _ hM2pos bitsC 3] at hCompAccEq
    -- align with the final add's normal form (component-decomposed, z-field reduced)
    simp only [Point.eval_eq] at hCompAccEq
    -- ── the complete-phase z-chain, continued from the lo chain (lo output, via `← h_gen_out_2`) ──
    have hLoZ125 := hLoCells 125 (by omega)
    rw [← h_gen_out_2, incomplete_output_eq,
      incompleteOutput_zs_getElem env _ _ _ 125 (by omega)] at hLoZ125
    simp only [Vector.getElem_ofFn, eval_of] at hLoZ125
    have hCompZ0 := hCompChain ⟨0, by omega⟩
    simp only [if_pos] at hCompZ0
    have hCompCells := chain_cast (n := 2) _ _
      (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC
      (by
        rw [compInputs_eval_eq, ← h_gen_out_2, incomplete_output_eq]
        simp only [Vector.getElem_ofFn, Halo2.ProvableType.eval_field', assignedCell_eval_of]
        exact hLoZ125)
      hCompZ0
      (fun b => by
        have h := hCompChain ⟨b.val + 1, by omega⟩
        simpa using h)
    -- z₁ (= comp zs[2]) as a chainNat cast on its advice read (comp output, via `← h_gen_out_3`)
    have hz1cast := hCompCells 2 (by omega)
    rw [← h_gen_out_3, complete_output_eq,
      completeOutput_zs_getElem env _ _ 2 (by omega)] at hz1cast
    simp only [Vector.getElem_ofFn, eval_of] at hz1cast
    -- ── the LSB gate: constraint-forced bit and correction point ──
    simp only [lsbGate, Constraints.withSelector, circuit_norm] at hGate
    obtain ⟨hBool, hLsbX, hLsbY⟩ := hGate
    -- the copied base coordinates in the gate window
    simp only [circuit_norm] at hBxC hByC
    -- ▸▸ engine site 5: the final complete addition ◂◂
    subcircuit_rw at hFin
    simp only [add_spec_eq, add_assumptions_eq, add_envAssumptions_eq] at hFin
    -- ▸▸ engine site 6: the overflow check (the layouter child) ◂◂
    simp only [EnvAssumptions] at _hE
    have hOvSpec := hOv (by rw [ov_envAssumptions_eq]; exact _hE)
      (by rw [ov_assumptions_eq]
          constructor <;> norm_num [MulOverflow.numWords, PALLAS_BASE_CARD])
    rw [ov_spec_eq] at hOvSpec
    rw [show (MulOverflow.Spec = fun input => input.z0 = input.alpha + (tQ : Fp) ∧
        (input.k254 = 0 ∨ input.z130 = (2 ^ 124 : Fp)) ∧
        ∃ (sHi : Fp) (sLo : ℕ), sLo < 2 ^ 130 ∧
          input.alpha + input.k254 * (2 ^ 130 : Fp) = (sLo : Fp) + (2 ^ 130 : Fp) * sHi ∧
          (input.k254 = 0 ∨ sHi = 0) ∧
          (input.k254 = 1 ∨ input.z130 ≠ 0 ∨ sHi = 0)) from rfl] at hOvSpec
    try rw [ovInputs_eval_eq] at hOvSpec
    -- the z-cell projections reduce under `rw` (full unification) — the concrete-α spelling
    -- misses the simp discr key
    rw [mainRegion_output_z0, mainRegion_output_z130, mainRegion_output_k254] at hOvSpec
    simp only [circuit_norm] at hOvSpec
    try rw [halpha] at hOvSpec
    obtain ⟨hOvZ0, hOvDisj2, hOvEx⟩ := hOvSpec
    -- ── the canonicity ladder ──
    have hZhiLt : chainNat 0 bitsHi 125 < 2 ^ 125 :=
      lt_of_lt_of_le (chainNat_lt 0 bitsHi 125) (by norm_num)
    have hCloLt : chainNat 0 bitsLo 126 < 2 ^ 126 :=
      lt_of_lt_of_le (chainNat_lt 0 bitsLo 126) (by norm_num)
    have hCcLt : chainNat 0 bitsC 3 < 2 ^ 3 :=
      lt_of_lt_of_le (chainNat_lt 0 bitsC 3) (by norm_num)
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
    -- k₂₅₄ (the hi z-cell 0) as the top bit (hi output, via `← h_gen_out_1`)
    have hK254v := hHiCells 0 (by omega)
    rw [← h_gen_out_1, incomplete_output_eq,
      incompleteOutput_zs_getElem env _ _ _ 0 (by omega)] at hK254v
    simp only [Vector.getElem_ofFn, eval_of] at hK254v
    rw [show ((chainNat 0 bitsHi 1 : ℕ) : Fp) = (if bitsHi 0 then 1 else 0) from by
      simp only [chainNat]; cases bitsHi 0 <;> simp] at hK254v
    -- the canonicity argument: the witnessed scalar is α + t_q over ℕ
    have hKpart : ∀ k0n : ℕ, k0n ≤ 1 →
        ((2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 + k0n : ℕ) : Fp)
          = input_alpha + tQ →
        2 * chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 + k0n
          = ZMod.val input_alpha + tQNat := by
      intro k0n hk0le hcong
      refine k_canonical (R := 2 ^ 4 * chainNat 0 bitsLo 126 + 2 * chainNat 0 bitsC 3 + k0n)
        hK254v hHiZ124 hZhiLt ?_ ?_ ?_ hcong hOvDisj2 hOvEx
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
    have hfin : ∀ s : ℕ, s = 2 ^ 254 + ZMod.val input_alpha + tQNat →
        s • ({ x := input_base_x, y := input_base_y } : Point Fp)
          = ZMod.val input_alpha • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      intro s hs
      have hq : PALLAS_SCALAR_CARD = 2 ^ 254 + tQNat := by
        norm_num [PALLAS_SCALAR_CARD, tQNat]
      rw [hs, show 2 ^ 254 + ZMod.val input_alpha + tQNat
          = ZMod.val input_alpha + PALLAS_SCALAR_CARD from by rw [hq]; ring]
      exact point_card_reduce hOnC _
    -- the z₁ read at the LSB base row is the comp z-cell 2
    have hz1read : env.env.advice cfg.completeConfig.zComplete
        ((env.place i₀ + (offLsb) : ℕ) : ℤ)
        = ((chainNat (chainNat (chainNat 0 bitsHi 125) bitsLo 126) bitsC 3 : ℕ) : Fp) := by
      rw [show (offLsb : ℕ) = offComp + (2 * 2 + 2) from by
        simp only [offLsb, compSpan]]
      exact hz1cast
    -- ── the LSB case split: correction point, final addition, and the goal ──
    -- the copied base coordinates at the gate's next row
    have hbXr : env.env.advice cfg.addConfig.xP
        ((env.place i₀ + (offLsb + 1) : ℕ) : ℤ) = input_base_x :=
      hBxC.trans hBxIn
    have hbYr : env.env.advice cfg.addConfig.yP
        ((env.place i₀ + (offLsb + 1) : ℕ) : ℤ) = input_base_y :=
      hByC.trans hByIn
    rw [hbXr] at hLsbX
    rw [hbYr] at hLsbY
    -- M₃ := accScalar M₂ bitsC 3 ≥ 1
    have hM3pos : 1 ≤ accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 :=
      accScalar_one_le hM2pos bitsC 3
    simp only [Spec]
    show ({ x := output_x, y := output_y } : Point Fp)
      = ZMod.val input_alpha • ({ x := input_base_x, y := input_base_y } : Point Fp)
    rw [← h_output]
    rcases mul_eq_zero.mp hBool with hk0 | hk1
    · -- k₀ = 0: the correction point is −base, the result is [M₃ − 1]•base
      have hcx : env.env.advice cfg.addConfig.xP
          ((env.place i₀ + (offLsb) : ℕ) : ℤ) = input_base_x := by
        linear_combination hLsbX - input_base_x * hk0
      have hcy : env.env.advice cfg.addConfig.yP
          ((env.place i₀ + (offLsb) : ℕ) : ℤ) = -input_base_y := by
        linear_combination hLsbY + input_base_y * hk0
      have hcorr : (Point.mk
            (env.env.advice cfg.addConfig.xP ((env.place i₀ + (offLsb) : ℕ) : ℤ))
            (env.env.advice cfg.addConfig.yP ((env.place i₀ + (offLsb) : ℕ) : ℤ))
            : Point Fp)
          = -({ x := input_base_x, y := input_base_y } : Point Fp) := by
        rw [hcx, hcy]; rfl
      -- The final add's `q` summand (`comp.acc`) uses `x_gen_out_3.acc` (the complete output local);
      -- recover the concrete complete output (`← h_gen_out_3`) to reduce
      -- it to `.acc`, landing on `hCompAccV`/`hCompAccEq`. The final add's own output is NOT abstracted
      -- (it flows to `h_output`), so it stays concrete.
      obtain ⟨hResV, hResEq⟩ := hFin trivial (by
        rw [addInputs_eval_eq]
        constructor
        · show Point.Valid (eval env ({ x := _, y := _ } : Point (AssignedCell Fp)))
          rw [Point.eval_eq]
          simp only [output_assignAdvice, eval_of]
          rw [hcorr]
          exact Halo2.Ironwood.Point.valid_neg hbaseV
        · show Point.Valid (eval env _)
          rw [← h_gen_out_3]
          simp only [complete_output_eq]
          exact hCompAccV)
      rw [addInputs_eval_eq, ← h_gen_out_3] at hResEq
      simp only [Point.eval_eq, output_assignAdvice, eval_of,
        complete_output_eq, ← h_gen_out_2, incomplete_output_eq] at hResEq
      rw [hcorr, hCompAccEq,
        point_neg_add_nsmul hOnC hM3pos] at hResEq
      -- the working scalar: k = α + t_q with k₀ = 0
      have hK := hKpart 0 (by omega) (by
        push_cast
        rw [← hz1read]
        linear_combination hOvZ0 - hk0)
      have hM3v : accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3 - 1
          = 2 ^ 254 + ZMod.val input_alpha + tQNat := by
        rw [hm3]; omega
      rw [hM3v, hfin _ rfl] at hResEq
      convert hResEq using 1;
        simp only [mainRegion, circuit_norm, FormalRegionCircuit.output_call',
          incomplete_output_eq, complete_output_eq, add_output_eq, Vector.getElem_ofFn]
    · -- k₀ = 1: the correction point is the identity, the result is [M₃]•base
      have hcx : env.env.advice cfg.addConfig.xP
          ((env.place i₀ + (offLsb) : ℕ) : ℤ) = 0 := by
        -- `bool_check = lsb·(1−lsb)`: the `hk1` branch is `1 − lsb = 0`.
        linear_combination hLsbX + input_base_x * hk1
      have hcy : env.env.advice cfg.addConfig.yP
          ((env.place i₀ + (offLsb) : ℕ) : ℤ) = 0 := by
        linear_combination hLsbY - input_base_y * hk1
      have hcorr : (Point.mk
            (env.env.advice cfg.addConfig.xP ((env.place i₀ + (offLsb) : ℕ) : ℤ))
            (env.env.advice cfg.addConfig.yP ((env.place i₀ + (offLsb) : ℕ) : ℤ))
            : Point Fp)
          = (0 : Point Fp) := by
        rw [hcx, hcy]; rfl
      -- same final-add recovery as the `k₀ = 0` branch (`← h_gen_out_3` on the `comp.acc` summand).
      obtain ⟨hResV, hResEq⟩ := hFin trivial (by
        rw [addInputs_eval_eq]
        constructor
        · show Point.Valid (eval env ({ x := _, y := _ } : Point (AssignedCell Fp)))
          rw [Point.eval_eq]
          simp only [output_assignAdvice, eval_of]
          rw [hcorr]
          exact Halo2.Ironwood.Point.valid_zero
        · show Point.Valid (eval env _)
          rw [← h_gen_out_3]
          simp only [complete_output_eq]
          exact hCompAccV)
      rw [addInputs_eval_eq, ← h_gen_out_3] at hResEq
      simp only [Point.eval_eq, output_assignAdvice, eval_of,
        complete_output_eq, ← h_gen_out_2, incomplete_output_eq] at hResEq
      rw [hcorr, hCompAccEq,
        point_zero_add (Halo2.Ironwood.Point.valid_nsmul hbaseV _)] at hResEq
      -- the working scalar: k = α + t_q with k₀ = 1
      have hK := hKpart 1 (by omega) (by
        push_cast
        rw [← hz1read]
        linear_combination hOvZ0 + hk1)
      have hM3v : accScalar (accScalar (accScalar 2 bitsHi 125) bitsLo 126) bitsC 3
          = 2 ^ 254 + ZMod.val input_alpha + tQNat := by
        rw [hm3]; omega
      rw [hM3v, hfin _ rfl] at hResEq
      convert hResEq using 1;
        simp only [mainRegion, circuit_norm, FormalRegionCircuit.output_call',
          incomplete_output_eq, complete_output_eq, add_output_eq, Vector.getElem_ofFn]

  -- ══ Completeness ══
  -- Honest-side mirror on the faithful layouter structure: the six child chunks discharged via
  -- `subcircuit_rw` (completeness mode — the goal chunks strengthen to `EnvA ∧ A ∧ PA` and the
  -- engine introduces `h_spec_0..h_spec_5`), the honest accumulator threaded
  -- `[2]base → hi → lo → complete`, the honest chains `kBits`-driven, and the overflow child's
  -- honest `Spec` landed via `overflow_spec_honest` — consumed at the layouter level.
  completeness := by
    circuit_proof_start
    -- Reassemble the split `place`/`env` into a `Placed` value (named `env` again), so
    -- `subcircuit_rw`'s completeness leaf can locate all six child contracts via a single
    -- `penv : Placed …`.
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed ProverEnvironment Fp, pe.place = place ∧ pe.env = env := ⟨⟨place, env⟩, rfl, rfl⟩
    have hOnC0 := hPA
    -- ── peel the faithful layouter structure (witnesses AND goal): the MAIN REGION at i₀ and
    -- the layouter-level MulOverflow chunk at i₀+1 ──
    try simp only [synthesize, circuit_norm] at hwit ⊢
    obtain ⟨hWMain, hWOv⟩ := hwit
    -- ── peel the main-region witness list (bind/append/per-op only) ──
    simp only [mainRegion,
      RegionCircuit.operations_bind,
      operations_assignAdvice, operations_copyAdvice, operations_enable,
      operations_constrainConstant, RegionOperations.extendsWitnesses_append] at hWMain
    obtain ⟨hWInit, hWZi, _hWZc, hWHi, hWLo, hWComp, hWZ0, hWbx, hWby, hWCx, hWCy,
      _hWGate, hWFin, -⟩ := hWMain
    provable_type_simp
    obtain ⟨hIalpha, hBxIn, hByIn⟩ := h_input
    -- ── peel the main-region GOAL constraints to the assembly shape (the six child chunks
    -- exposed as conjuncts), then strengthen them via the engine: `subcircuit_rw` turns each
    -- chunk into its `EnvA ∧ A ∧ PA` precondition bundle (ExtendsWitnesses located from the
    -- peeled hW* context facts) and introduces the derived contract statements
    -- `h_spec_0..h_spec_5 : EnvA → A → PA → Spec ∧ ProverSpec` (init/hi/lo/comp/fin/overflow) ──
    simp only [mainRegion,
      RegionCircuit.operations_bind, RegionCircuit.operations_pure,
      operations_assignAdvice, operations_copyAdvice, operations_enable,
      operations_constrainConstant, RegionOperations.constraints_append,
      RegionOperations.constraints_cons, RegionOperations.constraints_nil,
      RegionOperation.constraints_assignAdvice, RegionOperation.constraints_constrainConstant,
      RegionOperation.constraints_constrainEqual, and_true, true_and]
    -- unify the overflow chunk's raw main-region output spelling: the goal peel above unfolded
    -- `mainRegion` into the bind chain inside the overflow chunk's input, while `hWOv` still
    -- carries the folded `(mainRegion …).output`. Unfold it in `hWOv` too, so `abstract_outputs`
    -- mints one local for the raw output and the engine's witness lookup matches the two chunk
    -- inputs on that shared local.
    simp only [mainRegion] at hWOv
    -- ▸▸ make every output opaque before the engine runs: the chained chunk inputs (hi's
    --    entering [2]base, lo's/comp's entering accumulators) speak the child locals `x_gen_out_j`
    --    (0=init, 1=hi, 2=lo, 3=comp), and the raw main-region output feeding the overflow chunk
    --    becomes `x_gen_out_4`, each with `h_gen_out_j : <output> = x_gen_out_j`. The engine then
    --    emits `h_spec_j` over those locals. ◂◂
    abstract_outputs
    -- Engine completeness mode: strengthen the whole main-region goal to the AND of the six
    -- children's `EnvA ∧ A ∧ PA` preconditions and introduce the premised derived statements
    -- `h_spec_0..h_spec_5 : EnvA → A → PA → Spec ∧ ProverSpec` (init/hi/lo/comp/fin/overflow).
    -- Mul's value bookkeeping (chains feeding BOTH child preconditions and the parent LSB gate)
    -- is threaded through the single strengthened goal; `h_spec_j`'s outputs land on `x_gen_out_j`.
    subcircuit_rw
    -- ── the base point: cells and value, both eval views ──
    have hOnC : ({ x := input_base_x, y := input_base_y } : Point Fp).OnCurve := hOnC0
    have hbaseV : ({ x := input_base_x, y := input_base_y } : Point Fp).Valid := Or.inl hOnC
    have hbXv : eval env.toEnvironment input_var_base_x = input_base_x := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hBxIn
    have hbYv : eval env.toEnvironment input_var_base_y = input_base_y := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hByIn
    have hbXp : eval env input_var_base_x = input_base_x := by
      rw [ProvableType.eval_field_prover]; simpa only [AssignedCell.eval] using hBxIn
    have hbYp : eval env input_var_base_y = input_base_y := by
      rw [ProvableType.eval_field_prover]; simpa only [AssignedCell.eval] using hByIn
    have halphap : eval env input_var_alpha = input_alpha := by
      rw [ProvableType.eval_field_prover]; simpa only [AssignedCell.eval] using hIalpha
    -- the honest working-scalar bits, as a local opaque constant (`obtain`, not `set`: a
    -- delta-accessible `kBits` body would let the elaborator's defeq unfold into the `tQNat`
    -- numeral landmine)
    obtain ⟨bits, hbits⟩ : ∃ b : BitsHint, b = kBits input_alpha := ⟨_, rfl⟩
    -- window landings: the children's derived families in `bits` vocabulary
    have hW0 : kBitsWindow input_alpha 0 = bits := by
      rw [kBitsWindow_zero, hbits]
    have hW125 : kBitsWindow input_alpha 125 = fun i => bits (125 + i) := by
      rw [kBitsWindow_as_kBits, hbits]
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
    have hbaseEvalV : eval env.toEnvironment ({ x := input_var_base_x, y := input_var_base_y }
        : Point (AssignedCell Fp)) = { x := input_base_x, y := input_base_y } := by
      rw [Point.eval_eq, hbXv, hbYv]
    have hbaseEvalP : eval env ({ x := input_var_base_x, y := input_var_base_y }
        : Point (AssignedCell Fp)) = { x := input_base_x, y := input_base_y } := by
      rw [Point.eval_eq_prover, hbXp, hbYp]
    -- ── z_init honest value (the witness) ──
    simp only [RegionOperations.extendsWitnesses_cons, RegionOperations.extendsWitnesses_nil,
      RegionOperation.extendsWitness_assignAdvice, and_true,
      Witgen.WitgenIROver.getElem_eval_ofFExpr, Witgen.FExprOver.eval] at hWZi
    -- ── init add: verifier Spec (acc = base + base = [2]base) via h_spec_0 ──
    have hSpecInit := (h_spec_0 trivial
      (by
        simp only [add_assumptions_eq]
        rw [addInputs_eval_eq, hbaseEvalV]
        exact ⟨hbaseV, hbaseV⟩)
      trivial).1
    simp only [add_spec_eq] at hSpecInit
    rw [addInputs_eval_eq, hbaseEvalV] at hSpecInit
    obtain ⟨-, hAccEq⟩ := hSpecInit
    -- init output on the local (verifier view). `hAccEq : eval env.toEnvironment x_gen_out_0 = …`
    -- (the engine emitted `h_spec_0` over `x_gen_out_0`); recover the concrete init output and
    -- reduce it to the add's output cells (env reads).
    have hAcc2 : eval env.toEnvironment x_gen_out_0
        = 2 • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      rw [← point_two_nsmul hOnC]; exact hAccEq
    rw [← h_gen_out_0, add_output_eq, Point.eval_eq, eval_of, eval_of] at hAcc2
    simp only [Placed.toEnvironment_env, Placed.toEnvironment_place] at hAcc2
    -- prover view: the same output cells, prover env reads (which agree with verifier reads on
    -- advice — `env.env.advice ≡ env.env.toEnvironment.advice`)
    have hAcc2P : eval env x_gen_out_0
        = 2 • ({ x := input_base_x, y := input_base_y } : Point Fp) := by
      rw [← point_two_nsmul hOnC, ← h_gen_out_0, add_output_eq, Point.eval_eq_prover,
        eval_of_prover, eval_of_prover]
      rw [← point_two_nsmul hOnC] at hAcc2; exact hAcc2
    -- ── hi half: constraints + honest RoundInvariant (over `bits`) ──
    have hHiPS := (h_spec_1 trivial
      (by
        simp only [hi_assumptions_eq]
        rw [hiInputs_eval_eq]
        show (eval env.toEnvironment ({ x := input_var_base_x, y := input_var_base_y }
          : Point (AssignedCell Fp))).OnCurve
        rw [hbaseEvalV]; exact hOnC)
      (by
        simp only [hi_proverAssumptions_eq]
        rw [hiInputs_eval_eq_prover]
        refine ⟨?_, 2, ?_, le_refl 2, by norm_num⟩
        · show (eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))).OnCurve
          rw [hbaseEvalP]; exact hOnC
        · -- hi's entering accumulator = init output `x_gen_out_0` (a Point) = [2]base
          show eval env x_gen_out_0
            = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
              : Point (AssignedCell Fp))
          rw [hbaseEvalP]
          exact hAcc2P)).2
    simp only [hi_proverSpec_eq, MulIncomplete.RoundInvariant] at hHiPS
    rw [hiInputs_alpha_prover] at hHiPS
    simp only [fexpr_expr_eval_prover, halphap, hBF0] at hHiPS
    obtain ⟨hHiChain, hHiAccCl⟩ := hHiPS
    obtain ⟨hHiZ0, hHiZstep⟩ := zChain_split hHiChain
    -- the honest hi chain, as chainNat casts
    have hHiCells := chain_cast (n := 124) _ _ 0 bits
      (by
        rw [hiInputs_eval_eq_prover]
        simp only [output_assignAdvice, Halo2.ProvableType.eval_field_prover', assignedCell_eval_of, Nat.cast_zero]
        exact hWZi)
      hHiZ0 hHiZstep
    -- the honest hi accumulator: [accScalar 2 bits 125] • base. Entering acc = init output
    -- `x_gen_out_0` (a Point); its coords collapse to the whole local via `point_var_eval_eq_prover`,
    -- landing on `hAcc2P`. The hi output is `x_gen_out_1`; recover the concrete hi output to reduce
    -- its `.xA`/`.yA` fields to cells.
    have hHiOut := hHiAccCl 2
      (by
        rw [hiInputs_eval_eq_prover]
        show eval env x_gen_out_0
          = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))
        rw [hbaseEvalP]
        exact hAcc2P)
      (le_refl 2) (by norm_num)
    rw [← h_gen_out_1, incomplete_output_eq, incompleteOutput_acc_prover,
      hiInputs_eval_eq_prover] at hHiOut
    simp only [eval_of_prover] at hHiOut
    rw [hbaseEvalP] at hHiOut
    -- the honest hi z-cells 0 and 124 (over the hi output local; recover concrete)
    have hHiZ124 := hHiCells 124 (by omega)
    rw [← h_gen_out_1, incomplete_output_eq,
      incompleteOutput_zs_getElem_prover env _ _ _ 124 (by omega)] at hHiZ124
    simp only [Vector.getElem_ofFn, eval_of_prover] at hHiZ124
    have hHiZtop := hHiCells 0 (by omega)
    rw [← h_gen_out_1, incomplete_output_eq,
      incompleteOutput_zs_getElem_prover env _ _ _ 0 (by omega)] at hHiZtop
    simp only [Vector.getElem_ofFn, eval_of_prover] at hHiZtop
    -- ── lo half ──
    have hmB := m_bounds bits (fun i => bits (125 + i))
    have hLoPS := (h_spec_2 trivial
      (by
        simp only [lo_assumptions_eq]
        rw [hiInputs_eval_eq]
        show (eval env.toEnvironment ({ x := input_var_base_x, y := input_var_base_y }
          : Point (AssignedCell Fp))).OnCurve
        rw [hbaseEvalV]; exact hOnC)
      (by
        simp only [lo_proverAssumptions_eq]
        rw [hiInputs_eval_eq_prover]
        refine ⟨?_, accScalar 2 bits 125, ?_, hmB.1, hmB.2.1⟩
        · show (eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))).OnCurve
          rw [hbaseEvalP]; exact hOnC
        · -- lo's entering accumulator = hi output `x_gen_out_1`; recover concrete
          show eval env x_gen_out_1.acc
            = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
              : Point (AssignedCell Fp))
          rw [← h_gen_out_1, incomplete_output_eq]
          show eval env (Point.mk _ _) = _
          rw [Point.eval_eq_prover, eval_of_prover, eval_of_prover, hbaseEvalP]
          exact hHiOut)).2
    simp only [lo_proverSpec_eq, MulIncomplete.RoundInvariant] at hLoPS
    rw [hiInputs_alpha_prover] at hLoPS
    simp only [fexpr_expr_eval_prover, halphap, hBF125] at hLoPS
    obtain ⟨hLoChain, hLoAccCl⟩ := hLoPS
    obtain ⟨hLoZ0, hLoZstep⟩ := zChain_split hLoChain
    -- the honest lo chain, continued from the hi chain (hi z-cell 124, via `← h_gen_out_1`)
    have hLoCells := chain_cast (n := 125) _ _ (chainNat 0 bits 125) (fun i => bits (125 + i))
      (by
        rw [hiInputs_eval_eq_prover]
        rw [← h_gen_out_1, incomplete_output_eq]
        simp only [Vector.getElem_ofFn, Halo2.ProvableType.eval_field_prover', assignedCell_eval_of]
        exact hHiZ124)
      hLoZ0 hLoZstep
    -- the honest lo accumulator (lo output is `x_gen_out_2`)
    have hLoOut := hLoAccCl (accScalar 2 bits 125)
      (by
        rw [hiInputs_eval_eq_prover]
        show eval env x_gen_out_1.acc
          = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))
        rw [← h_gen_out_1, incomplete_output_eq]
        show eval env (Point.mk _ _) = _
        rw [Point.eval_eq_prover, eval_of_prover, eval_of_prover, hbaseEvalP]
        exact hHiOut)
      hmB.1 hmB.2.1
    rw [← h_gen_out_2, incomplete_output_eq, incompleteOutput_acc_prover,
      hiInputs_eval_eq_prover] at hLoOut
    simp only [eval_of_prover] at hLoOut
    rw [hbaseEvalP] at hLoOut
    have hLoZ125 := hLoCells 125 (by omega)
    rw [← h_gen_out_2, incomplete_output_eq,
      incompleteOutput_zs_getElem_prover env _ _ _ 125 (by omega)] at hLoZ125
    simp only [Vector.getElem_ofFn, eval_of_prover] at hLoZ125
    -- ── complete rounds ──
    have hM2pos : 1 ≤ accScalar (accScalar 2 bits 125) (fun i => bits (125 + i)) 126 :=
      hmB.2.2.1
    have hLoOutV : Point.Valid (Point.ofCoords
        (env.env.toEnvironment.advice cfg.loConfig.xA
          ((env.place i₀ + (offLo + 125 + 2) : ℕ) : ℤ),
         env.env.toEnvironment.advice cfg.loConfig.lambda1
          ((env.place i₀ + (offLo + 125 + 2) : ℕ) : ℤ))) := by
      show (Point.mk _ _).Valid
      rw [hLoOut]
      exact Halo2.Ironwood.Point.valid_nsmul hbaseV _
    -- comp's entering accumulator = lo output `x_gen_out_2`; recover concrete (`← h_gen_out_2`) to
    -- reduce its `.xA`/`.yA` to the lo output cells (matching `hLoOutV`).
    have hCompBoth := h_spec_3 trivial
      (by
        simp only [comp_assumptions_eq]
        rw [compInputs_eval_eq, ← h_gen_out_2, incomplete_output_eq]
        simp only [Halo2.ProvableType.eval_field', assignedCell_eval_of, Placed.toEnvironment_env, Placed.toEnvironment_place]
        rw [hbaseEvalV]
        exact ⟨hLoOutV, hbaseV⟩)
      (by
        simp only [comp_proverAssumptions_eq]
        rw [compInputs_eval_eq_prover, ← h_gen_out_2, incomplete_output_eq]
        simp only [Halo2.ProvableType.eval_field_prover', assignedCell_eval_of]
        rw [hbaseEvalP]
        exact ⟨hLoOutV, hbaseV⟩)
    have hCompPS := hCompBoth.2
    simp only [comp_proverSpec_eq, MulComplete.RoundInvariant] at hCompPS
    rw [compInputs_alpha_prover] at hCompPS
    simp only [fexpr_expr_eval_prover, halphap, hW251] at hCompPS
    obtain ⟨hCompChain, hCompAccCl⟩ := hCompPS
    -- the honest complete-phase accumulator validity
    obtain ⟨hCompAccV, -⟩ := hCompAccCl
      (by
        rw [compInputs_eval_eq_prover, ← h_gen_out_2, incomplete_output_eq]
        simp only [Halo2.ProvableType.eval_field_prover', assignedCell_eval_of]
        exact hLoOutV)
      (by
        rw [compInputs_eval_eq_prover]
        show Point.Valid (eval env ({ x := input_var_base_x, y := input_var_base_y }
          : Point (AssignedCell Fp)))
        rw [hbaseEvalP]; exact hbaseV)
    -- the honest complete-phase z-chain (lo z-cell 125 entering, via `← h_gen_out_2`)
    have hCompZ0 := hCompChain ⟨0, by omega⟩
    simp only [if_pos] at hCompZ0
    have hCompCells := chain_cast (n := 2) _ _
      (chainNat (chainNat 0 bits 125) (fun i => bits (125 + i)) 126) (fun i => bits (251 + i))
      (by
        rw [compInputs_eval_eq_prover, ← h_gen_out_2, incomplete_output_eq]
        simp only [Vector.getElem_ofFn, Halo2.ProvableType.eval_field_prover', assignedCell_eval_of]
        exact hLoZ125)
      hCompZ0
      (fun b => by
        have h := hCompChain ⟨b.val + 1, by omega⟩
        simpa using h)
    -- comp output is `x_gen_out_3`; recover concrete to reduce its `.zs[2]`
    have hz1cast := hCompCells 2 (by omega)
    rw [← h_gen_out_3, complete_output_eq,
      completeOutput_zs_getElem_prover env _ _ 2 (by omega)] at hz1cast
    simp only [Vector.getElem_ofFn, eval_of_prover] at hz1cast
    -- ── the honest chain values, `kBits`-driven ──
    have hck := cells_kNat input_alpha
    rw [hbits] at hHiZtop hHiZ124 hz1cast
    rw [hck.1] at hHiZtop
    rw [hck.2.1] at hHiZ124
    rw [hck.2.2] at hz1cast
    -- ── the honest z₀ value: 2·z₁ + k₀ reconstructs k. The witness's z₁ read is comp's zs[2],
    --    abstracted to `x_gen_out_3.zs[2]`; recover the concrete comp output (`← h_gen_out_3`). ──
    simp only [← h_gen_out_3] at hWZ0
    simp only [RegionOperations.extendsWitnesses_cons, RegionOperations.extendsWitnesses_nil,
      RegionOperation.extendsWitness_assignAdvice, and_true,
      Witgen.WitgenIROver.getElem_eval_ofFExpr, Witgen.FExprOver.eval,
      kBitWindowExpr_expr_eval, readCell,
      complete_output_eq, Vector.getElem_ofFn] at hWZ0
    -- the LSB bit landing: rewrite the closure's scalar-cell read to `input_alpha`, then the
    -- derived bit to `bits 254`
    have haevalv : AssignedCell.eval env.place env.env.toEnvironment input_var_alpha
        = input_alpha := hIalpha
    have hlsb0 : kBitsWindow input_alpha 254 0 = bits 254 := by
      rw [kBitsWindow_eq_kBits, hbits]
    simp only [haevalv, hlsb0] at hWZ0
    -- restate defeq-clean (the `#v[·][0]`/`Placed` residues collapse)
    have hWZ0' : env.env.toEnvironment.advice cfg.completeConfig.zComplete
        ((env.place i₀ + (offLsb + 1) : ℕ) : ℤ)
        = 2 * env.env.toEnvironment.advice cfg.completeConfig.zComplete
            ((env.place i₀ + (offComp + 2 * 2 + 2) : ℕ) : ℤ)
          + (if bits 254 then 1 else 0) := hWZ0
    rw [hz1cast] at hWZ0'
    -- z₀ = ↑(kNat α)  (`z0_cell_value`)
    have hz0v : env.env.toEnvironment.advice cfg.completeConfig.zComplete
        ((env.place i₀ + (offLsb + 1) : ℕ) : ℤ)
        = ((kNat input_alpha : ℕ) : Fp) := by
      refine z0_cell_value input_alpha rfl ?_
      rw [← hbits]
      exact hWZ0'
    -- ── the honest correction-point cells ──
    simp only [RegionOperations.extendsWitnesses_cons, RegionOperations.extendsWitnesses_nil,
      RegionOperation.extendsWitness_assignAdvice, and_true,
      Witgen.WitgenIROver.getElem_eval_ofFExpr, Witgen.FExprOver.eval,
      Witgen.FExprOver.neg, kBitWindowExpr_expr_eval, neg_one_mul, readCell,
      AssignedCell.eval] at hWCx hWCy
    simp only [hIalpha, hlsb0] at hWCx hWCy
    have hCxv : env.env.toEnvironment.advice cfg.addConfig.xP
        ((env.place i₀ + (offLsb) : ℕ) : ℤ)
        = (if bits 254 then 0 else input_base_x) := by
      refine Eq.trans hWCx ?_
      rcases Bool.dichotomy (bits 254) with h | h <;> simp only [h]
      · exact hBxIn
      · rfl
    have hCyv : env.env.toEnvironment.advice cfg.addConfig.yP
        ((env.place i₀ + (offLsb) : ℕ) : ℤ)
        = (if bits 254 then 0 else -input_base_y) := by
      refine Eq.trans hWCy ?_
      rcases Bool.dichotomy (bits 254) with h | h <;> simp only [h]
      · exact congrArg Neg.neg hByIn
      · rfl
    -- ── the copied base coordinates (witness values) ──
    simp only [RegionOperations.extendsWitnesses_cons, RegionOperations.extendsWitnesses_nil,
      RegionOperation.extendsWitness_assignAdvice,
      RegionOperation.extendsWitness_constrainEqual, and_true,
      eval_ofFExpr_zero, Witgen.FExprOver.eval, WitgenEnv.readVar_halo2,
      AssignedCell.eval] at hWbx hWby
    -- ── the complete-phase verifier Spec (`h_spec_3.1`) ──
    have hCompSpecV := hCompBoth.1
    simp only [comp_spec_eq] at hCompSpecV
    obtain ⟨bitsC', hCompRIv⟩ := hCompSpecV
    simp only [MulComplete.RoundInvariant] at hCompRIv
    obtain ⟨-, hCompAccClv⟩ := hCompRIv
    obtain ⟨hCompAccVv, -⟩ := hCompAccClv
      (by
        rw [compInputs_eval_eq, ← h_gen_out_2, incomplete_output_eq]
        simp only [Halo2.ProvableType.eval_field', assignedCell_eval_of, Placed.toEnvironment_env, Placed.toEnvironment_place]
        exact hLoOutV)
      (by
        rw [compInputs_eval_eq]
        show Point.Valid (eval env.toEnvironment ({ x := input_var_base_x, y := input_var_base_y }
          : Point (AssignedCell Fp)))
        rw [hbaseEvalV]; exact hbaseV)
    rw [← h_gen_out_3, complete_output_eq, completeOutput_acc] at hCompAccVv
    -- ── assemble the strengthened goal: per-child `EnvA ∧ A ∧ PA` triples for the six chunks
    -- (init/hi/lo/comp/fin/overflow) + the parent's own constraints (z_init, the two base
    -- copies, the LSB gate) ──
    refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · -- init add EnvAssumptions (trivial)
      exact trivial
    · -- init add Assumptions: both summands are the (valid) base point
      simp only [add_assumptions_eq]
      rw [addInputs_eval_eq, hbaseEvalV]
      exact ⟨hbaseV, hbaseV⟩
    · -- init add ProverAssumptions (trivial)
      exact trivial
    · -- z_init = 0 (the constrainConstant constraint, from the assign witness)
      rw [output_assignAdvice, cell_eval_of]
      exact hWZi
    · -- hi EnvAssumptions (trivial)
      exact trivial
    · -- hi Assumptions: base on-curve
      simp only [hi_assumptions_eq]
      rw [hiInputs_eval_eq]
      show (eval env.toEnvironment ({ x := input_var_base_x, y := input_var_base_y }
        : Point (AssignedCell Fp))).OnCurve
      rw [hbaseEvalV]; exact hOnC
    · -- hi ProverAssumptions: honest accumulator entry [2]base
      simp only [hi_proverAssumptions_eq]
      rw [hiInputs_eval_eq_prover]
      refine ⟨?_, 2, ?_, le_refl 2, by norm_num⟩
      · show (eval env ({ x := input_var_base_x, y := input_var_base_y }
          : Point (AssignedCell Fp))).OnCurve
        rw [hbaseEvalP]; exact hOnC
      · -- init output entering: the whole-point local lands on `hAcc2P`
        show eval env x_gen_out_0
          = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))
        rw [hbaseEvalP]
        exact hAcc2P
    · -- lo EnvAssumptions (trivial)
      exact trivial
    · -- lo Assumptions
      simp only [lo_assumptions_eq]
      rw [hiInputs_eval_eq]
      show (eval env.toEnvironment ({ x := input_var_base_x, y := input_var_base_y }
        : Point (AssignedCell Fp))).OnCurve
      rw [hbaseEvalV]; exact hOnC
    · -- lo ProverAssumptions: honest accumulator entry [accScalar 2 bits 125]base
      simp only [lo_proverAssumptions_eq]
      rw [hiInputs_eval_eq_prover]
      refine ⟨?_, accScalar 2 bits 125, ?_, hmB.1, hmB.2.1⟩
      · show (eval env ({ x := input_var_base_x, y := input_var_base_y }
          : Point (AssignedCell Fp))).OnCurve
        rw [hbaseEvalP]; exact hOnC
      · -- hi output entering: recover concrete (`← h_gen_out_1`), land on `hHiOut`
        show eval env x_gen_out_1.acc
          = _ • eval env ({ x := input_var_base_x, y := input_var_base_y }
            : Point (AssignedCell Fp))
        rw [← h_gen_out_1, incomplete_output_eq]
        show eval env (Point.mk _ _) = _
        rw [Point.eval_eq_prover, eval_of_prover, eval_of_prover, hbaseEvalP]
        exact hHiOut
    · -- comp EnvAssumptions (trivial)
      exact trivial
    · -- comp Assumptions (lo output entering, via `← h_gen_out_2`)
      simp only [comp_assumptions_eq]
      rw [compInputs_eval_eq, ← h_gen_out_2, incomplete_output_eq]
      simp only [Halo2.ProvableType.eval_field', assignedCell_eval_of, Placed.toEnvironment_env, Placed.toEnvironment_place]
      rw [hbaseEvalV]
      exact ⟨hLoOutV, hbaseV⟩
    · -- comp ProverAssumptions (lo output entering, via `← h_gen_out_2`)
      simp only [comp_proverAssumptions_eq]
      rw [compInputs_eval_eq_prover, ← h_gen_out_2, incomplete_output_eq]
      simp only [Halo2.ProvableType.eval_field_prover', assignedCell_eval_of]
      rw [hbaseEvalP]
      exact ⟨hLoOutV, hbaseV⟩
    · -- base_x copy equality
      rw [cellOf_eval]
      exact hWbx
    · -- base_y copy equality
      rw [cellOf_eval]
      exact hWby
    · -- the q_mul_lsb gate on the honest values
      simp only [lsbGate, Constraints.withSelector, circuit_norm]
      -- the gate-window reads: z₁ at the LSB base row is the comp z-cell 2
      have hz1gate : env.env.toEnvironment.advice cfg.completeConfig.zComplete
          ((env.place i₀ + (offLsb) : ℕ) : ℤ)
          = ((kNat input_alpha / 2 : ℕ) : Fp) := by
        rw [show (offLsb : ℕ) = offComp + (2 * 2 + 2) from by
          simp only [offLsb, compSpan]]
        exact hz1cast
      have hbxg : env.env.toEnvironment.advice cfg.addConfig.xP
          ((env.place i₀ + (offLsb + 1) : ℕ) : ℤ) = input_base_x :=
        hWbx.trans hBxIn
      have hbyg : env.env.toEnvironment.advice cfg.addConfig.yP
          ((env.place i₀ + (offLsb + 1) : ℕ) : ℤ) = input_base_y :=
        hWby.trans hByIn
      rw [hz0v, hz1gate, hCxv, hCyv, hbxg, hbyg]
      -- k₀ = z₀ − 2·z₁ is the honest bit
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
      rw [hsplit]
      rcases Bool.dichotomy (bits 254) with h | h <;> rw [h] <;>
        simp only [Bool.false_eq_true, if_false, if_true] <;>
        refine ⟨by ring, by ring, by ring⟩
    · -- final add EnvAssumptions (trivial)
      exact trivial
    · -- final add Assumptions: correction point (±base or identity) and comp acc are valid
      simp only [add_assumptions_eq]
      rw [addInputs_eval_eq]
      constructor
      · show Point.Valid (eval env.toEnvironment ({ x := _, y := _ }
          : Point (AssignedCell Fp)))
        rw [Point.eval_eq]
        simp only [output_assignAdvice, eval_of]
        simp only [Placed.toEnvironment_env, Placed.toEnvironment_place]
        rw [hCxv, hCyv]
        rcases Bool.dichotomy (bits 254) with h | h <;> rw [h]
        · simp only [Bool.false_eq_true, if_false]
          -- land `valid_neg` via a cheap POINT-level `rfl` step: unifying at the `Valid` level
          -- (`{x, -y}.Valid =?= (-{x,y}).Valid`) sends the unifier down the OnCurve polynomial
          -- equations (~1.5s failing path) before it recovers
          rw [show ({ x := input_base_x, y := -input_base_y } : Point Fp)
                = -{ x := input_base_x, y := input_base_y } from rfl]
          exact Halo2.Ironwood.Point.valid_neg hbaseV
        · simp only [if_true]
          exact Halo2.Ironwood.Point.valid_zero
      · -- comp acc validity: recover the concrete comp output (`← h_gen_out_3`), land on `hCompAccVv`
        show Point.Valid (eval env.toEnvironment _)
        rw [← h_gen_out_3]
        simp only [complete_output_eq]
        exact hCompAccVv
    · -- final add ProverAssumptions (trivial)
      exact trivial
    · -- overflow EnvAssumptions (the parent's, by projection)
      rw [ov_envAssumptions_eq]; exact _hE
    · -- overflow Assumptions (field-capacity bounds at K = 10)
      rw [ov_assumptions_eq]
      constructor <;> norm_num [MulOverflow.numWords, PALLAS_BASE_CARD]
    · -- overflow ProverAssumptions: the honest running-sum cells satisfy the overflow Spec. The
      -- input's z-cells are projections of the raw main-region output local (`x_gen_out_4`);
      -- recover the concrete bind-chain output (`← h_gen_out_4`), then reduce the projections
      -- lazily via `circuit_norm` and land the cells on env reads.
      simp only [ov_proverAssumptions_eq]
      try rw [ovInputs_eval_eq_prover]
      rw [← h_gen_out_4]
      simp only [circuit_norm]
      rw [incomplete_call_output]
      simp only [Vector.getElem_ofFn, AssignedCell.of_cell, Cell.of_regionIndex,
        Cell.of_rowOffset, Cell.of_column, Environment.get_advice]
      rw [hz0v, hHiZ124, hHiZtop]
      exact overflow_spec_honest' input_alpha rfl rfl rfl

/-! ## Bundle contract bridges, shared by the layouter-level consumers (generated; the
bundle stays folded) -/

derive_contract_bridges mul := mul

end Halo2.Ironwood.Ecc.Mul
