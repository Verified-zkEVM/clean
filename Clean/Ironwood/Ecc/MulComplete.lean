import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Halo2.Tactics.AbstractOutputs
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.MulCompleteTheorems
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulIncomplete
import Clean.Halo2.CircuitTypeDeriving

/-!
Variable-base scalar multiplication, *complete* phase: the final three bits (`COMPLETE_RANGE`),
processed with the complete group law, which is exceptional-case-free on all Pallas points. Per
bit: extend the running sum `z` (`z_next = 2·z_cur + k`) in the `z_complete` column, conditionally
negate the base `y` (`y_p = if k then base_y else −base_y`, checked by the `q_mul_decompose_var`
gate), and perform two chained complete additions `tmp = U + acc`, `acc' = acc + tmp` with
`U = (base.x, ±base.y)` — the `(acc + U) + acc` double-and-add step.

Reference: `halo2_gadgets/src/ecc/chip/mul/complete.rs`.
-/

open ProvableType.Halo2 (eval_cells)

namespace Zcash.Circuits.Ecc.MulComplete

open Halo2
open Ecc.Mul.Incomplete.DoubleAndAdd (zRunValue)
open Ecc.MulIncomplete (BitsHint kBitsWindow kBitsWindow_eq_kBits)

/-! ## Config -/

structure Config where
  -- Selector used to constrain the cells used in complete addition.
  qDecompose : Selector
  -- Advice column used to decompose the scalar in complete addition.
  zComplete : Column .advice
  -- Configuration used in complete addition.
  addConfig : Add.Config

/-! ## The `q_mul_decompose_var` gate

    | y_p | z_complete |
    --------------------
    | y_p | z_{i + 1}  |
    |     | base_y     |   ← selector enabled here
    |     | z_i        |
-/

/-- Checks that the scalar decomposition is correct for the complete-addition bits (the
incomplete-addition gate `q_mul` already checks it for the other bits): `k = z_i − 2·z_{i+1}` is a
bit, and `y_p` is `base_y` conditionally negated by it (`k = 1 ⇒ y_p = base_y`, `k = 0 ⇒
y_p = −base_y`). -/
def decomposeGate (cfg : Config) : Gate Fp :=
  let zPrev : Expression Fp Query := queryAdvice cfg.zComplete (-1)   -- z_{i+1}
  let zNext : Expression Fp Query := queryAdvice cfg.zComplete 1      -- z_i
  let baseY : Expression Fp Query := queryAdvice cfg.zComplete 0      -- base_y
  let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP (-1)   -- y_p
  Gate.withSelector "Decompose scalar for complete bits of variable-base mul"
    cfg.qDecompose [zPrev, zNext, baseY, yP] <|
    let k := zNext - (2 : Fp) * zPrev
    -- `k · (1 − k)`, with the `1` on the left of the subtraction to match the compiled gate AST.
    let boolCheck := k * ((1 : Fp) - k)
    let ySwitch := k * (baseY - yP) + ((1 : Fp) - k) * (baseY + yP)
    [ ("bool_check", boolCheck), ("y_switch", ySwitch) ]

/-- Enable equality on `z_complete`, allocate the selector, register the gate. The `add::Config`'s
columns are already equality-enabled by `add`'s own `configure`. -/
def configure (zComplete : Column .advice) (addConfig : Add.Config) : Configure Fp Config := do
  enableEquality zComplete.toAny
  let qDecompose ← selector
  let cfg : Config := { qDecompose, zComplete, addConfig }
  createGate (decomposeGate cfg)
  return cfg

/-! ## Inputs / Output -/

structure Inputs (F : Type) where
  -- Scalar reading program (prover hint); the complete-range bits are the `w`-shifted window of
  -- its bits, derived into the witnesses without constraining the scalar cell.
  alpha : Unconstrained field F
  -- The base point.
  base : Point F
  -- x-coordinate of the entering accumulator, from incomplete addition.
  xA : F
  -- y-coordinate of the entering accumulator, from incomplete addition.
  yA : F
  -- The entering running sum.
  z : F
deriving CircuitType

structure Output (numBits : ℕ) (F : Type) where
  -- The final accumulator point.
  acc : Point F
  -- The interstitial running sums, one per bit.
  zs : Vector F numBits
deriving ProvableStruct

/-! ## Value-level round algebra -/

/-- The conditionally-negated per-bit point `U = (base.x, if bit then base.y else −base.y)`. -/
def stepBasePoint (base : Point Fp) (bit : Bool) : Point Fp :=
  { x := base.x, y := if bit then base.y else -base.y }

/-- One complete-addition round on `Point`s: `acc + (U + acc)` (`tmp = U + acc`, `acc' = acc + tmp`). -/
def stepPoint (base : Point Fp) (acc : Point Fp) (bit : Bool) : Point Fp :=
  acc + (stepBasePoint base bit + acc)

/-- The accumulator after the first `b` complete rounds. -/
def accPoint (base : Point Fp) (acc0 : Point Fp) (bits : BitsHint) : ℕ → Point Fp
  | 0 => acc0
  | b + 1 => stepPoint base (accPoint base acc0 bits b) (bits b)

/-- `stepBasePoint` is valid when `base` is (negation preserves validity). -/
theorem stepBasePoint_valid {base : Point Fp} (hbase : base.Valid) (bit : Bool) :
    (stepBasePoint base bit).Valid := by
  simp only [stepBasePoint]
  rcases Bool.dichotomy bit with hb | hb <;> rw [hb]
  · simpa using Point.valid_neg hbase
  · simpa using hbase

/-- Validity is preserved by a complete round (the complete group law is total on valid points). -/
theorem stepPoint_valid {base acc : Point Fp} (hbase : base.Valid) (hacc : acc.Valid)
    (bit : Bool) : (stepPoint base acc bit).Valid :=
  Point.valid_add hacc
    (Point.valid_add (stepBasePoint_valid hbase bit) hacc)

theorem accPoint_valid {base acc0 : Point Fp} (hbase : base.Valid) (hacc0 : acc0.Valid)
    (bits : BitsHint) (b : ℕ) : (accPoint base acc0 bits b).Valid := by
  induction b with
  | zero => exact hacc0
  | succ k ih => exact stepPoint_valid hbase ih (bits k)

/-- `accPoint` only reads the bits below `n` — congruence under agreement on those. -/
theorem accPoint_congr {base acc0 : Point Fp} {bits₁ bits₂ : BitsHint} (n : ℕ)
    (h : ∀ j, j < n → bits₁ j = bits₂ j) :
    accPoint base acc0 bits₁ n = accPoint base acc0 bits₂ n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [accPoint, ih (fun j hj => h j (by omega)), h k (by omega)]

/-! ## The per-bit round loop

Each iteration uses two rows (two complete additions). Row layout relative to the ambient `offset`,
with round `iter` at base row `r := offset + 2·iter`:

    | x_p | y_p | x_qr    | y_qr    | z_complete |
    ---------------------------------------------
    | U_x | U_y | acc_x   | acc_y   | z_{i + 1}  |   r
    |acc_x|acc_y| acc+U_x | acc+U_y | base_y     |   r + 1  ← q_mul_decompose_var enabled
    |     |     | res_x   | res_y   | z_i        |   r + 2

`z` is copied in from incomplete addition at row `offset`. Each round assigns `z_i`, copies `base_y`
into `z_complete`, assigns the conditionally-negated `y_p`, and calls `add` twice: `U + acc` at `r`,
`acc + tmp` at `r + 1`. -/

/-- The working-scalar bit expressions for this phase: bit `i` is `kBitsWindow (alpha value)
 w i`, i.e. bit `254 − (w + i)` of `t_q + alpha.val`. A single bit-family program binds the
scalar's reading program once and yields the window as plain expressions. -/
def kBitWindowExpr (alpha : FExpr Fp) (w i : ℕ) : BExpr Fp :=
  .neq ((Witgen.NExprOver.add (.const Mul.tQNat) (.val alpha)).testBit
    (.const (254 - (w + i)))) (.const 1)

/-- Binds the scalar's reading program once, then produces the per-round window expressions. -/
def kBitWindowProg (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) (w : ℕ) :
    Witgen.MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp) :=
  (fun a i => kBitWindowExpr a w i) <$> alpha

/-- The value of a plain bit-expression family in a step-locals context. -/
def bexprsVal (ebits : ℕ → BExpr Fp)
    (ctx : Witgen.CtxOver Fp (Placed ProverEnvironment Fp)) : BitsHint :=
  fun i => (ebits i).eval ctx

/-- The value of a bit-family program at a placed prover environment. -/
def ebitsVal (ebits : Witgen.MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp))
    (env : Placed ProverEnvironment Fp) : BitsHint :=
  fun i => Witgen.MOver.evalBool env ((fun bs => bs i) <$> ebits)

/-- `kBitWindowExpr`'s value is `kBitsWindow` of the scalar expression's value. -/
theorem bexprsVal_kBitWindowExpr (alpha : FExpr Fp) (w : ℕ)
    (ctx : Witgen.CtxOver Fp (Placed ProverEnvironment Fp)) :
    bexprsVal (kBitWindowExpr alpha w) ctx
      = kBitsWindow (Witgen.FExprOver.eval ctx alpha) w := by
  funext i
  simp only [bexprsVal, kBitWindowExpr, MulIncomplete.kBitsWindow,
    Witgen.NExprOver.testBit, Witgen.BExprOver.eval, Witgen.NExprOver.eval,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  simp only [FiniteField.val_F]

/-- `kBitWindowProg`'s values are `kBitsWindow` of the scalar program's value. -/
theorem ebitsVal_kBitWindowProg (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (w : ℕ) (env : Placed ProverEnvironment Fp) :
    ebitsVal (kBitWindowProg alpha w) env
      = kBitsWindow (Witgen.MOver.eval (value := field) env alpha) w := by
  funext i
  rcases h : alpha #[] with ⟨a, steps⟩
  have := congrFun (bexprsVal_kBitWindowExpr a w
    { env, locals := Witgen.evalSteps env steps.toList }) i
  simp only [bexprsVal] at this
  simp only [ebitsVal, kBitWindowProg, Witgen.MOver.evalBool, Witgen.MOver.eval,
    Witgen.M.map_def, h, this]
  simp only [Witgen.eval_field]

/-- The conditionally-negated `y_p` at round `iter`: `if k then base_y else −base_y`, with the
bit `k` selected from the family program. -/
def yPWit (baseY : AssignedCell Fp) (ebits : Witgen.MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp))
    (iter : ℕ) : WitgenIR Fp 1 :=
  Witgen.MOver.toIRScalar ((fun bs => .ite (bs iter) (.expr baseY)
    (Witgen.FExprOver.neg (.expr baseY))) <$> ebits)

/-- `yPWit`'s prover value: `±base_y` by the round's bit value. -/
theorem yPWit_eval (baseY : AssignedCell Fp)
    (ebits : Witgen.MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp)) (iter : ℕ)
    (env : Placed ProverEnvironment Fp) (hi : 0 < 1) :
    ((yPWit baseY ebits iter).eval env)[0]
      = if ebitsVal ebits env iter then readCell env baseY
        else -(readCell env baseY) := by
  rcases h : ebits #[] with ⟨bs, steps⟩
  simp only [yPWit, ebitsVal, Witgen.MOver.toIRScalar, Witgen.MOver.toIR,
    Witgen.MOver.evalBool, h, Witgen.WitgenIROver.eval,
    Witgen.FExprOver.eval, Witgen.FExprOver.neg, Witgen.VExprOver.eval, circuit_norm]
  rcases (bs iter).eval { env, locals := Witgen.evalSteps env steps.toList }
    |>.dichotomy with hb | hb <;> simp [hb, readCell, circuit_norm]

/-- The running-sum expression at round `iter`: `z_next = 2·z_cur + k`, unrolled over the entering
`z`. -/
def zWitExpr (z : FExpr Fp) (ebits : ℕ → BExpr Fp) : ℕ → FExpr Fp
  | 0 => .add (.mul (.const 2) z) (.ite (ebits 0) (.const 1) (.const 0))
  | i + 1 => .add (.mul (.const 2) (zWitExpr z ebits i))
      (.ite (ebits (i + 1)) (.const 1) (.const 0))

/-- The witness-IR value of the running-sum cell `z_i` at round `iter`: `zRunValue z bits iter`
(with `zRunValue z bits 0 = 2·z + k₀`). -/
def zWit (z : AssignedCell Fp) (ebits : Witgen.MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp))
    (iter : ℕ) : WitgenIR Fp 1 :=
  Witgen.MOver.toIRScalar ((fun bs => zWitExpr (.expr z) bs iter) <$> ebits)

/-- `zWitExpr`'s prover value is `zRunValue` at the bit family's values. -/
theorem zWitExpr_eval (z : FExpr Fp) (ebits : ℕ → BExpr Fp) (iter : ℕ)
    (ctx : Witgen.CtxOver Fp (Placed ProverEnvironment Fp)) :
    Witgen.FExprOver.eval ctx (zWitExpr z ebits iter)
      = zRunValue (Witgen.FExprOver.eval ctx z) (bexprsVal ebits ctx) iter := by
  induction iter with
  | zero =>
    simp only [zWitExpr, zRunValue, Witgen.FExprOver.eval, bexprsVal]
    rcases (ebits 0).eval ctx |>.dichotomy with hb | hb <;> simp [hb]
  | succ i ih =>
    simp only [zWitExpr, zRunValue, Witgen.FExprOver.eval, bexprsVal, ih]
    rcases (ebits (i + 1)).eval ctx |>.dichotomy with hb | hb <;> simp [hb]

/-- `zWit`'s prover value: the honest running sum. -/
theorem zWit_eval (z : AssignedCell Fp)
    (ebits : Witgen.MOver Fp (AssignedCell Fp) (ℕ → BExpr Fp)) (iter : ℕ)
    (env : Placed ProverEnvironment Fp) (hi : 0 < 1) :
    ((zWit z ebits iter).eval env)[0]
      = zRunValue (readCell env z) (ebitsVal ebits env) iter := by
  rcases h : ebits #[] with ⟨bs, steps⟩
  have hz := zWitExpr_eval (.expr z) bs iter
    { env, locals := Witgen.evalSteps env steps.toList }
  simp only [zWit, Witgen.MOver.toIRScalar, Witgen.MOver.toIR,
    h, Witgen.WitgenIROver.eval,
    Witgen.VExprOver.eval, circuit_norm, hz]
  have hbv : ebitsVal ebits env
      = bexprsVal bs { env, locals := Witgen.evalSteps env steps.toList } := by
    funext i
    simp only [ebitsVal, bexprsVal, Witgen.MOver.evalBool, h]
  rw [hbv]
  simp only [readCell, AssignedCell.eval]

/-- The honest running-sum step, in the `RoundInvariant` shape. -/
private theorem zRunValue_step (z : Fp) (bits : BitsHint) (j : ℕ) :
    zRunValue z bits j
      = 2 * (if j = 0 then z else zRunValue z bits (j - 1)) + (if bits j then 1 else 0) := by
  rcases j with _ | j'
  · simp [zRunValue]
  · simp [zRunValue]

/-! ## The bundled round

One complete-addition round. The base row is the call's `offset` (round `iter` of the loop calls
at `offset + 2·iter`). Emits: the running-sum cell `z_i` (at `offset + 2`), the base_y copy (at
`offset + 1`) and the `q_mul_decompose_var` enable (at `offset + 1`), the conditionally-negated
`y_p` (at `offset`, on `add.yP`), and the TWO `add.call`s — `U + acc` at `offset`,
`acc' = acc + tmp` at `offset + 1`. The output is the stepped accumulator (the second `add`'s
output point) together with this round's running-sum cell.

The gate's third read — the *previous* running sum at the base row — is a positional
neighborhood cell this round does not own; it is published as the `extract` witness, and the
`Spec` states the z-step over it. -/

structure RoundInputs (F : Type) where
  -- Scalar reading program (prover hint); the round derives its bit from it.
  alpha : Unconstrained field F
  -- The base point.
  base : Point F
  -- The entering running sum (the cell copied in before round 0).
  z : F
  -- The entering accumulator (the previous round's output point).
  acc : Point F
deriving CircuitType

structure RoundOutput (F : Type) where
  -- The stepped accumulator.
  acc : Point F
  -- This round's running-sum cell `z_i`.
  z : F
deriving ProvableStruct

def round (w iter : ℕ) : FormalRegionCircuit Fp Config Config RoundInputs RoundOutput where
  configure := pure

  synthesize cfg offset (input : Var RoundInputs Fp) := do
    let ebits := kBitWindowProg input.alpha w
    -- running-sum cell z_i at offset + 2
    let _z ← assignAdvice cfg.zComplete (offset + 2) (zWit input.z ebits iter)
    -- base_y copied into z_complete at offset + 1 (for the decomposition gate's `base_y` read)
    let _baseY ← copyAdvice input.base.y cfg.zComplete (offset + 1)
    -- conditionally-negated y_p, assigned on add.yP at offset
    let yP ← assignAdvice cfg.addConfig.yP offset (yPWit input.base.y ebits iter)
    -- the q_mul_decompose_var gate at the middle row offset + 1
    (decomposeGate cfg).enable (offset + 1)
    -- tmp = U + acc, U = (base.x, y_p)
    let tmp ← Add.add.call cfg.addConfig offset ⟨{ x := input.base.x, y := yP }, input.acc⟩
    -- acc' = acc + tmp
    let acc' ← Add.add.call cfg.addConfig (offset + 1) ⟨input.acc, tmp⟩
    let zOut ← cellAt cfg.zComplete (offset + 2)
    return { acc := acc', z := zOut }

  -- the intended output representation: the second `add.call`'s output point plus this
  -- round's running-sum cell. `derive_contract_bridges` reads it off into `round_output`.
  elaborated cfg offset :=
    { output := fun input self =>
        { acc := (Add.add.call cfg.addConfig (offset + 1)
            { p := input.acc,
              q := (Add.add.call cfg.addConfig offset
                { p := { x := input.base.x, y := AssignedCell.of self offset cfg.addConfig.yP },
                  q := input.acc }).output self }).output self,
          z := AssignedCell.of self (offset + 2) cfg.zComplete }
      output_eq := by intro _ _; rfl }

  -- acc, base are valid Pallas points (complete addition is exceptional-case-free).
  Assumptions input := input.acc.Valid ∧ input.base.Valid

  -- the previous running-sum cell at the base row: a positional neighborhood read.
  Witness := field
  extract cfg offset _ self env :=
    AssignedCell.eval env.place env.env (.of self offset cfg.zComplete)

  -- Some bit (forced by the decomposition gate) steps the z-chain over the neighborhood
  -- cell, and the output accumulator is the complete double-and-add step by it.
  Spec input out zPrev :=
    ∃ b : Bool,
      out.z = 2 * zPrev + (if b then 1 else 0) ∧
      out.acc = stepPoint input.base input.acc b ∧
      out.acc.Valid

  -- honest neighborhood: the previous cell carries the honest running sum.
  ProverAssumptions input zPrev _ :=
    zPrev = (if iter = 0 then input.z
             else zRunValue input.z (kBitsWindow input.alpha w) (iter - 1))

  ProverSpec input out zPrev _ :=
    out.acc = stepPoint input.base input.acc (kBitsWindow input.alpha w iter) ∧
    out.z = zRunValue input.z (kBitsWindow input.alpha w) iter

  soundness := by
    circuit_proof_start2 [decomposeGate, Add.add]
    obtain ⟨hAccV, hBaseV⟩ := assumptions
    -- fold the elaborated output spelling onto the peel's atoms
    rw [tmp_eq, acc'_eq] at output_eq
    obtain ⟨hAccOut, -⟩ := output_eq
    obtain ⟨hbool, hswitch⟩ := region_1
    rw [region_0] at hswitch
    set zP := env.advice cfg.zComplete ((place self + offset : ℕ) : ℤ) with hzP
    set yPv := env.advice cfg.addConfig.yP ((place self + offset : ℕ) : ℤ) with hyPv
    -- ── the constraint-forced bit + conditionally-negated y_p ──
    have hb : (output_z = 2 * zP ∧ yPv = -input_base_y)
        ∨ (output_z = 2 * zP + 1 ∧ yPv = input_base_y) := by
      rcases mul_eq_zero.mp hbool with hk | hk
      · exact Or.inl ⟨by linear_combination hk,
          by linear_combination hswitch + 2 * yPv * hk⟩
      · exact Or.inr ⟨by linear_combination -hk,
          by linear_combination -hswitch + 2 * yPv * hk⟩
    -- ── consume the two child contracts, threading tmp.Valid into the second ──
    rcases hb with ⟨hzeq, hyeq⟩ | ⟨hzeq, hyeq⟩
    · -- bit 0: U = (base.x, −base.y)
      rw [hyeq] at tmp_spec
      have hUv : ({ x := input_base_x, y := -input_base_y } : Point Fp).Valid := by
        simpa [stepBasePoint] using stepBasePoint_valid hBaseV false
      obtain ⟨hV1, hE1⟩ := tmp_spec ⟨hUv, hAccV⟩
      rw [hE1] at acc'_spec
      obtain ⟨hV2, hE2⟩ := acc'_spec ⟨hAccV, Point.valid_add hUv hAccV⟩
      rw [hAccOut] at hV2 hE2
      refine ⟨false, by simpa using hzeq, ?_, hV2⟩
      rw [hE2]
      simp [stepPoint, stepBasePoint]
    · -- bit 1: U = (base.x, base.y)
      rw [hyeq] at tmp_spec
      have hUv : ({ x := input_base_x, y := input_base_y } : Point Fp).Valid := by
        simpa [stepBasePoint] using stepBasePoint_valid hBaseV true
      obtain ⟨hV1, hE1⟩ := tmp_spec ⟨hUv, hAccV⟩
      rw [hE1] at acc'_spec
      obtain ⟨hV2, hE2⟩ := acc'_spec ⟨hAccV, Point.valid_add hUv hAccV⟩
      rw [hAccOut] at hV2 hE2
      refine ⟨true, by simpa using hzeq, ?_, hV2⟩
      rw [hE2]
      simp [stepPoint, stepBasePoint]
  completeness := by
    circuit_proof_start2 [decomposeGate, Add.add, zWit_eval, yPWit_eval,
      ebitsVal_kBitWindowProg, readCell]
    obtain ⟨hAccV, hBaseV⟩ := assumptions
    have hzPrev := prover_assumptions
    -- fold the elaborated output spelling onto the peel's atoms
    rw [tmp_eq, acc'_eq] at output_eq
    obtain ⟨hAccOut, -⟩ := output_eq
    -- land the honest witness values in the goal, then split on the round's bit
    rw [region_0, region_1, hzPrev, zRunValue_step input_z (kBitsWindow input_alpha w) iter]
    rcases Bool.dichotomy (kBitsWindow input_alpha w iter) with hb | hb <;>
      rw [hb] at region_2 ⊢ <;>
      simp only [if_false, Bool.false_eq_true, if_true] at region_2 <;>
      rw [region_2] at tmp_spec ⊢
    · -- bit 0: U = (base.x, −base.y)
      have hUv : ({ x := input_base_x, y := -input_base_y } : Point Fp).Valid := by
        simpa [stepBasePoint] using stepBasePoint_valid hBaseV false
      obtain ⟨hTmpV, hTmpE⟩ := tmp_spec ⟨hUv, hAccV⟩
      obtain ⟨hAccV', hAccE⟩ := acc'_spec ⟨hAccV, hTmpV⟩
      refine ⟨⟨rfl, ⟨by simp, by simp⟩, ⟨hUv, hAccV⟩, hAccV, hTmpV⟩, ?_, rfl⟩
      rw [← hAccOut, hAccE, hTmpE]
      simp [stepPoint, stepBasePoint]
    · -- bit 1: U = (base.x, base.y)
      have hUv : ({ x := input_base_x, y := input_base_y } : Point Fp).Valid := by
        simpa [stepBasePoint] using stepBasePoint_valid hBaseV true
      obtain ⟨hTmpV, hTmpE⟩ := tmp_spec ⟨hUv, hAccV⟩
      obtain ⟨hAccV', hAccE⟩ := acc'_spec ⟨hAccV, hTmpV⟩
      refine ⟨⟨rfl, ⟨by simp, by simp⟩, ⟨hUv, hAccV⟩, hAccV, hTmpV⟩, ?_, rfl⟩
      rw [← hAccOut, hAccE, hTmpE]
      simp [stepPoint, stepBasePoint]

/-- Name a whole vector of `z` cells at fixed region-local rows, emitting no op — the running-sum
`Output.zs` cells. (`MulIncomplete.cellVec`, inlined; the round-`iter` `z_i` cell is at
`offset + 2·iter + 2`.) -/
def zsCells (cfg : Config) (offset : ℕ) (numBits : ℕ) :
    RegionCircuit Fp (Vector (AssignedCell Fp) numBits) :=
  fun self => (Vector.ofFn (fun i => AssignedCell.of self (offset + 2 * i.val + 2) cfg.zComplete), [])

@[circuit_norm]
theorem operations_zsCells (cfg : Config) (offset numBits : ℕ) (self : RegionIndex) :
    (zsCells cfg offset numBits).operations self = [] := rfl

@[circuit_norm]
theorem output_zsCells (cfg : Config) (offset numBits : ℕ) (self : RegionIndex) :
    (zsCells cfg offset numBits).output self
      = Vector.ofFn (fun i => AssignedCell.of self (offset + 2 * i.val + 2) cfg.zComplete) := rfl

/-! ## Contract-projection bridges

Expose the child's contract fields (`Add.add.Spec` etc.) while keeping its synthesize body folded.
Generated by `derive_contract_bridges`. -/

derive_contract_bridges add := Add.add
derive_contract_bridges round (w iter : ℕ) := round w iter

/-- **Fold soundness.** From the per-round contracts — each producing a constraint-forced
bit, the z-step over adjacent cells, and the complete step on the accumulator — some bit
sequence steps the whole chain and the accumulator lands on `accPoint`, valid throughout.
Value-level: `acc`/`zread` are the evaluated accumulator/running-sum families. -/
theorem fold_sound {base A0 : Point Fp} (hA0 : A0.Valid) (hbase : base.Valid)
    (acc : ℕ → Point Fp) (zread : ℕ → Fp) (hacc0 : acc 0 = A0) (n : ℕ)
    (hround : ∀ i : Fin n, (acc i.val).Valid ∧ base.Valid →
      ∃ b : Bool,
        zread (i.val + 1) = 2 * zread i.val + (if b then 1 else 0) ∧
        acc (i.val + 1) = stepPoint base (acc i.val) b ∧
        (acc (i.val + 1)).Valid) :
    ∃ bits' : BitsHint,
      (∀ j, j < n → zread (j + 1) = 2 * zread j + (if bits' j then 1 else 0)) ∧
      acc n = accPoint base A0 bits' n ∧ (accPoint base A0 bits' n).Valid := by
  induction n with
  | zero =>
    exact ⟨fun _ => false, fun j hj => absurd hj (by omega), hacc0, hacc0 ▸ hA0⟩
  | succ k ih =>
    obtain ⟨bits', hchain, hout, hvalid⟩ := ih (fun i hpre => hround ⟨i.val, by omega⟩ hpre)
    obtain ⟨b, hstep, houtr, hvalidr⟩ := hround ⟨k, by omega⟩ ⟨hout.symm ▸ hvalid, hbase⟩
    dsimp only [] at hstep houtr hvalidr
    have hacc_succ : accPoint base A0 (fun j => if j = k then b else bits' j) (k + 1)
        = stepPoint base (accPoint base A0 bits' k) b := by
      simp only [accPoint]
      rw [accPoint_congr k (fun j hj => (if_neg (by omega : j ≠ k)))]
      simp
    refine ⟨fun j => if j = k then b else bits' j, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · simpa only [if_neg (Nat.ne_of_lt hj')] using hchain j hj'
      · simpa only [if_pos rfl] using hstep
    · rw [houtr, hout, hacc_succ]
    · rw [hacc_succ, ← hout]
      rw [houtr] at hvalidr
      exact hvalidr

/-- The two eval flavors agree on a cell-valued point (both are the advice reads). -/
theorem point_eval_toEnvironment (place : RegionIndex → ℕ) (env : ProverEnvironment Fp)
    (v : Point (AssignedCell Fp)) :
    eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp) v
      = eval (⟨place, env⟩ : Placed ProverEnvironment Fp) v := by
  rcases v with ⟨x, y⟩
  simp [circuit_norm]

/-- **Fold completeness.** From the honest per-round contracts — each turning the honest
neighborhood into its round's constraints and pinning the outputs to the honest values —
every round's constraints hold, the accumulator lands on `accPoint`, and every
running-sum cell carries the honest running sum. `C` abstracts the per-round
constraints predicate; `acc`/`zread` are the evaluated accumulator/running-sum
families. -/
theorem fold_complete {base A0 : Point Fp} (hA0 : A0.Valid) (hbase : base.Valid)
    (bits : BitsHint) (z0 : Fp) (C : ℕ → Prop)
    (acc : ℕ → Point Fp) (zread : ℕ → Fp) (hacc0 : acc 0 = A0) (hz0 : zread 0 = z0)
    (n : ℕ)
    (hround : ∀ i : Fin n,
      ((acc i.val).Valid ∧ base.Valid ∧
        zread i.val = (if i.val = 0 then z0 else zRunValue z0 bits (i.val - 1))) →
      C i.val ∧ acc (i.val + 1) = stepPoint base (acc i.val) (bits i.val) ∧
        zread (i.val + 1) = zRunValue z0 bits i.val) :
    (∀ i : Fin n, C i.val) ∧ acc n = accPoint base A0 bits n ∧
      ∀ j, j < n → zread (j + 1) = zRunValue z0 bits j := by
  induction n with
  | zero => exact ⟨fun i => i.elim0, hacc0, fun j hj => absurd hj (by omega)⟩
  | succ k ih =>
    obtain ⟨hC, hacck, hzk⟩ := ih (fun i hpre => hround ⟨i.val, by omega⟩ hpre)
    have hpre : (acc k).Valid ∧ base.Valid ∧
        zread k = (if k = 0 then z0 else zRunValue z0 bits (k - 1)) := by
      refine ⟨by rw [hacck]; exact accPoint_valid hbase hA0 bits k, hbase, ?_⟩
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simpa using hz0
      · rw [if_neg (by omega), show k = (k - 1) + 1 from by omega]
        exact hzk (k - 1) (by omega)
    obtain ⟨hCk, hacc_succ, hz_succ⟩ := hround ⟨k, by omega⟩ hpre
    dsimp only [] at hCk hacc_succ hz_succ
    refine ⟨?_, ?_, ?_⟩
    · intro i
      rcases Nat.lt_succ_iff_lt_or_eq.mp i.isLt with hi | hi
      · exact hC ⟨i.val, hi⟩
      · rw [hi]
        exact hCk
    · rw [hacc_succ, hacck]
      rfl
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hzk j hj'
      · exact hz_succ

/-! ## The bundle contract -/

/-- The complete-rounds invariant: the running-sum chain over `numBits` bits, and — for a valid
entering accumulator and base — the output accumulator equals `accPoint … numBits`, valid
throughout. -/
def RoundInvariant (numBits : ℕ) (z xA yA : Fp) (base : Point Fp)
    (output : Output numBits Fp) (bits : BitsHint) : Prop :=
  (∀ b : Fin numBits, output.zs[b.val]
      = 2 * (if b.val = 0 then z else output.zs[b.val - 1]'(by have := b.isLt; omega))
        + (if bits b.val then 1 else 0)) ∧
  (({ x := xA, y := yA } : Point Fp).Valid → base.Valid →
    output.acc.Valid
      ∧ output.acc = accPoint base { x := xA, y := yA } bits numBits)

/-! ## The gadget bundle

`assign_region` over the three complete bits, generalized to `numBits`. Parameterized by the window
offset `w` (this phase's first bit, 251 in `mul.rs`); the witness closures derive each round's bit
from `input.alpha`. The verifier-facing `Spec` existentially quantifies a matching bit sequence. -/

/-- The `z` copy emitted before the loop: the entering running sum into `cfg.zComplete` at
`offset`. -/
def startCopy (cfg : Config) (input : Var Inputs Fp) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  let _z ← copyAdvice input.z cfg.zComplete offset
  return ()

def assign_region (numBits : ℕ) (w : ℕ) :
    FormalRegionCircuit Fp (Column .advice × Add.Config) Config Inputs (Output numBits) where
  configure := fun (zComplete, addConfig) => configure zComplete addConfig

  synthesize cfg offset (input : Var Inputs Fp) := do
    -- copy the entering running sum
    startCopy cfg input offset
    -- the per-bit round loop: round `i` at base row `offset + 2·i`, threading the accumulator
    let accFinal ← RegionCircuit.foldRange offset 2 numBits
      ({ x := input.xA, y := input.yA } : Point (AssignedCell Fp))
      (fun i r acc => do
        let out ← (round w i).call cfg r
          { alpha := input.alpha, base := input.base, z := input.z, acc }
        pure out.acc)
    -- name the running-sum output cells (at fixed absolute rows)
    let zsOut ← zsCells cfg offset numBits
    return { acc := accFinal, zs := zsOut }

  -- the base point is a valid Pallas point (complete addition is exceptional-case-free).
  Assumptions input :=
    let base : Point Fp := input.base
    let acc0 : Point Fp := { x := input.xA, y := input.yA }
    acc0.Valid ∧ base.Valid

  Spec input output _ :=
    ∃ bits' : BitsHint,
      RoundInvariant numBits input.z input.xA input.yA input.base output bits'

  ProverAssumptions input _ _ :=
    let base : Point Fp := input.base
    let acc0 : Point Fp := { x := input.xA, y := input.yA }
    acc0.Valid ∧ base.Valid

  -- honest bits: the `w`-window of the scalar value's `kBits` — the same family the witness
  -- programs compute (no external `bits` hint).
  ProverSpec input output _ _ :=
    RoundInvariant numBits input.z input.xA input.yA input.base output
      (kBitsWindow input.alpha w)

  -- ══ Soundness ══
  -- The fold splits into the per-round `round` contracts; `fold_sound` chains them.
  soundness := by
    circuit_proof_start2 [round, round_output]
    obtain ⟨hAcc0V, hBaseV⟩ := assumptions
    obtain ⟨hOutAcc, hzs⟩ := output_eq
    -- the running-sum output cells, per index
    have h_output_zs : ∀ (j : ℕ) (hj : j < numBits),
        output_zs[j] = env.advice cfg.zComplete ((place self + (offset + 2 * j + 2) : ℕ) : ℤ) := by
      intro j hj
      rw [← hzs]
      simp [circuit_norm]
    -- the fold invariant from the per-round contracts
    obtain ⟨bits', hchain, hout, hvalid⟩ :=
      fold_sound (base := { x := input_base_x, y := input_base_y })
        (A0 := { x := input_xA, y := input_yA }) hAcc0V hBaseV
        (fun n => eval (⟨place, env⟩ : Placed Environment Fp)
          (RegionCircuit.foldAcc (fun j => offset + j * 2)
            ({ x := input_var_xA, y := input_var_yA } : Point (AssignedCell Fp))
            (fun i r acc => do
              let out ← (round w i).call cfg r
                { alpha := input_var_alpha,
                  base := { x := input_var_base_x, y := input_var_base_y },
                  z := input_var_z, acc := acc }
              pure out.acc) n self))
        (fun n => env.advice cfg.zComplete ((place self + (offset + n * 2) : ℕ) : ℤ))
        (by simp [circuit_norm, input_eq]) numBits
        (fun i hpre => by
          obtain ⟨b, h1, h2, h3⟩ := region_1 i hpre
          refine ⟨b, ?_, ?_, ?_⟩ <;> beta_reduce
          · rw [show (↑i + 1) * 2 = ↑i * 2 + 2 from by ring]
            exact h1
          · rw [RegionCircuit.foldAcc_succ]
            simp only [round_output, circuit_norm] at h2 ⊢
            exact h2
          · rw [RegionCircuit.foldAcc_succ]
            simp only [round_output, circuit_norm] at h3 ⊢
            exact h3)
    -- ── assemble `RoundInvariant` ──
    refine ⟨bits', ?_, fun _ _ => ⟨?_, ?_⟩⟩
    · -- z-chain: the fold's per-round steps, re-indexed onto the output cells
      intro b
      dsimp only []
      rw [h_output_zs b.val b.isLt]
      have hstep := hchain b.val b.isLt
      beta_reduce at hstep
      rw [show (b.val + 1) * 2 = 2 * b.val + 2 from by ring] at hstep
      rcases Nat.eq_zero_or_pos b.val with hb0 | hbpos
      · rw [if_pos hb0]
        rw [show offset + b.val * 2 = offset from by omega, region_0] at hstep
        exact hstep
      · rw [if_neg (by omega)]
        rw [h_output_zs (b.val - 1) (by have := b.isLt; omega),
          show offset + 2 * (b.val - 1) + 2 = offset + b.val * 2 from by omega]
        exact hstep
    · -- accumulator validity
      rw [show ({ x := output_acc_x, y := output_acc_y } : Point Fp)
        = accPoint { x := input_base_x, y := input_base_y } { x := input_xA, y := input_yA }
            bits' numBits from hOutAcc.symm.trans hout]
      exact hvalid
    · -- accumulator value
      exact hOutAcc.symm.trans hout

  -- ══ Completeness ══
  -- The fold's honest witnesses feed the per-round engine leaves; `fold_complete` chains them.
  completeness := by
    circuit_proof_start2 [round, round_output]
    obtain ⟨hAcc0V, hBaseV⟩ := prover_assumptions
    obtain ⟨hOutAcc, hzs⟩ := output_eq
    -- the running-sum output cells, per index
    have h_output_zs : ∀ (j : ℕ) (hj : j < numBits),
        output_zs[j] = env.advice cfg.zComplete ((place self + (offset + 2 * j + 2) : ℕ) : ℤ) := by
      intro j hj
      rw [← hzs]
      simp [circuit_norm]
    -- the per-round honest bundles (the engine strengthened the goal per round and
    -- delivered `round_spec`), chained by `fold_complete`
    obtain ⟨hCall, haccN, hzN⟩ :=
      fold_complete (base := { x := input_base_x, y := input_base_y })
        (A0 := { x := input_xA, y := input_yA }) hAcc0V hBaseV
        (kBitsWindow input_alpha w) input_z
        (fun i => ((eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
            (RegionCircuit.foldAcc (fun j => offset + j * 2)
              ({ x := input_var_xA, y := input_var_yA } : Point (AssignedCell Fp))
              (fun i r acc => do
                let out ← (round w i).call cfg r
                  { alpha := input_var_alpha,
                    base := { x := input_var_base_x, y := input_var_base_y },
                    z := input_var_z, acc := acc }
                pure out.acc) i self)).Valid ∧
            ({ x := input_base_x, y := input_base_y } : Point Fp).Valid) ∧
          env.advice cfg.zComplete ((place self + (offset + i * 2) : ℕ) : ℤ)
            = if i = 0 then input_z
              else zRunValue input_z (kBitsWindow input_alpha w) (i - 1))
        (fun n => eval (⟨place, env.toEnvironment⟩ : Placed Environment Fp)
          (RegionCircuit.foldAcc (fun j => offset + j * 2)
            ({ x := input_var_xA, y := input_var_yA } : Point (AssignedCell Fp))
            (fun i r acc => do
              let out ← (round w i).call cfg r
                { alpha := input_var_alpha,
                  base := { x := input_var_base_x, y := input_var_base_y },
                  z := input_var_z, acc := acc }
              pure out.acc) n self))
        (fun n => env.advice cfg.zComplete ((place self + (offset + n * 2) : ℕ) : ℤ))
        (by simp [circuit_norm, input_eq]) (by simpa using region_0) numBits
        (fun i hpre => by
          obtain ⟨hAV, hBV, hzP⟩ := hpre
          beta_reduce at hAV hzP
          obtain ⟨hSpec, hPSacc, hPSz⟩ := round_spec i ⟨hAV, hBV⟩ hzP
          refine ⟨⟨⟨hAV, hBV⟩, hzP⟩, ?_, ?_⟩ <;> beta_reduce
          · rw [RegionCircuit.foldAcc_succ]
            simp only [round_output, circuit_norm, ← point_eval_toEnvironment] at hPSacc ⊢
            exact hPSacc
          · rw [show (↑i + 1) * 2 = ↑i * 2 + 2 from by ring]
            exact hPSz)
    -- ── assemble: copy constraint + per-round constraints + `RoundInvariant` ──
    refine ⟨⟨region_0, fun i => hCall i⟩, ?_, fun _ _ => ⟨?_, ?_⟩⟩
    · -- z-chain on the honest values
      intro b
      have hzb := hzN b.val b.isLt
      beta_reduce at hzb
      rw [h_output_zs b.val b.isLt,
        show offset + 2 * b.val + 2 = offset + (b.val + 1) * 2 from by ring, hzb,
        zRunValue_step input_z (kBitsWindow input_alpha w) b.val]
      rcases Nat.eq_zero_or_pos b.val with hb0 | hbpos
      · rw [if_pos hb0, if_pos hb0]
      · have hzb1 := hzN (b.val - 1) (by have := b.isLt; omega)
        beta_reduce at hzb1
        rw [if_neg (show ¬(b.val = 0) by omega), if_neg (show ¬(b.val = 0) by omega),
          h_output_zs (b.val - 1) (by have := b.isLt; omega),
          show offset + 2 * (b.val - 1) + 2 = offset + (b.val - 1 + 1) * 2 from by ring, hzb1]
    · -- accumulator validity
      rw [show ({ x := output_acc_x, y := output_acc_y } : Point Fp)
        = accPoint { x := input_base_x, y := input_base_y } { x := input_xA, y := input_yA }
            (kBitsWindow input_alpha w) numBits from
        hOutAcc.symm.trans haccN]
      exact accPoint_valid hBaseV hAcc0V (kBitsWindow input_alpha w) numBits
    · -- accumulator value
      exact hOutAcc.symm.trans haccN

end Zcash.Circuits.Ecc.MulComplete
