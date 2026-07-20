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

namespace Halo2.Ironwood.Ecc.MulComplete

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc.Mul.Incomplete.DoubleAndAdd (zRunValue)
open Halo2.Ironwood.Ecc.MulIncomplete (BitsHint kBitsWindow kBitsWindow_eq_kBits)

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
def decomposeGate (cfg : Config) : Gate Fp where
  name := "Decompose scalar for complete bits of variable-base mul"
  selector := cfg.qDecompose
  constraints :=
    let zPrev : Expression Fp Query := queryAdvice cfg.zComplete (-1)   -- z_{i+1}
    let zNext : Expression Fp Query := queryAdvice cfg.zComplete 1      -- z_i
    let baseY : Expression Fp Query := queryAdvice cfg.zComplete 0      -- base_y
    let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP (-1)   -- y_p
    let k := zNext - (2 : Fp) * zPrev
    -- `k · (1 − k)`, with the `1` on the left of the subtraction to match the compiled gate AST.
    let boolCheck := k * ((1 : Fp) - k)
    let ySwitch := k * (baseY - yP) + ((1 : Fp) - k) * (baseY + yP)
    Constraints.withSelector cfg.qDecompose
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
  alpha : UnconstrainedExpr field F
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
  · simpa using Halo2.Ironwood.Point.valid_neg hbase
  · simpa using hbase

/-- Validity is preserved by a complete round (the complete group law is total on valid points). -/
theorem stepPoint_valid {base acc : Point Fp} (hbase : base.Valid) (hacc : acc.Valid)
    (bit : Bool) : (stepPoint base acc bit).Valid :=
  Halo2.Ironwood.Point.valid_add hacc
    (Halo2.Ironwood.Point.valid_add (stepBasePoint_valid hbase bit) hacc)

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

/-- The working-scalar bit programs for this phase, as witness-IR conditions on the scalar's
reading program: bit `i` is `kBitsWindow (alpha value) w i`, i.e. bit `254 − (w + i)` of
`t_q + alpha.val` — the `w`-shifted window of the working scalar's MSB-first bits (Rust
`decompose_for_scalar_mul(alpha.value())`). The `t_q + ·` spelling mirrors `kBitsWindow`'s
kernel-safe left-literal addition. The loop plumbing below is abstract in a *program-level*
bit family `ebits : ℕ → BExpr Fp` (plain witness-IR data, no environment closure); the
bundle instantiates `ebits := kBitWindowExpr input.alpha w`. -/
def kBitWindowExpr (alpha : FExpr Fp) (w i : ℕ) : BExpr Fp :=
  .neq ((Witgen.NExprOver.add (.const Mul.tQNat) (.val alpha)).testBit
    (.const (254 - (w + i)))) (.const 1)

/-- The value of a program-level bit family at a placed prover environment. -/
def ebitsVal (ebits : ℕ → BExpr Fp) (env : Placed ProverEnvironment Fp) : BitsHint :=
  fun i => (ebits i).eval { env := env }

/-- `kBitWindowExpr`'s value is `kBitsWindow` of the scalar program's value. -/
theorem ebitsVal_kBitWindowExpr (alpha : FExpr Fp) (w : ℕ)
    (env : Placed ProverEnvironment Fp) :
    ebitsVal (kBitWindowExpr alpha w) env
      = kBitsWindow (Witgen.FExprOver.eval { env := env } alpha) w := by
  funext i
  simp only [ebitsVal, kBitWindowExpr, MulIncomplete.kBitsWindow,
    Witgen.NExprOver.testBit, Witgen.BExprOver.eval, Witgen.NExprOver.eval,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  with_unfolding_all rfl

/-- The conditionally-negated `y_p` at round `iter`: `if k then base_y else −base_y`, with the
bit `k` the round's program `ebits iter`. -/
def yPWit (input : Var Inputs Fp) (ebits : ℕ → BExpr Fp) (iter : ℕ) : WitgenIR Fp 1 :=
  .ofFExpr (.ite (ebits iter) (.expr input.base.y) (Witgen.FExprOver.neg (.expr input.base.y)))

/-- `yPWit`'s prover value: `±base_y` by the round's bit value. -/
theorem yPWit_eval (input : Var Inputs Fp) (ebits : ℕ → BExpr Fp) (iter : ℕ)
    (env : Placed ProverEnvironment Fp) (hi : 0 < 1) :
    ((yPWit input ebits iter).eval env)[0]
      = if ebitsVal ebits env iter then readCell env input.base.y
        else -(readCell env input.base.y) := by
  simp only [yPWit, Witgen.WitgenIROver.getElem_eval_ofFExpr, Witgen.FExprOver.eval,
    Witgen.FExprOver.neg, ebitsVal]
  rcases (ebits iter).eval { env := env } |>.dichotomy with hb | hb <;>
    simp [hb, readCell, circuit_norm]

/-- The running-sum program at round `iter`: `z_next = 2·z_cur + k`, unrolled over the entering
`z`. -/
def zWitExpr (z : FExpr Fp) (ebits : ℕ → BExpr Fp) : ℕ → FExpr Fp
  | 0 => .add (.mul (.const 2) z) (.ite (ebits 0) (.const 1) (.const 0))
  | i + 1 => .add (.mul (.const 2) (zWitExpr z ebits i))
      (.ite (ebits (i + 1)) (.const 1) (.const 0))

/-- The witness-IR value of the running-sum cell `z_i` at round `iter`: `zRunValue z bits iter`
(with `zRunValue z bits 0 = 2·z + k₀`). -/
def zWit (input : Var Inputs Fp) (ebits : ℕ → BExpr Fp) (iter : ℕ) : WitgenIR Fp 1 :=
  .ofFExpr (zWitExpr (.expr input.z) ebits iter)

/-- `zWitExpr`'s prover value is `zRunValue` at the bit family's values. -/
theorem zWitExpr_eval (z : FExpr Fp) (ebits : ℕ → BExpr Fp) (iter : ℕ)
    (env : Placed ProverEnvironment Fp) :
    Witgen.FExprOver.eval { env := env } (zWitExpr z ebits iter)
      = zRunValue (Witgen.FExprOver.eval { env := env } z) (ebitsVal ebits env) iter := by
  induction iter with
  | zero =>
    simp only [zWitExpr, zRunValue, Witgen.FExprOver.eval, ebitsVal]
    rcases (ebits 0).eval { env := env } |>.dichotomy with hb | hb <;> simp [hb]
  | succ i ih =>
    simp only [zWitExpr, zRunValue, Witgen.FExprOver.eval, ebitsVal, ih]
    rcases (ebits (i + 1)).eval { env := env } |>.dichotomy with hb | hb <;> simp [hb]

/-- `zWit`'s prover value: the honest running sum. -/
theorem zWit_eval (input : Var Inputs Fp) (ebits : ℕ → BExpr Fp) (iter : ℕ)
    (env : Placed ProverEnvironment Fp) (hi : 0 < 1) :
    ((zWit input ebits iter).eval env)[0]
      = zRunValue (readCell env input.z) (ebitsVal ebits env) iter := by
  simp only [zWit, Witgen.WitgenIROver.getElem_eval_ofFExpr, zWitExpr_eval]
  rfl

/-- One complete-addition round at loop index `iter`, at absolute rows relative to `offset`. The
base row is `r = offset + 2·iter`. Emits: the running-sum cell `z_i` (at `r + 2`), the base_y copy
(at `r + 1`) and the `q_mul_decompose_var` enable (at `r + 1`), the conditionally-negated `y_p`
(at `r`, on `add.yP`), and the TWO `add.call`s — `U + acc` at offset `r`, `acc' = acc + tmp` at
offset `r + 1`. Returns the round's output accumulator cells (the second `add`'s output point).

The accumulator flows through the return value: `acc` is the previous round's output point (cells).
The first round's `acc` is the entering `(input.xA, input.yA)`; `cellAt`-style naming is not needed
because the child `add.call` returns the fresh R cells directly. -/
def round (cfg : Config) (input : Var Inputs Fp) (ebits : ℕ → BExpr Fp)
    (offset iter : ℕ) (acc : Point (AssignedCell Fp)) :
    RegionCircuit Fp (Point (AssignedCell Fp)) := do
  let r := offset + 2 * iter
  -- running-sum cell z_i at r + 2
  let _z ← assignAdvice cfg.zComplete (r + 2) (zWit input ebits iter)
  -- base_y copied into z_complete at r + 1 (for the decomposition gate's `base_y` read)
  let _baseY ← copyAdvice input.base.y cfg.zComplete (r + 1)
  -- conditionally-negated y_p, assigned on add.yP at r
  let yP ← assignAdvice cfg.addConfig.yP r (yPWit input ebits iter)
  -- the q_mul_decompose_var gate at the middle row r + 1
  (decomposeGate cfg).enable (r + 1)
  -- U = (base.x, y_p)
  let U : Point (AssignedCell Fp) := { x := input.base.x, y := yP }
  -- tmp = U + acc, at add-offset r
  let tmp ← Add.add.call cfg.addConfig r ⟨U, acc⟩
  -- acc' = acc + tmp, at add-offset r + 1
  let acc' ← Add.add.call cfg.addConfig (r + 1) ⟨acc, tmp⟩
  return acc'

/-- The complete-addition loop: `numRounds` rounds, structurally recursive, threading the
accumulator point through. By the append-bind of `RegionCircuit`,
`(loop … (k+1)).operations self = (loop … k).operations self ++ (round … k accₖ).operations self`
— the per-round decomposition the induction consumes. The return value is the final accumulator. -/
def loop (cfg : Config) (input : Var Inputs Fp) (ebits : ℕ → BExpr Fp) (offset : ℕ) :
    ℕ → RegionCircuit Fp (Point (AssignedCell Fp))
  | 0 => pure { x := input.xA, y := input.yA }
  | k + 1 => do
    let acc ← loop cfg input ebits offset k
    round cfg input ebits offset k acc

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

/-- Per-round operations decomposition (holds by `rfl` via the monad's `operations_bind`), the
crux that makes the loop inductable. Mirrors `MulIncomplete.loop_operations_succ`, but note the
accumulator threads through the *value* of the previous loop stage, so the round's ops depend on
`(loop … k).output self`. -/
theorem loop_operations_succ (cfg : Config) (input : Var Inputs Fp)
    (ebits : ℕ → BExpr Fp) (offset k : ℕ) (self : RegionIndex) :
    (loop cfg input ebits offset (k + 1)).operations self
      = (loop cfg input ebits offset k).operations self
        ++ (round cfg input ebits offset k ((loop cfg input ebits offset k).output self)).operations self := by
  simp only [loop, RegionCircuit.operations_bind]

theorem loop_output_succ (cfg : Config) (input : Var Inputs Fp)
    (ebits : ℕ → BExpr Fp) (offset k : ℕ) (self : RegionIndex) :
    (loop cfg input ebits offset (k + 1)).output self
      = (round cfg input ebits offset k ((loop cfg input ebits offset k).output self)).output self := by
  simp only [loop, RegionCircuit.output_bind]

/-! ## Contract-projection bridges

Expose the child's contract fields (`Add.add.Spec` etc.) while keeping its synthesize body folded.
Generated by `derive_contract_bridges`. -/

derive_contract_bridges add := Add.add

/-- Componentwise eval of the child's input struct. Only fires on locally-stated equations (see
`round_complete`); the soundness path normalizes spellings via `provable_type_simp` instead. -/
private theorem addInputs_eval_eq (env : Placed Environment Fp)
    (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : Add.Inputs (AssignedCell Fp)) = { p := eval env p, q := eval env q } := by
  simp only [circuit_norm, ProvableType.eval_cells]

/-! ## Per-round composition lemma

The per-round core the loop induction invokes: one round with its two chained `add` calls,
output-of-first threaded into the precondition of the second. Soundness produces the round's
constraint-forced bit `b` (read off the running-sum cells by the decomposition gate), so bundle
soundness does not depend on the derived witness bit family. -/

/-- One round's soundness. If the round's constraints hold, the entering accumulator `acc` reads
a valid point `A`, and the base is valid, then there is a bit `b` (forced by the decomposition
gate on the running-sum cells) such that the z-chain steps by `b` and the round's output point
is the complete `stepPoint base A b` — via the two `add.call` chunks. -/
theorem round_acc_sound (cfg : Config) (input : Var Inputs Fp)
    (ebits : ℕ → BExpr Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset iter : ℕ)
    (acc : Point (AssignedCell Fp)) (A base : Point Fp)
    (hAvalid : A.Valid) (hbase : base.Valid)
    (hAcc : eval (⟨place, env⟩ : Placed Environment Fp) acc = A)
    (hBaseX : eval (⟨place, env⟩ : Placed Environment Fp) input.base.x = base.x)
    (hBaseY : eval (⟨place, env⟩ : Placed Environment Fp) input.base.y = base.y)
    (hC : RegionOperations.Constraints place self env
      ((round cfg input ebits offset iter acc).operations self)) :
    ∃ b : Bool,
      env.advice cfg.zComplete ((place self + (offset + 2 * iter + 2) : ℕ) : ℤ)
        = 2 * env.advice cfg.zComplete ((place self + (offset + 2 * iter) : ℕ) : ℤ)
          + (if b then 1 else 0)
      ∧ eval (⟨place, env⟩ : Placed Environment Fp)
          ((round cfg input ebits offset iter acc).output self) = stepPoint base A b
      ∧ (stepPoint base A b).Valid := by
  -- peel the round's own ops around the two folded `add.call` chunks
  simp only [round, circuit_norm,
    RegionCircuit.operations_bind, RegionCircuit.output_bind,
    operations_assignAdvice, operations_copyAdvice, operations_enable,
    RegionOperations.constraints_append] at hC ⊢
  obtain ⟨hz, hdec, hC1, hC2⟩ := hC
  -- ▸▸ engine site 1 (first add: `tmp = U + acc` at row r): weakens the folded chunk to
  --    the child's `EnvA → A → Spec` implication ◂◂
  subcircuit_rw at hC1
  -- ▸▸ engine site 2 (second add: `acc' = acc + tmp` at row r+1) ◂◂
  subcircuit_rw at hC2
  -- expose the child's contract projections (the child stays folded)
  simp only [add_spec_eq, add_assumptions_eq, add_envAssumptions_eq] at hC1 hC2
  rename' hC1 => hSpec1, hC2 => hSpec2
  -- ── the decomposition gate: reduce to the two value-level polynomials ──
  -- (`circuit_norm` folds the ±1 rotations into the ℕ-sum row spelling directly)
  simp only [decomposeGate, Constraints.withSelector, circuit_norm] at hdec
  obtain ⟨hbool, hswitch⟩ := hdec
  -- normalize every provable-type eval to the shared normal form (destructures input/acc/A/base
  -- into coordinates; the folded `Add.add.output` evals stay atoms)
  provable_type_simp
  -- ▸▸ make every child-add output opaque: the goal's output, both Specs' outputs, and the FIRST
  --    add's output threaded into the SECOND's input all become `x_gen_out_0`/`x_gen_out_1` locals
  --    (with `h_gen_out_0`/`h_gen_out_1 : <output> = x_gen_out_i`). Replaces the hand-rolled
  --    `hout1`/`hout2` rfl bridges + the `call.output → output` alignments. ◂◂
  abstract_outputs
  obtain ⟨hAx, hAy⟩ := hAcc
  -- the copied base_y cell: copy constraint + input eval (now in the same normal form)
  have hzy : env.advice cfg.zComplete ((place self + (offset + 2 * iter + 1) : ℕ) : ℤ)
      = base_y := hz.trans hBaseY
  rw [hzy] at hswitch
  -- name the three cell reads (abstracts them in the gate facts, the Specs, and the goal)
  set zP := env.advice cfg.zComplete ((place self + (offset + 2 * iter) : ℕ) : ℤ) with hzP
  set zN := env.advice cfg.zComplete ((place self + (offset + 2 * iter + 2) : ℕ) : ℤ) with hzN
  set yPv := env.advice cfg.addConfig.yP ((place self + (offset + 2 * iter) : ℕ) : ℤ) with hyPv
  -- land the child Specs' input coordinates on the abstract values
  simp only [hAx, hAy, hBaseX] at hSpec1 hSpec2
  -- ── the constraint-forced bit + conditionally-negated y_p ──
  have hb : (zN = 2 * zP ∧ yPv = -base_y) ∨ (zN = 2 * zP + 1 ∧ yPv = base_y) := by
    rcases mul_eq_zero.mp hbool with hk | hk
    · exact Or.inl ⟨by linear_combination hk,
        by linear_combination hswitch + 2 * yPv * hk⟩
    · -- `bool_check = k·(1−k)`, so the second factor is now `1 − k` (was `k − 1`): flip signs.
      exact Or.inr ⟨by linear_combination -hk,
        by linear_combination -hswitch + 2 * yPv * hk⟩
  -- ── consume the two child Specs, threading tmp.Valid into add 2's precondition ──
  rcases hb with ⟨hzeq, hyeq⟩ | ⟨hzeq, hyeq⟩
  · -- bit 0: U = (base.x, −base.y)
    refine ⟨false, by simpa using hzeq, ?_, stepPoint_valid hbase hAvalid false⟩
    rw [hyeq] at hSpec1
    have hUv : ({ x := base_x, y := -base_y } : Point Fp).Valid := by
      simpa [stepBasePoint] using stepBasePoint_valid hbase false
    obtain ⟨hV1, hE1⟩ := hSpec1 trivial ⟨hUv, hAvalid⟩
    rw [hE1] at hSpec2
    obtain ⟨hV2, hE2⟩ := hSpec2 trivial ⟨hAvalid, Halo2.Ironwood.Point.valid_add hUv hAvalid⟩
    rw [hE2]
    simp [stepPoint, stepBasePoint]
  · -- bit 1: U = (base.x, base.y)
    refine ⟨true, by simpa using hzeq, ?_, stepPoint_valid hbase hAvalid true⟩
    rw [hyeq] at hSpec1
    have hUv : ({ x := base_x, y := base_y } : Point Fp).Valid := by
      simpa [stepBasePoint] using stepBasePoint_valid hbase true
    obtain ⟨hV1, hE1⟩ := hSpec1 trivial ⟨hUv, hAvalid⟩
    rw [hE1] at hSpec2
    obtain ⟨hV2, hE2⟩ := hSpec2 trivial ⟨hAvalid, Halo2.Ironwood.Point.valid_add hUv hAvalid⟩
    rw [hE2]
    simp [stepPoint, stepBasePoint]

/-- **Loop soundness.** Under the loop's constraints, there is a bit sequence (forced round by
round by the decomposition gates) such that every round steps the z-chain and the loop's output
accumulator is `accPoint … n`, valid throughout — the induction consuming `round_acc_sound` per
round, with the accumulator validity threading from each round's output into the next round's
entering-accumulator assumption. -/
theorem loop_sound (cfg : Config) (input : Var Inputs Fp)
    (ebits : ℕ → BExpr Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset : ℕ)
    (A0 base : Point Fp) (hA0 : A0.Valid) (hbase : base.Valid)
    (hIxA : eval (⟨place, env⟩ : Placed Environment Fp) input.xA = A0.x)
    (hIyA : eval (⟨place, env⟩ : Placed Environment Fp) input.yA = A0.y)
    (hBaseX : eval (⟨place, env⟩ : Placed Environment Fp) input.base.x = base.x)
    (hBaseY : eval (⟨place, env⟩ : Placed Environment Fp) input.base.y = base.y)
    (n : ℕ) :
    RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n).operations self) →
    ∃ bits' : BitsHint,
      (∀ j, j < n →
        env.advice cfg.zComplete ((place self + (offset + 2 * j + 2) : ℕ) : ℤ)
          = 2 * env.advice cfg.zComplete ((place self + (offset + 2 * j) : ℕ) : ℤ)
            + (if bits' j then 1 else 0))
      ∧ eval (⟨place, env⟩ : Placed Environment Fp)
          ((loop cfg input ebits offset n).output self) = accPoint base A0 bits' n
      ∧ (accPoint base A0 bits' n).Valid := by
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => false, fun j hj => absurd hj (by omega), ?_, hA0⟩
    show eval (⟨place, env⟩ : Placed Environment Fp)
      ({ x := input.xA, y := input.yA } : Point (AssignedCell Fp)) = A0
    rw [Point.eval_eq, hIxA, hIyA]
  | succ k ih =>
    intro hC
    rw [loop_operations_succ, RegionOperations.constraints_append] at hC
    obtain ⟨hCk, hCr⟩ := hC
    obtain ⟨bits', hchain, hout, hvalid⟩ := ih hCk
    -- the previous rounds' output accumulator is valid — exactly the next round's assumption
    obtain ⟨b, hstep, houtr, hvalidr⟩ := round_acc_sound cfg input ebits place self env offset k
      _ (accPoint base A0 bits' k) base hvalid hbase hout hBaseX hBaseY hCr
    -- extend the bit sequence with round k's constraint-forced bit
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
    · rw [loop_output_succ, houtr, hacc_succ]
    · rw [hacc_succ]
      exact hvalidr

/-! ## Completeness ladder

The honest-prover side: round `k`'s add outputs feed round `k+1`'s honest values, and the first
add's output validity feeds the second add's precondition. -/

/-- The honest running-sum step, in the `RoundInvariant` shape. -/
private theorem zRunValue_step (z : Fp) (bits : BitsHint) (j : ℕ) :
    zRunValue z bits j
      = 2 * (if j = 0 then z else zRunValue z bits (j - 1)) + (if bits j then 1 else 0) := by
  rcases j with _ | j'
  · simp [zRunValue]
  · simp [zRunValue]

/-- **Round completeness.** The honest witnesses of one round satisfy its constraints (its own
decomposition gate from the honest `z`/`y_p` values; the two add chunks via the `subcircuit_rw`
engine's completeness mode), and pin the round's output to the complete `stepPoint` and the round's
`z` cell to the honest running sum. `hzPrev` threads the previous `z` cell's honest value (the
start copy for round 0, the previous round's cell otherwise). -/
theorem round_complete (cfg : Config) (input : Var Inputs Fp)
    (ebits : ℕ → BExpr Fp)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp) (offset iter : ℕ)
    (acc : Point (AssignedCell Fp)) (A base : Point Fp)
    (hAvalid : A.Valid) (hbase : base.Valid)
    (hAcc : eval env.toEnvironment acc = A)
    (hBaseX : eval env.toEnvironment input.base.x = base.x)
    (hBaseY : eval env.toEnvironment input.base.y = base.y)
    (hzPrev : env.env.advice cfg.zComplete ((env.place self + (offset + 2 * iter) : ℕ) : ℤ)
      = (if iter = 0 then readCell env input.z
          else zRunValue (readCell env input.z) (ebitsVal ebits env) (iter - 1)))
    (hW : RegionOperations.ExtendsWitnesses env.place self env.env
      ((round cfg input ebits offset iter acc).operations self)) :
    RegionOperations.Constraints env.place self env.env
      ((round cfg input ebits offset iter acc).operations self)
    ∧ eval env.toEnvironment ((round cfg input ebits offset iter acc).output self)
        = stepPoint base A (ebitsVal ebits env iter)
    ∧ env.env.advice cfg.zComplete ((env.place self + (offset + 2 * iter + 2) : ℕ) : ℤ)
        = zRunValue (readCell env input.z) (ebitsVal ebits env) iter := by
  simp only [round, circuit_norm, zWit_eval, yPWit_eval,
    RegionCircuit.operations_bind, RegionCircuit.output_bind,
    operations_assignAdvice, operations_copyAdvice, operations_enable,
    RegionOperations.extendsWitnesses_append, RegionOperations.constraints_append] at hW ⊢
  obtain ⟨hWz, hWby, hWyP, hWc1, hWc2⟩ := hW
  -- the honest base_y read, in value form
  have hby : readCell env input.base.y = base.y := by
    rw [← hBaseY]; with_unfolding_all rfl
  -- the assigned y_p cell's verifier read = its honest (prover-witnessed) value = ±base.y
  have hyPcell : eval env.toEnvironment
      (AssignedCell.of self (offset + 2 * iter) cfg.addConfig.yP : AssignedCell Fp)
      = env.env.advice cfg.addConfig.yP ((env.place self + (offset + 2 * iter) : ℕ) : ℤ) := by
    with_unfolding_all rfl
  -- ── eval landings for the two child calls (all spellings elaborated here, hence coherent) ──
  have hUeval : eval env.toEnvironment
      ({ x := input.base.x, y := AssignedCell.of self (offset + 2 * iter) cfg.addConfig.yP }
        : Point (AssignedCell Fp))
      = stepBasePoint base (ebitsVal ebits env iter) := by
    rw [Point.eval_eq, hBaseX, hyPcell, hWyP, hby]
    rcases Bool.dichotomy (ebitsVal ebits env iter) with hb | hb <;> simp [stepBasePoint, hb]
  have hIn1 : eval env.toEnvironment
      (⟨{ x := input.base.x, y := AssignedCell.of self (offset + 2 * iter) cfg.addConfig.yP },
        acc⟩ : Var Add.Inputs Fp)
      = (⟨stepBasePoint base (ebitsVal ebits env iter), A⟩ : Add.Inputs Fp) := by
    simp only [addInputs_eval_eq]
    rw [hUeval, hAcc]
  have hA1 : Add.add.Assumptions (eval env.toEnvironment
      (⟨{ x := input.base.x, y := AssignedCell.of self (offset + 2 * iter) cfg.addConfig.yP },
        acc⟩ : Var Add.Inputs Fp)) := by
    simp only [add_assumptions_eq, hIn1]
    exact ⟨stepBasePoint_valid hbase (ebitsVal ebits env iter), hAvalid⟩
  -- ▸▸ make every child-add output opaque BEFORE the engine runs: the goal's output equation and
  --    the first add's output threaded into the second add's chunk input become `x_gen_out_0`
  --    (first) / `x_gen_out_1` (second) opaque locals, with `h_gen_out_i : <output> = x_gen_out_i`.
  --    Replaces the hand-rolled `hout1`/`hout2` rfl bridges. The engine then EMITS `h_spec_i` OVER
  --    these locals (it consults the `h_gen_out_i` equations before materializing each output), so
  --    `hSpec1.2`/`hSpec2.2` speak `x_gen_out_i` directly — no post-hoc bridging needed. ◂◂
  abstract_outputs
  -- ▸▸ engine (completeness): strengthen the goal's two folded add chunks to their
  --    `EnvA ∧ A ∧ PA` preconditions (ExtendsWitnesses located from `hWc1`/`hWc2`), and introduce
  --    the premised derived statements `h_spec_0`/`h_spec_1 : EnvA → A → PA → Spec ∧ ProverSpec`. ◂◂
  subcircuit_rw
  -- derive add 1's Spec from `h_spec_0` (Add's `ProverSpec` is `True`, so `.1` is the Spec)
  have hSpec1 := (h_spec_0 trivial hA1 trivial).1
  simp only [add_spec_eq, hIn1] at hSpec1
  -- the first add's output value, on the opaque local — the engine emitted `h_spec_0` OVER
  -- `x_gen_out_0` (it found the `h_gen_out_0` abstraction equation before re-materializing the
  -- concrete output), so `hSpec1.2` already speaks the local directly.
  have hxout0 : eval env.toEnvironment x_gen_out_0
      = stepBasePoint base (ebitsVal ebits env iter) + A := hSpec1.2
  have hIn2 : eval env.toEnvironment (⟨acc, x_gen_out_0⟩ : Var Add.Inputs Fp)
      = (⟨A, stepBasePoint base (ebitsVal ebits env iter) + A⟩ : Add.Inputs Fp) := by
    simp only [addInputs_eval_eq]; rw [hAcc, hxout0]
  have hA2 : Add.add.Assumptions (eval env.toEnvironment (⟨acc, x_gen_out_0⟩ : Var Add.Inputs Fp)) := by
    simp only [add_assumptions_eq, hIn2]
    exact ⟨hAvalid, hSpec1.2 ▸ hSpec1.1⟩
  -- add 2's Spec from `h_spec_1`, its `q.Valid` threaded from the first's Spec
  have hSpec2 := (h_spec_1 trivial hA2 trivial).1
  simp only [add_spec_eq, hIn2] at hSpec2
  -- the second add's output value, on the opaque local — `h_spec_1` emitted over `x_gen_out_1`.
  have hxout1 : eval env.toEnvironment x_gen_out_1
      = A + (stepBasePoint base (ebitsVal ebits env iter) + A) := hSpec2.2
  -- ── assemble: copy constraint, gate polys, the two strengthened chunk preconditions; output
  --    value; z value. The engine turned the chunk positions into `EnvA ∧ A ∧ PA` bundles. ──
  refine ⟨⟨hWby, ?_, ⟨trivial, hA1, trivial⟩, ⟨trivial, hA2, trivial⟩⟩, ?_, ?_⟩
  · -- the decomposition gate holds on the honest values
    simp only [decomposeGate, Constraints.withSelector, circuit_norm]
    rw [hWz, hzPrev, hWby, hWyP]
    rw [show env.env.get input.base.y.cell.column
        ((env.place input.base.y.cell.regionIndex + input.base.y.cell.rowOffset : ℕ) : ℤ)
        = readCell env input.base.y from rfl]
    rw [zRunValue_step (readCell env input.z) (ebitsVal ebits env) iter]
    constructor
    · -- bool_check: `k = bit ∈ {0, 1}`
      rcases Bool.dichotomy (ebitsVal ebits env iter) with hb | hb <;> rw [hb] <;> simp
    · -- y_switch: `k = 1 ⇒ y_p = base_y`, `k = 0 ⇒ y_p = −base_y`, on the honest value
      rcases Bool.dichotomy (ebitsVal ebits env iter) with hb | hb <;> rw [hb] <;> simp
  · -- output value: the goal's output is now the opaque `x_gen_out_1`
    rw [hxout1]
    simp [stepPoint, stepBasePoint]
  · -- z cell value: the honest running sum
    exact hWz

/-- **Loop completeness.** The honest witnesses of the whole loop satisfy its constraints, pin
the output accumulator to `accPoint … n`, and pin every round's `z` cell to the honest running
sum — by induction via `round_complete`, threading each round's honest `z`-predecessor (the
start copy for round 0, the previous round's cell otherwise) and the honest accumulator. -/
theorem loop_complete (cfg : Config) (input : Var Inputs Fp)
    (ebits : ℕ → BExpr Fp)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp) (offset : ℕ)
    (A0 base : Point Fp) (hA0 : A0.Valid) (hbase : base.Valid)
    (hIxA : eval env.toEnvironment input.xA = A0.x)
    (hIyA : eval env.toEnvironment input.yA = A0.y)
    (hBaseX : eval env.toEnvironment input.base.x = base.x)
    (hBaseY : eval env.toEnvironment input.base.y = base.y)
    (hzStart : env.env.advice cfg.zComplete ((env.place self + offset : ℕ) : ℤ)
      = readCell env input.z)
    (n : ℕ) :
    RegionOperations.ExtendsWitnesses env.place self env.env
      ((loop cfg input ebits offset n).operations self) →
    RegionOperations.Constraints env.place self env.env
      ((loop cfg input ebits offset n).operations self)
    ∧ eval env.toEnvironment ((loop cfg input ebits offset n).output self)
        = accPoint base A0 (ebitsVal ebits env) n
    ∧ (∀ j, j < n →
        env.env.advice cfg.zComplete ((env.place self + (offset + 2 * j + 2) : ℕ) : ℤ)
          = zRunValue (readCell env input.z) (ebitsVal ebits env) j) := by
  induction n with
  | zero =>
    intro _
    refine ⟨trivial, ?_, fun j hj => absurd hj (by omega)⟩
    show eval env.toEnvironment ({ x := input.xA, y := input.yA } : Point (AssignedCell Fp)) = A0
    rw [Point.eval_eq, hIxA, hIyA]
  | succ k ih =>
    intro hW
    rw [loop_operations_succ, RegionOperations.extendsWitnesses_append] at hW
    obtain ⟨hWk, hWr⟩ := hW
    obtain ⟨hCk, hAcck, hZk⟩ := ih hWk
    -- the previous z cell's honest value: start copy (k = 0) or round k−1's cell (k ≥ 1)
    have hzPrev : env.env.advice cfg.zComplete ((env.place self + (offset + 2 * k) : ℕ) : ℤ)
        = (if k = 0 then readCell env input.z
            else zRunValue (readCell env input.z) (ebitsVal ebits env) (k - 1)) := by
      by_cases hk0 : k = 0
      · rw [if_pos hk0, show offset + 2 * k = offset from by omega]
        exact hzStart
      · rw [if_neg hk0, show offset + 2 * k = offset + 2 * (k - 1) + 2 from by omega]
        exact hZk (k - 1) (by omega)
    obtain ⟨hCr, hOutr, hZr⟩ := round_complete cfg input ebits self env offset k
      _ (accPoint base A0 (ebitsVal ebits env) k) base (accPoint_valid hbase hA0 (ebitsVal ebits env) k) hbase
      hAcck hBaseX hBaseY hzPrev hWr
    rw [loop_operations_succ, RegionOperations.constraints_append]
    refine ⟨⟨hCk, hCr⟩, ?_, ?_⟩
    · rw [loop_output_succ, hOutr]
      rfl
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hZk j hj'
      · exact hZr

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
    -- the per-bit round loop (bit programs derived from the scalar's reading program,
    -- `kBitWindowExpr input.alpha w`); the final accumulator is the loop's return value
    let accFinal ← loop cfg input (kBitWindowExpr input.alpha w) offset numBits
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
  -- Peel `startCopy ++ loop ++ zsCells`, then route the loop constraints into `loop_sound`
  -- (whose induction consumes each round's two child chunks via `round_acc_sound`).
  soundness := by
    circuit_proof_start [startCopy]
    -- composite gadget: `circuit_proof_start` bundled step (a) (intro + `soundness_iff` + house
    -- names) and the constraints peel; the loop's child chunks keep it composite, so the leaf-only
    -- finish (row-fact chaining + cleanup) is correctly skipped, leaving `hc`/`h_input` intact.
    obtain ⟨hCopyZ, hLoop⟩ := hc
    -- `h_input`: the scalar-program conjunct is trivial (verifier view of a hint), the base
    -- conjunct is whole-point (bridged coordinatewise below), the direct fields are cell reads
    obtain ⟨-, hib, hIxA, hIyA, hIz⟩ := h_input
    obtain ⟨hAcc0V, hBaseV⟩ := hA
    -- ── the loop invariant, by induction via `round_acc_sound` (both add chunks per round) ──
    obtain ⟨bits', hchain, hout, hvalid⟩ :=
      loop_sound cfg input_var (kBitWindowExpr input_var.alpha w) place self env offset
        { x := input_xA, y := input_yA } { x := input_base_x, y := input_base_y }
        hAcc0V hBaseV
        (by with_unfolding_all exact hIxA)
        (by with_unfolding_all exact hIyA)
        (by with_unfolding_all exact congrArg Halo2.Ironwood.Point.x hib)
        (by with_unfolding_all exact congrArg Halo2.Ironwood.Point.y hib)
        numBits hLoop
    -- ── the output components: `provable_type_simp` destructured `output` and split `h_output`
    -- component-wise into `⟨eval loop.output = ⟨acc_x, acc_y⟩, eval ⟨zs cells⟩ = output_zs⟩` (the
    -- `acc` leaf is opaque-eval-vs-Point-literal, the `zs` leaf a whole-vector eval; the pass keeps
    -- them as this conjunction). Read each off. ──
    obtain ⟨hOaccEval, hOzsEval⟩ := h_output
    have hOutAcc : (⟨output_acc_x, output_acc_y⟩ : Point Fp)
        = eval (⟨place, env⟩ : Placed Environment Fp)
          ((loop cfg input_var (kBitWindowExpr input_var.alpha w) offset numBits).output self) :=
      hOaccEval.symm
    have hOutZs : ∀ (i : ℕ) (hi : i < numBits),
        output_zs[i] = env.advice cfg.zComplete
          ((place self + (offset + 2 * i + 2) : ℕ) : ℤ) := by
      intro i hi
      have := (congrArg (fun v => v[i]'hi) hOzsEval).symm
      simpa only [circuit_norm] using this
    -- ── assemble `RoundInvariant` ──
    refine ⟨bits', ?_, fun _ _ => ⟨?_, ?_⟩⟩
    · -- z-chain: the loop's per-round steps, re-indexed onto the output cells
      intro b
      rw [hOutZs b.val b.isLt]
      have hstep := hchain b.val b.isLt
      by_cases hb0 : b.val = 0
      · rw [if_pos hb0, hstep]
        rw [show offset + 2 * b.val = offset from by omega]
        rw [hCopyZ.trans hIz]
      · rw [if_neg hb0]
        rw [hOutZs (b.val - 1) (by have := b.isLt; omega)]
        rw [show offset + 2 * (b.val - 1) + 2 = offset + 2 * b.val from by omega]
        exact hstep
    · -- accumulator validity
      rw [hOutAcc, hout]
      exact hvalid
    · -- accumulator value
      rw [hOutAcc, hout]

  -- ══ Completeness ══
  -- Peel the witness list, then route the loop witnesses into `loop_complete` (whose induction
  -- consumes each round's two child chunks via `round_complete`, which uses the `subcircuit_rw`
  -- engine's completeness mode).
  completeness := by
    circuit_proof_start [startCopy]
    -- composite gadget: the loop's child chunks keep the goal composite, so the leaf-only finish
    -- is skipped and `hwit`/`h_input`/`hPA` survive for the manual continuation below.
    obtain ⟨hWz, hWloop⟩ := hwit
    -- `h_input`: the scalar-program conjunct is its prover value, the base conjunct is
    -- whole-point (bridged coordinatewise below), the direct fields are cell reads
    obtain ⟨hIalpha, hib, hIxA, hIyA, hIz⟩ := h_input
    obtain ⟨hAcc0V, hBaseV⟩ := hPA
    -- the honest entering-z read, in value form
    have hzread : readCell (⟨place, env⟩ : Placed ProverEnvironment Fp) input_var.z
        = input_z := by
      with_unfolding_all exact hIz
    -- the honest bit sequence (`ProverSpec` target): the values of the witness bit programs
    set bits : BitsHint := kBitsWindow input_alpha w with hbitsdef
    have hbits : ebitsVal (kBitWindowExpr input_var.alpha w)
        (⟨place, env⟩ : Placed ProverEnvironment Fp) = bits := by
      rw [ebitsVal_kBitWindowExpr, hbitsdef, hIalpha]
    -- ── the loop: constraints + honest accumulator/z values, via `loop_complete` ──
    obtain ⟨hCloop, hAccOut, hZs⟩ :=
      loop_complete cfg input_var (kBitWindowExpr input_var.alpha w) self
        (⟨place, env⟩ : Placed ProverEnvironment Fp) offset
        { x := input_xA, y := input_yA } { x := input_base_x, y := input_base_y }
        hAcc0V hBaseV
        (by with_unfolding_all exact hIxA)
        (by with_unfolding_all exact hIyA)
        (by with_unfolding_all exact congrArg Halo2.Ironwood.Point.x hib)
        (by with_unfolding_all exact congrArg Halo2.Ironwood.Point.y hib)
        (by rw [hWz]; rfl)
        numBits hWloop
    rw [hbits] at hAccOut
    simp only [hbits] at hZs
    -- ── the output components: `h_output` (prover view) as the `⟨acc-eval, zs-eval⟩` conjunction ──
    obtain ⟨hOaccEval, hOzsEval⟩ := h_output
    have hOutAcc : (⟨output_acc_x, output_acc_y⟩ : Point Fp)
        = accPoint { x := input_base_x, y := input_base_y }
            { x := input_xA, y := input_yA } bits numBits :=
      hOaccEval.symm.trans hAccOut
    have hOutZs : ∀ (i : ℕ) (hi : i < numBits),
        output_zs[i] = env.advice cfg.zComplete
          ((place self + (offset + 2 * i + 2) : ℕ) : ℤ) := by
      intro i hi
      have := (congrArg (fun v => v[i]'hi) hOzsEval).symm
      simpa only [circuit_norm] using this
    -- ── assemble: copy constraint + loop constraints + `RoundInvariant` ──
    refine ⟨⟨hWz, hCloop⟩, ?_, fun _ _ => ⟨?_, ?_⟩⟩
    · -- z-chain on the honest values
      intro b
      rw [hOutZs b.val b.isLt, hZs b.val b.isLt, hzread, zRunValue_step input_z bits b.val]
      by_cases hb0 : b.val = 0
      · simp only [if_pos hb0]
      · simp only [if_neg hb0]
        rw [hOutZs (b.val - 1) (by have := b.isLt; omega),
          hZs (b.val - 1) (by have := b.isLt; omega), hzread]
    · -- accumulator validity
      rw [hOutAcc]
      exact accPoint_valid hBaseV hAcc0V bits numBits
    · -- accumulator value
      exact hOutAcc

end Halo2.Ironwood.Ecc.MulComplete
