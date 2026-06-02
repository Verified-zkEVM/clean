import Clean.Gadgets.SHA256.BitwiseOps

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^35)]

namespace Gadgets.SHA256

/-!
# Multi-operand 32-bit modular addition for SHA-256

Adds `n ≤ 8` 32-bit words (as `fields 32` bit vectors, LSB first) modulo `2^32` in a single
range reduction, exploiting that linear combinations are free in R1CS.  Instead of chaining
binary `add32` (each re-witnessing 32 output bits), we sum the operands as one free linear
combination and bit-decompose the result once, with a `cw`-bit carry.

R1CS structure (per call):
- 32 witnesses for output bits `z[0..31]`, `cw` witnesses for carry bits `c[0..cw-1]`
- 32 + `cw` boolean constraints
- 1  linear constraint: `Σ_j valueBits(op_j) = valueBits(z) + 2^32 · Σ_i 2^i · c[i]`

The carry width `cw` need only satisfy `n ≤ 2^cw` (the operand sum is `< n·2^32`, so its
quotient by `2^32` is `≤ n - 1`).  Callers pick the minimal `cw`: round adds (`n = 6, 7`)
use `cw = 3`, the schedule add (`n = 4`) uses `cw = 2`.

Soundness needs `p > 2^35` so the linear constraint lifts from `F p` to `ℕ`
(`Σ < 8·2^32 = 2^35`, using `n ≤ 8` and `2^cw ≤ 8`).  The 254-bit BN254 scalar field
satisfies this with huge margin.

This file provides the gadget definition together with its `FormalCircuit` (proved
soundness and completeness). It is used by the SHA-256 round and message schedule.
-/

-- `cw` is the carry width: the number of boolean carry bits.  The operand sum is
-- `< n · 2^32`, so its quotient by `2^32` is `≤ n - 1`; `cw` bits suffice whenever
-- `n ≤ 2^cw`.  Round adds (`n = 6, 7`) use `cw = 3`; the schedule add (`n = 4`) uses
-- `cw = 2`, saving one carry witness/constraint per call.  `2^cw ≤ 8` keeps the
-- soundness lift within the existing `p > 2^35` bound.
variable {n cw : ℕ} [NeZero cw] [hn : Fact (n ≤ 8)] [hncw : Fact (n ≤ 2^cw)] [hcw : Fact (2^cw ≤ 8)]

/-- Natural-number value of all operands summed. -/
def opsValueSum (ops : Vector (fields 32 (F p)) n) : ℕ :=
  ∑ j : Fin n, valueBits ops[j]

/-- Linear-combination expression of the operand sum (free in R1CS). -/
def sumExpr (ops : Vector (Var (fields 32) (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc (j : Fin n) => acc + fromBitsExpr ops[j]) (0 : Expression (F p))

/-- Carry expression from `cw` boolean bit variables: `Σ_i 2^i · c[i]` (LSB first). -/
def carryExpr (c : Var (fields cw) (F p)) : Expression (F p) :=
  Utils.Bits.fieldFromBitsExpr c

private def evalBitsNat (env : ProverEnvironment (F p)) (a : Var (fields 32) (F p)) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) => (env a[i]).val * 2^i.val

private def sumBitsNat (env : ProverEnvironment (F p)) (ops : Vector (Var (fields 32) (F p)) n) : ℕ :=
  ∑ j : Fin n, evalBitsNat env ops[j]

/-- Add `n` 32-bit words mod `2^32` (single reduction with a `cw`-bit carry). -/
def addMod32 (ops : Vector (Var (fields 32) (F p)) n) :
    Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    let s := (sumBitsNat env ops) % 2^32
    Vector.ofFn fun (i : Fin 32) => ((s / 2^i.val % 2 : ℕ) : F p)
  let c ← witnessVector cw fun env =>
    let s := sumBitsNat env ops
    Vector.ofFn fun (i : Fin cw) => ((s / 2^32 / 2^i.val % 2 : ℕ) : F p)
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  Circuit.forEach (Vector.finRange cw) fun i =>
    assertZero (c[i] * (c[i] - 1))
  assertZero (sumExpr ops - fromBitsExpr z - (2^32 : F p) * carryExpr c)
  return z

namespace AddMod32

-- `cw` (the carry width) is not determined by the input/output types, so this is a plain
-- `def` rather than an `instance`; `circuit` below wires it in explicitly.
def elaborated : ElaboratedCircuit (F p) (ProvableVector (fields 32) n) (fields 32) where
  main := addMod32
  localLength _ := 32 + cw
  output _ i0 := varFromOffset (fields 32) i0
  localLength_eq _ _ := by simp only [circuit_norm, addMod32, Nat.mul_zero, Nat.add_zero]; rfl
  output_eq _ _ := rfl
  subcircuitsConsistent _ _ := by simp +arith only [circuit_norm, addMod32]
  channelsLawful := by intro x n; simp +arith only [circuit_norm, addMod32]

/-- All operands are normalized (boolean bit vectors). -/
def Assumptions (ops : ProvableVector (fields 32) n (F p)) : Prop :=
  ∀ j : Fin n, Normalized ops[j]

/-- The output is the modular sum of the operands, and is normalized. -/
def Spec (ops : ProvableVector (fields 32) n (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = (opsValueSum ops) % 2^32 ∧ Normalized z

/-!
## Helper lemmas
-/

private def bitsValue {m : ℕ} (bits : Vector (F p) m) : ℕ :=
  ∑ i : Fin m, bits[i].val * 2^i.val

omit [Fact (Nat.Prime p)] h_large hn in
private lemma bitsValue_eq_valueBits (bits : Vector (F p) 32) :
    bitsValue bits = valueBits bits := rfl

private lemma sum_bool_lt_two_pow (m : ℕ) (f : Fin m → ℕ) (hf : ∀ i, f i ≤ 1) :
    ∑ i : Fin m, f i * 2^i.val < 2^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
    have ihm : ∑ i : Fin m, f (Fin.castSucc i) * 2 ^ i.val < 2 ^ m :=
      ih (f ∘ Fin.castSucc) (fun i => hf _)
    have hfm : f (Fin.last m) ≤ 1 := hf _
    have hfm_bound : f (Fin.last m) * 2 ^ m ≤ 2 ^ m := by nlinarith [Nat.two_pow_pos m]
    have h2 : 2^m + 2^m = 2^(m+1) := by ring
    omega

omit h_large in
private lemma bitsValue_lt_two_pow {m : ℕ} (bits : Vector (F p) m)
    (h : ∀ i : Fin m, bits[i] = 0 ∨ bits[i] = 1) :
    bitsValue bits < 2^m := by
  unfold bitsValue
  apply sum_bool_lt_two_pow
  intro i
  rcases h i with h0 | h1
  · simp [h0, ZMod.val_zero]
  · simp [h1, ZMod.val_one]

omit h_large in
/-- valueBits of normalized bits is < 2^32. -/
private lemma valueBits_lt_two_pow (bits : Vector (F p) 32) (h : Normalized bits) :
    valueBits bits < 2^32 := by
  rw [← bitsValue_eq_valueBits]
  exact bitsValue_lt_two_pow bits h

omit h_large hn in
private lemma fieldFromBits_eq_bitsValue {m : ℕ} (bits : Vector (F p) m) :
    Utils.Bits.fieldFromBits bits = (bitsValue bits : F p) := by
  rw [Utils.Bits.fieldFromBits_as_sum, Fin.foldl_to_sum]
  unfold bitsValue
  conv_rhs => rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_val, Fin.getElem_fin]
  rw [ZMod.cast_id]
  change bits[i] * (2 ^ i.val : F p) = bits[i] * (2 ^ i.val : F p)
  rfl

omit h_large hn in
private lemma fromBitsExpr_eval_bitsValue {m : ℕ} (env : Environment (F p))
    (bits_var : Vector (Expression (F p)) m) (bits : Vector (F p) m)
    (h_eval : Vector.map (Expression.eval env) bits_var = bits) :
    Expression.eval env (Utils.Bits.fieldFromBitsExpr bits_var) = (bitsValue bits : F p) := by
  show env (Utils.Bits.fieldFromBitsExpr bits_var) = _
  rw [Utils.Bits.fieldFromBits_eval, h_eval, fieldFromBits_eq_bitsValue]

omit h_large hn in
/-- fromBitsExpr evaluated at concrete inputs = (valueBits bits : F p). -/
private lemma fromBitsExpr_eval_normalized (env : Environment (F p))
    (bits_var : Var (fields 32) (F p)) (bits : Vector (F p) 32)
    (h_eval : Vector.map (Expression.eval env) bits_var = bits) :
    Expression.eval env (fromBitsExpr bits_var) = (valueBits bits : F p) := by
  show Expression.eval env (Utils.Bits.fieldFromBitsExpr bits_var) = _
  rw [fromBitsExpr_eval_bitsValue env bits_var bits h_eval, bitsValue_eq_valueBits]

omit h_large hn in
/-- For normalized bits with p > 2^32, (fromBitsExpr bits_var).val = valueBits bits. -/
private lemma fromBitsExpr_val_eq (env : Environment (F p))
    (bits_var : Var (fields 32) (F p)) (bits : Vector (F p) 32)
    (h_eval : Vector.map (Expression.eval env) bits_var = bits)
    (h_norm : Normalized bits) (hp : 2^32 < p) :
    (Expression.eval env (fromBitsExpr bits_var)).val = valueBits bits := by
  rw [fromBitsExpr_eval_normalized env bits_var bits h_eval]
  exact ZMod.val_natCast_of_lt (by linarith [valueBits_lt_two_pow bits h_norm])

omit h_large hn in
private lemma var_vector_eval (env : Environment (F p)) (m i₀ : ℕ) :
    Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => (var {index := i₀ + i} : Expression (F p)))
    = Vector.ofFn fun i : Fin m => env.get (i₀ + i.val) := by
  ext i
  simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]

omit h_large hn in
private lemma isbool_of_bool_constraint {x : F p} (h : x * (x + -1) = 0) : IsBool x := by
  rwa [show x + -1 = x - 1 by ring, ← IsBool.iff_mul_sub_one] at h

omit h_large hn in
private lemma normalized_of_bool_holds (env : Environment (F p)) (i₀ : ℕ)
    (h : ∀ i : Fin 32, env.get (i₀ + i.val) * (env.get (i₀ + i.val) + -1) = 0) :
    Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) := by
  intro i
  have hi := h i
  have h_get : (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
    simp [Vector.getElem_ofFn]
  rw [h_get]
  exact isbool_of_bool_constraint hi

omit h_large hn in
private lemma bools_of_bool_holds {m : ℕ} (env : Environment (F p)) (i₀ : ℕ)
    (h : ∀ i : Fin m, env.get (i₀ + i.val) * (env.get (i₀ + i.val) + -1) = 0) :
    ∀ i : Fin m, (Vector.ofFn fun j : Fin m => env.get (i₀ + j.val))[i] = 0 ∨
      (Vector.ofFn fun j : Fin m => env.get (i₀ + j.val))[i] = 1 := by
  intro i
  have hi := h i
  have h_get : (Vector.ofFn fun j : Fin m => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
    simp [Vector.getElem_ofFn]
  rw [h_get]
  exact isbool_of_bool_constraint hi

omit h_large hn in
private lemma eval_vector_get_fields (env : Environment (F p))
    (ops_var : Var (ProvableVector (fields 32) n) (F p))
    (ops : ProvableVector (fields 32) n (F p))
    (h_eval : eval env ops_var = ops) (j : Fin n) :
    Vector.map (Expression.eval env) ops_var[j] = ops[j] := by
  have h := eval_vector_eq_get env ops_var ops h_eval j.val j.isLt
  simpa [CircuitType.eval_expression] using h

omit h_large hn in
private lemma evalBitsNat_eq_valueBits (env : ProverEnvironment (F p))
    (a_var : Var (fields 32) (F p)) (a : fields 32 (F p))
    (h : Vector.map (Expression.eval env.toEnvironment) a_var = a) :
    evalBitsNat env a_var = valueBits a := by
  subst h
  unfold evalBitsNat valueBits
  apply Finset.sum_congr rfl
  intro i _
  simp [Vector.getElem_map]

omit h_large hn in
private lemma sumBitsNat_eq_opsValueSum (env : ProverEnvironment (F p))
    (ops_var : Var (ProvableVector (fields 32) n) (F p))
    (ops : ProvableVector (fields 32) n (F p))
    (h_eval : eval env.toEnvironment ops_var = ops) :
    sumBitsNat env ops_var = opsValueSum ops := by
  unfold sumBitsNat opsValueSum
  apply Finset.sum_congr rfl
  intro j _
  exact evalBitsNat_eq_valueBits env ops_var[j] ops[j]
    (eval_vector_get_fields env.toEnvironment ops_var ops h_eval j)

omit h_large hn in
private lemma sumExpr_eval_eq (env : Environment (F p))
    (ops_var : Var (ProvableVector (fields 32) n) (F p))
    (ops : ProvableVector (fields 32) n (F p))
    (h_eval : eval env ops_var = ops) :
    Expression.eval env (sumExpr ops_var) = (opsValueSum ops : F p) := by
  unfold sumExpr opsValueSum
  rw [eval_foldl]
  · simp only [Expression.eval]
    rw [Fin.foldl_to_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact fromBitsExpr_eval_normalized env ops_var[j] ops[j]
      (eval_vector_get_fields env ops_var ops h_eval j)
  · intro e i
    simp [Expression.eval]

omit h_large in
private lemma opsValueSum_lt_two_pow35 (ops : ProvableVector (fields 32) n (F p))
    (h : ∀ j : Fin n, Normalized ops[j]) :
    opsValueSum ops < 2^35 := by
  have h_each_le : ∀ j : Fin n, valueBits ops[j] ≤ 2^32 - 1 := by
    intro j
    have hlt := valueBits_lt_two_pow ops[j] (h j)
    omega
  have h_sum_le : opsValueSum ops ≤ n * (2^32 - 1) := by
    unfold opsValueSum
    calc
      ∑ j : Fin n, valueBits ops[j] ≤ ∑ _j : Fin n, (2^32 - 1) := by
        apply Finset.sum_le_sum
        intro j _
        exact h_each_le j
      _ = n * (2^32 - 1) := by simp
  have h_n_le : n ≤ 8 := hn.elim
  have h_prod_le : n * (2^32 - 1) ≤ 8 * (2^32 - 1) :=
    Nat.mul_le_mul_right _ h_n_le
  have h_prod_lt : 8 * (2^32 - 1) < 2^35 := by norm_num
  exact lt_of_le_of_lt (le_trans h_sum_le h_prod_le) h_prod_lt

omit h_large hn hcw [NeZero cw] in
/-- The operand-sum quotient by `2^32` fits in `cw` carry bits (uses `n ≤ 2^cw`). -/
private lemma opsValueSum_div_lt (ops : ProvableVector (fields 32) n (F p))
    (h : ∀ j : Fin n, Normalized ops[j]) :
    opsValueSum ops / 2^32 < 2^cw := by
  have h_each_le : ∀ j : Fin n, valueBits ops[j] ≤ 2^32 - 1 := fun j => by
    have hlt := valueBits_lt_two_pow ops[j] (h j); omega
  have h_sum_le : opsValueSum ops ≤ n * (2^32 - 1) := by
    unfold opsValueSum
    calc
      ∑ j : Fin n, valueBits ops[j] ≤ ∑ _j : Fin n, (2^32 - 1) :=
        Finset.sum_le_sum (fun j _ => h_each_le j)
      _ = n * (2^32 - 1) := by simp
  have h_n_le : n ≤ 2^cw := hncw.elim
  apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)).mpr
  have h2 : n * (2^32 - 1) ≤ 2^cw * (2^32 - 1) := Nat.mul_le_mul_right _ h_n_le
  have h3 : 2^cw * (2^32 - 1) < 2^cw * 2^32 :=
    mul_lt_mul_of_pos_left (by norm_num) (Nat.two_pow_pos cw)
  omega

/-- testBit equals div/mod expression. -/
private lemma testBit_ite_eq (x i : ℕ) : (if x.testBit i = true then 1 else 0 : ℕ) = x / 2^i % 2 := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (x / 2^i) with h | h <;> rw [h] <;> rfl

/-- Bit decomposition: sum_i (x / 2^i % 2) * 2^i = x for x < 2^m. -/
private lemma bit_decomp_sum (m x : ℕ) (h_x_lt : x < 2^m) :
    ∑ i : Fin m, x / 2^i.val % 2 * 2^i.val = x := by
  conv_rhs => rw [← Utils.Bits.fromBits_toBits h_x_lt]
  unfold Utils.Bits.fromBits Utils.Bits.toBits
  rw [Fin.foldl_to_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_mapRange, testBit_ite_eq]

omit h_large in
private lemma bitsValue_bit_decomp (m x : ℕ) (h_x_lt : x < 2^m) (hp2 : 2 < p) :
    bitsValue (Vector.ofFn fun i : Fin m => ((x / 2^i.val % 2 : ℕ) : F p)) = x := by
  unfold bitsValue
  calc
    ∑ i : Fin m, (Vector.ofFn fun j : Fin m =>
        ((x / 2^j.val % 2 : ℕ) : F p))[i].val * 2^i.val
        = ∑ i : Fin m, x / 2^i.val % 2 * 2^i.val := by
          apply Finset.sum_congr rfl
          intro i _
          have hbit_lt : x / 2^i.val % 2 < p := by
            have : x / 2^i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          have hval : (Vector.ofFn fun j : Fin m =>
              ((x / 2^j.val % 2 : ℕ) : F p))[i].val = x / 2^i.val % 2 := by
            simp [Vector.getElem_ofFn, ZMod.val_natCast_of_lt hbit_lt]
          rw [hval]
    _ = x := bit_decomp_sum m x h_x_lt

omit h_large in
private lemma fieldFromBits_bit_decomp (m x : ℕ) (h_x_lt : x < 2^m) (hp2 : 2 < p) :
    Utils.Bits.fieldFromBits (Vector.ofFn fun i : Fin m => ((x / 2^i.val % 2 : ℕ) : F p)) =
    ((x : ℕ) : F p) := by
  rw [fieldFromBits_eq_bitsValue, bitsValue_bit_decomp m x h_x_lt hp2]

omit h_large hn hncw hcw [NeZero cw] in
private lemma carryExpr_eval_bitsValue (env : Environment (F p))
    (c_var : Var (fields cw) (F p)) (c : fields cw (F p))
    (h_eval : Vector.map (Expression.eval env) c_var = c) :
    Expression.eval env (carryExpr c_var) = (bitsValue c : F p) :=
  fromBitsExpr_eval_bitsValue env c_var c h_eval

omit h_large hn hncw hcw [NeZero cw] in
private lemma carryExpr_val_eq (env : Environment (F p))
    (c_var : Var (fields cw) (F p)) (c : fields cw (F p))
    (h_eval : Vector.map (Expression.eval env) c_var = c)
    (h_norm : ∀ i : Fin cw, c[i] = 0 ∨ c[i] = 1) (hpc : 2^cw < p) :
    (Expression.eval env (carryExpr c_var)).val = bitsValue c := by
  rw [carryExpr_eval_bitsValue env c_var c h_eval]
  exact ZMod.val_natCast_of_lt (by linarith [bitsValue_lt_two_pow c h_norm])

/-!
## Soundness
-/

omit hncw [NeZero cw] in
private theorem soundness_of_constraints (i₀ : ℕ) (env : Environment (F p))
    (input_var : Var (ProvableVector (fields 32) n) (F p))
    (input : ProvableVector (fields 32) n (F p))
    (h_input : eval env input_var = input)
    (h_assumptions : ∀ j : Fin n, Normalized input[j])
    (h_z_bool : ∀ i : Fin 32, env.get (i₀ + i.val) * (env.get (i₀ + i.val) + -1) = 0)
    (h_c_bool : ∀ i : Fin cw, env.get (i₀ + 32 + i.val) * (env.get (i₀ + 32 + i.val) + -1) = 0)
    (h_lin : Expression.eval env (sumExpr input_var) +
      -Expression.eval env (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
      -((2^32 : F p) * Expression.eval env (carryExpr
        (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p))))) = 0) :
    Spec input (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) := by
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) :=
    normalized_of_bool_holds env i₀ h_z_bool
  have h_c_norm : ∀ i : Fin cw,
      (Vector.ofFn fun j : Fin cw => env.get (i₀ + 32 + j.val))[i] = 0 ∨
      (Vector.ofFn fun j : Fin cw => env.get (i₀ + 32 + j.val))[i] = 1 :=
    bools_of_bool_holds env (i₀ + 32) h_c_bool
  refine ⟨?_, h_z_norm⟩
  have h_p_large := h_large.elim
  have h_cw_le : (2:ℕ)^cw ≤ 8 := hcw.elim
  have hp32 : (2:ℕ)^32 < p := by omega
  have hpc : (2:ℕ)^cw < p := by omega
  have hp2 : 2 < p := by omega
  set z : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) with hz_def
  set c : fields cw (F p) := Vector.ofFn fun i : Fin cw => env.get (i₀ + 32 + i.val) with hc_def
  set vz := valueBits z with hvz_def
  set vc := bitsValue c with hvc_def
  have h_ops_lt : opsValueSum input < 2^35 :=
    opsValueSum_lt_two_pow35 input h_assumptions
  have h_ops_lt_p : opsValueSum input < p := by linarith
  have hvz_lt : vz < 2^32 := valueBits_lt_two_pow z (by simpa [z] using h_z_norm)
  have hvc_lt : vc < 2^cw := bitsValue_lt_two_pow c (by simpa [c] using h_c_norm)
  have hvc_le : vc ≤ 7 := by omega
  have h_sum_eval : (Expression.eval env (sumExpr input_var)).val = opsValueSum input := by
    rw [sumExpr_eval_eq env input_var input h_input]
    exact ZMod.val_natCast_of_lt h_ops_lt_p
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) = z := by
    exact var_vector_eval env 32 i₀
  have h_fz : (Expression.eval env (fromBitsExpr
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))))).val = vz :=
    fromBitsExpr_val_eq env _ z h_z_eval (by simpa [z] using h_z_norm) hp32
  have h_c_eval : Vector.map (Expression.eval env)
      (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p))) = c := by
    exact var_vector_eval env cw (i₀ + 32)
  have h_fc : (Expression.eval env (carryExpr
      (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p))))).val = vc :=
    carryExpr_val_eq env _ c h_c_eval (by simpa [c] using h_c_norm) hpc
  have h_pow32_val : (2^32 : F p).val = 2^32 := by
    have hcast : ((2^32 : ℕ) : F p) = (2^32 : F p) := by push_cast; ring
    rw [← hcast, ZMod.val_natCast_of_lt hp32]
  have h_lin' : Expression.eval env (sumExpr input_var) =
      Expression.eval env (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
      (2^32 : F p) * Expression.eval env (carryExpr
        (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p)))) := by
    rw [← sub_eq_zero]
    have h_ring : Expression.eval env (sumExpr input_var) -
        (Expression.eval env (fromBitsExpr
          (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
        (2^32 : F p) * Expression.eval env (carryExpr
          (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p))))) =
        Expression.eval env (sumExpr input_var) +
        -Expression.eval env (fromBitsExpr
          (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
        -((2^32 : F p) * Expression.eval env (carryExpr
          (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p))))) := by ring
    rw [h_ring]
    exact h_lin
  have h_mul_lt : 2^32 * vc < p := by
    have hlt : 2^32 * vc < 2^35 := by
      calc
        2^32 * vc ≤ 2^32 * 7 := Nat.mul_le_mul_left _ hvc_le
        _ < 2^35 := by norm_num
    linarith
  have h_total_lt : vz + 2^32 * vc < p := by
    have hlt : vz + 2^32 * vc < 2^35 := by
      calc
        vz + 2^32 * vc < 2^32 + 2^32 * 7 := Nat.add_lt_add_of_lt_of_le hvz_lt
          (Nat.mul_le_mul_left _ hvc_le)
        _ = 2^35 := by norm_num
    linarith
  have h_rhs_val : (Expression.eval env (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) +
      (2^32 : F p) * Expression.eval env (carryExpr
        (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p))))).val =
      vz + 2^32 * vc := by
    rw [ZMod.val_add, ZMod.val_mul, h_fz, h_pow32_val, h_fc]
    rw [Nat.mod_eq_of_lt h_mul_lt, Nat.mod_eq_of_lt h_total_lt]
  have h_nat_eq : opsValueSum input = vz + 2^32 * vc := by
    have := congr_arg ZMod.val h_lin'
    rw [h_sum_eval, h_rhs_val] at this
    exact this
  change vz = opsValueSum input % 2^32
  rw [h_nat_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvz_lt]

omit hncw in
theorem soundness : Soundness (Input := ProvableVector (fields 32) n) (Output := fields 32)
    (F p) (elaborated (n:=n) (cw:=cw)) (Assumptions (n:=n)) (Spec (n:=n)) := by
  circuit_proof_start [addMod32]
  obtain ⟨h_z_bool, h_c_bool, h_lin⟩ := h_holds
  rw [var_vector_eval env 32 i₀]
  exact soundness_of_constraints i₀ env input_var input h_input h_assumptions
    h_z_bool h_c_bool h_lin

/-!
## Completeness
-/

omit hn hcw in
theorem completeness : Completeness (Input := ProvableVector (fields 32) n) (Output := fields 32)
    (F p) (elaborated (n:=n) (cw:=cw)) (Assumptions (n:=n)) := by
  circuit_proof_start [addMod32]
  obtain ⟨h_env_z, h_env_c⟩ := h_env
  obtain ⟨h_env_c, -⟩ := h_env_c
  set S := sumBitsNat env input_var with hS_def
  have h_input_env : eval env.toEnvironment input_var = input := by
    simpa [CircuitType.eval_expression_prover] using h_input
  have hS_eq : S = opsValueSum input := by
    rw [hS_def]
    exact sumBitsNat_eq_opsValueSum env input_var input h_input_env
  have h_p_large := h_large.elim
  have hp32 : (2:ℕ)^32 < p := by omega
  have hp2 : 2 < p := by omega
  have h_S_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
  have h_div_lt : S / 2^32 < 2^cw := by
    rw [hS_eq]; exact opsValueSum_div_lt input h_assumptions
  have hS_decomp : S = S % 2^32 + 2^32 * (S / 2^32) := by
    exact (Nat.mod_add_div S (2^32)).symm.trans (by ring)
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have henv_i := h_env_z i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S % 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · have henv_i := h_env_c i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · have h_sum_expr : Expression.eval env.toEnvironment (sumExpr input_var) =
        ((opsValueSum input : ℕ) : F p) :=
      sumExpr_eval_eq env.toEnvironment input_var input h_input_env
    have h_z_eval : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [var_vector_eval env.toEnvironment 32 i₀]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have h := h_env_z ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at h
      exact h
    have h_fz : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      change env.toEnvironment (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p)
      rw [Utils.Bits.fieldFromBits_eval, h_z_eval]
      exact fieldFromBits_bit_decomp 32 (S % 2^32) h_S_mod_lt hp2
    have h_c_eval : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin cw => ((S / 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [var_vector_eval env.toEnvironment cw (i₀ + 32)]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have h := h_env_c ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at h
      exact h
    have h_fc : Expression.eval env.toEnvironment (carryExpr
        (Vector.mapRange cw fun i => (var {index := i₀ + 32 + i} : Expression (F p)))) =
        ((S / 2^32 : ℕ) : F p) := by
      rw [carryExpr_eval_bitsValue env.toEnvironment _ _ h_c_eval]
      rw [bitsValue_bit_decomp cw (S / 2^32) h_div_lt hp2]
    rw [h_sum_expr, h_fz, h_fc]
    have hnat : opsValueSum input = S % 2^32 + 2^32 * (S / 2^32) := by
      rw [← hS_eq, ← hS_decomp]
    have hF : ((opsValueSum input : ℕ) : F p) =
        ((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((S / 2^32 : ℕ) : F p) := by
      have h := congr_arg (Nat.cast : ℕ → F p) hnat
      rw [Nat.cast_add, Nat.cast_mul] at h
      rw [show ((2^32 : ℕ) : F p) = (2^32 : F p) from by push_cast; ring] at h
      exact h
    have rearrange : ((opsValueSum input : ℕ) : F p) +
        -((S % 2^32 : ℕ) : F p) + -((2^32 : F p) * ((S / 2^32 : ℕ) : F p)) =
        ((opsValueSum input : ℕ) : F p) -
        (((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((S / 2^32 : ℕ) : F p)) := by ring
    rw [rearrange, hF, sub_self]

def circuit : FormalCircuit (F p) (ProvableVector (fields 32) n) (fields 32) :=
  { elaborated (n:=n) (cw:=cw) with
    Assumptions := Assumptions
    Spec := Spec
    soundness := soundness
    completeness := completeness }

end AddMod32
end Gadgets.SHA256
end
