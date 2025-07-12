import Clean.Circuit
import Clean.Utils.Bits
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean


namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

-- Define a 2D vector type for BinSum inputs
-- Represents ops operands, each with n bits
-- This is a vector of ops elements, where each element is a vector of n field elements
@[reducible]
def BinSumInput (n ops : ℕ) := ProvableVector (fields n) ops

-- Instance for NonEmptyProvableType for fields when n > 0
instance {n : ℕ} [hn : NeZero n] : NonEmptyProvableType (fields n) where
  nonempty := Nat.pos_of_ne_zero hn.out

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/binsum.circom

The BinSum template takes multiple binary numbers as input and outputs their sum in binary form.
Note that the input bits must be guaranteed to be binary (0 or 1) by the caller.
The circuit ensures that:
1. All output bits are binary (0 or 1)
2. The sum of inputs equals the sum represented by output bits
-/

def nbits (a : ℕ) : ℕ :=
  if a = 0 then 1 else Nat.log2 a + 1

-- Lemma: The ZMod.val of a Fin.foldl sum is bounded by the sum of individual ZMod.vals
omit [Fact (Nat.Prime p)] [Fact (p > 2)] in
lemma foldl_sum_val_bound {ops : ℕ} (f : Fin ops → F p) (M : ℕ)
    (h_bound : ∀ j : Fin ops, (f j).val ≤ M) (h_no_overflow : ops * M < p) :
    (Fin.foldl ops (fun sum j => sum + f j) 0).val ≤ ops * M := by
  -- Use induction on ops
  induction ops with
  | zero =>
    simp only [Fin.foldl_zero, ZMod.val_zero, zero_mul, le_refl]
  | succ k ih =>
    -- For the inductive step, use Fin.foldl_succ_last
    rw [Fin.foldl_succ_last]
    -- The key insight: use ZMod.val_add_of_lt when the sum doesn't overflow
    have h_partial_bound := ih (fun j => f j.castSucc)
                               (fun j => h_bound j.castSucc)
                               (by
                                 -- k * M < (k+1) * M < p
                                 apply Nat.lt_of_le_of_lt _ h_no_overflow
                                 apply Nat.mul_le_mul_right
                                 exact Nat.le_succ k)

    -- Show that the partial sum + new element doesn't overflow
    have h_add_lt : (Fin.foldl k (fun sum j => sum + f j.castSucc) 0).val + (f (Fin.last k)).val < p := by
      apply Nat.lt_of_le_of_lt
      · apply Nat.add_le_add h_partial_bound (h_bound (Fin.last k))
      · rw [← Nat.succ_mul]
        exact h_no_overflow

    -- Use the fact that ZMod.val preserves addition when no overflow
    rw [ZMod.val_add_of_lt h_add_lt]
    -- We want to show: partial_sum + element ≤ (k+1) * M
    -- We know: partial_sum ≤ k * M and element ≤ M
    -- So: partial_sum + element ≤ k * M + M = (k+1) * M
    have h_succ : (k + 1) * M = k * M + M := by rw [Nat.succ_mul]
    rw [h_succ]
    apply Nat.add_le_add h_partial_bound (h_bound (Fin.last k))

-- Lemma: The sum of ops n-bit numbers fits in nbits((2^n - 1) * ops) bits
omit [Fact (p > 2)] in
lemma sum_bound_of_binary_inputs {n ops : ℕ} [hn : NeZero n] (hops : 0 < ops)
    (hnout : 2^(nbits ((2^n - 1) * ops)) < p)
    (inputs : BinSumInput n ops (F p))
    (h_binary : ∀ j k (hj : j < ops) (hk : k < n), IsBool inputs[j][k])
    (h_sum : F p)
    (h_sum_eq : h_sum = Fin.foldl ops (fun sum j => sum + fieldFromBits inputs[j]) 0) :
    h_sum.val < 2^(nbits ((2^n - 1) * ops)) := by
  -- Each input[j] is n-bit binary, so fieldFromBits inputs[j] ≤ 2^n - 1
  -- The sum of ops such numbers is at most ops * (2^n - 1)
  -- We need to show this is < 2^(nbits(ops * (2^n - 1)))

  -- First, bound each individual fieldFromBits
  have h_individual_bound : ∀ j (hj : j < ops), (fieldFromBits inputs[j]).val ≤ 2^n - 1 := by
    intro j hj
    -- Apply the bound theorem for binary inputs
    have h_binary_j : ∀ k (hk : k < n), IsBool inputs[j][k] := fun k hk => h_binary j k hj hk
    have h_binary_alt : ∀ k (hk : k < n), inputs[j][k] = 0 ∨ inputs[j][k] = 1 := by
      intro k hk
      cases h_binary_j k hk with
      | inl h => left; exact h
      | inr h => right; exact h
    -- Use the fieldFromBits bound
    have h_lt := fieldFromBits_lt inputs[j] h_binary_alt
    -- We have fieldFromBits inputs[j] < 2^n, so its value is ≤ 2^n - 1
    omega

  -- Now bound the sum using h_sum_eq
  rw [h_sum_eq]
  -- The sum is bounded by ops * (2^n - 1)
  have h_sum_bound : (Fin.foldl ops (fun sum j => sum + fieldFromBits inputs[j]) 0).val ≤ ops * (2^n - 1) := by
    -- Apply our general lemma about foldl sum bounds
    apply foldl_sum_val_bound (fun j => fieldFromBits inputs[j]) (2^n - 1)
    · -- Prove each element is bounded
      intro j
      exact h_individual_bound j j.isLt
    · -- Prove no overflow: ops * (2^n - 1) < p
      -- This follows from hnout and the definition of nbits
      rw [mul_comm]
      apply Nat.lt_trans _ hnout
      simp only [nbits]
      split_ifs with h
      · -- Case (2^n - 1) * ops = 0, but this contradicts our assumptions
        have pos_prod : 0 < (2^n - 1) * ops := by
          apply Nat.mul_pos
          · have : 1 < 2^n := by
              apply Nat.one_lt_pow
              · exact NeZero.ne n
              · norm_num
            omega
          · exact hops
        omega
      · -- Case (2^n - 1) * ops ≠ 0
        exact Nat.lt_log2_self

  -- Apply the bound we just proved
  apply Nat.lt_of_le_of_lt h_sum_bound
  -- We need to apply the nbits property to (2^n - 1) * ops
  rw [mul_comm]
  -- The goal is (2^n - 1) * ops < 2^(nbits ((2^n - 1) * ops))
  -- This follows from the definition of nbits
  simp only [nbits]
  split_ifs with h
  · -- Case (2^n - 1) * ops = 0, contradicts our assumptions
    have pos_prod : 0 < (2^n - 1) * ops := by
      apply Nat.mul_pos
      · have : 1 < 2^n := by
          apply Nat.one_lt_pow
          · exact NeZero.ne n
          · norm_num
        omega
      · exact hops
    omega
  · -- Case (2^n - 1) * ops ≠ 0
    exact Nat.lt_log2_self
namespace BinSum

/-
Circuit that computes the linear sum of multiple binary numbers.
Takes n-bit binary numbers and computes their weighted sum.
-/
namespace InputLinearSum

-- Compute the linear sum of input bits weighted by powers of 2
def main (n ops : ℕ) (inp : BinSumInput n ops (Expression (F p))) : Circuit (F p) (Expression (F p)) := do
  -- Calculate input linear sum
  Circuit.foldlRange n (0 : Expression (F p)) fun lin k => do
    let e2 : Expression (F p) := (2^k.val : F p)
    Circuit.foldlRange ops lin fun lin j => do
      return lin + inp[j][k] * e2

-- Lemma: Expression.eval distributes over Fin.foldl with addition
omit [Fact (p > 2)] in
lemma Expression.eval_foldl (env : Environment (F p)) (n : ℕ)
    (f : Expression (F p) → Fin n → Expression (F p)) (init : Expression (F p))
    (hf : ∀ (e : Expression (F p)) (i : Fin n),
      Expression.eval env (f e i) = Expression.eval env (f (Expression.const (Expression.eval env e)) i)) :
    Expression.eval env (Fin.foldl n f init) =
    Fin.foldl n (fun (acc : F p) (i : Fin n) => Expression.eval env (f (Expression.const acc) i)) (Expression.eval env init) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n' ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    -- Apply the inductive hypothesis with the appropriate function and assumption
    have hf' : ∀ (e : Expression (F p)) (i : Fin n'),
      Expression.eval env (f e i.castSucc) = Expression.eval env (f (Expression.const (Expression.eval env e)) i.castSucc) := by
      intros e i
      exact hf e i.castSucc

    have h1 : Expression.eval env (Fin.foldl n' (fun x1 x2 => f x1 x2.castSucc) init) =
              Fin.foldl n' (fun acc i => Expression.eval env (f (Expression.const acc) i.castSucc)) (Expression.eval env init) :=
      ih (fun x i => f x i.castSucc) hf'

    -- Now apply the assumption to relate the two sides
    rw [hf (Fin.foldl n' (fun x1 x2 => f x1 x2.castSucc) init) (Fin.last n')]
    -- Rewrite using h1
    rw [h1]

-- Helper lemma: Factoring out a constant from a foldl sum
omit [Fact (p > 2)] in
lemma foldl_factor_const {n : ℕ} (f : Fin n → F p) (c : F p) (init : F p) :
    Fin.foldl n (fun acc i => acc + f i * c) init =
    init + c * Fin.foldl n (fun acc i => acc + f i) 0 := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ m ih =>
    -- Unfold the foldl on both sides
    simp only [Fin.foldl_succ_last]
    -- Apply IH to the castSucc part
    have h_eq : Fin.foldl m (fun x1 x2 => x1 + f x2.castSucc * c) init =
                Fin.foldl m (fun x1 x2 => x1 + (f ∘ Fin.castSucc) x2 * c) init := by
      congr
    rw [h_eq, ih (f ∘ Fin.castSucc)]
    -- Now simplify the RHS
    have h_rhs : Fin.foldl m (fun x1 x2 => x1 + f x2.castSucc) 0 =
                 Fin.foldl m (fun x1 x2 => x1 + (f ∘ Fin.castSucc) x2) 0 := by
      congr
    rw [← h_rhs]
    -- Now we have: init + c * (foldl of castSucc) + f(last) * c
    -- We want: init + c * (foldl of castSucc + f(last))
    ring

-- Lemma 1: The circuit evaluation computes the nested sum Σ_k 2^k * (Σ_j offset[j][k])
omit [Fact (p > 2)] in
lemma circuit_eval_nested_sum {n ops : ℕ}
    (env : Environment (F p))
    (offset : Var (BinSumInput n ops) (F p))
    (input_offset : ℕ) :
    Expression.eval env ((main n ops offset input_offset).1) =
    Fin.foldl n (fun acc k => acc + (2^k.val : F p) *
      Fin.foldl ops (fun acc' j => acc' + Expression.eval env offset[j][k]) 0) 0 := by
  -- The main function uses nested Circuit.foldlRange
  simp only [main, circuit_norm]
  rw [Expression.eval_foldl]
  · simp only [circuit_norm]
    congr 1
    ext acc k
    rw [Expression.eval_foldl]
    · simp only [circuit_norm]
      -- Apply the factorization lemma with proper coercions
      have h := foldl_factor_const (fun i => Expression.eval env offset[↑i][↑k]) (2 ^ k.val) acc
      -- The lemma gives us exactly what we need after recognizing that ↑k = k.val
      convert h
    · intros e i
      simp only [circuit_norm]
  · intros e i
    rw [Expression.eval_foldl]
    · simp only [circuit_norm]
      rw [Expression.eval_foldl]
      · simp only [circuit_norm]
      · intros e' i'
        simp only [circuit_norm]
    · intros e' i'
      simp only [circuit_norm]

-- Lemma to convert Fin.foldl to Finset.sum via range
omit [Fact (p > 2)] in
lemma foldl_eq_sum_range {α : Type*} [AddCommMonoid α] : ∀ (n' : ℕ) (f' : Fin n' → α),
    Fin.foldl n' (fun acc i => acc + f' i) 0 = ∑ i ∈ Finset.range n', if h : i < n' then f' ⟨i, h⟩ else 0 := by
  intro n' f'
  induction n' with
  | zero =>
    simp [Fin.foldl_zero, Finset.range_zero, Finset.sum_empty]
  | succ n'' ih =>
    rw [Fin.foldl_succ_last]
    rw [Finset.sum_range_succ]
    simp only [ih]
    -- We need to show that the sum equals itself plus the last term
    congr 1
    -- For the sum part, we need to show the functions are equal
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Fin.castSucc_mk]
      simp only [hi]
      simp only [↓reduceDIte]
      have hi' : i < n'' + 1 := by omega
      simp only [hi', ↓reduceDIte]
    · -- For the last term
      simp only [Fin.last, Nat.lt_succ_self, dif_pos]

omit [Fact p.Prime] [Fact (p > 2)] in
lemma foldl_to_sum : ∀ (n' : ℕ) (f' : Fin n' → F p),
    Fin.foldl n' (fun acc i => acc + f' i) 0 = ∑ i : Fin n', f' i := by
  intro n' f'
  simp only [Finset.sum_fin_eq_sum_range]
  exact foldl_eq_sum_range n' f'

-- Lemma 2: Summation interchange for the double sum
omit [Fact (p > 2)] in
lemma sum_interchange_binsum {n ops : ℕ} (f : Fin ops → Fin n → F p) :
    Fin.foldl n (fun acc k => acc + (2^k.val : F p) *
      Fin.foldl ops (fun acc' j => acc' + f j k) 0) 0 =
    Fin.foldl ops (fun acc j => acc +
      Fin.foldl n (fun acc' k => acc' + f j k * (2^k.val : F p)) 0) 0 := by
  -- Now convert the LHS
  have lhs_eq : Fin.foldl n (fun acc k => acc + (2^k.val : F p) *
      Fin.foldl ops (fun acc' j => acc' + f j k) 0) 0 =
      ∑ k : Fin n, (2^k.val : F p) * (∑ j : Fin ops, f j k) := by
    rw [foldl_to_sum]
    congr 1
    ext k
    rw [foldl_to_sum]

  -- Convert the RHS
  have rhs_eq : Fin.foldl ops (fun acc j => acc +
      Fin.foldl n (fun acc' k => acc' + f j k * (2^k.val : F p)) 0) 0 =
      ∑ j : Fin ops, (∑ k : Fin n, f j k * (2^k.val : F p)) := by
    rw [foldl_to_sum]
    congr 1
    ext j
    rw [foldl_to_sum]

  rw [lhs_eq, rhs_eq]
  -- Now we have: ∑ k, 2^k * (∑ j, f j k) = ∑ j, (∑ k, f j k * 2^k)
  -- Distribute multiplication
  simp only [Finset.mul_sum]
  -- Now: ∑ k, (∑ j, 2^k * f j k) = ∑ j, (∑ k, f j k * 2^k)
  -- Use sum_comm to swap order
  rw [Finset.sum_comm]
  -- Just need to show 2^k * f j k = f j k * 2^k
  simp only [mul_comm]

-- Lemma: fieldFromBits decomposes as sum of first n bits + bit_n * 2^n
omit [Fact (p > 2)] in
lemma fieldFromBits_succ (n : ℕ) (bits : Vector (F p) (n + 1)) :
    fieldFromBits bits =
    fieldFromBits (bits.take n) + bits[n] * (2^n : F p) := by
  simp only [fieldFromBits, fromBits, Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]
  have h_min : min n (n + 1) = n := min_eq_left (Nat.le_succ n)
  simp only [Vector.getElem_map, Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, Nat.cast_pow,
    Nat.cast_ofNat, Vector.take_eq_extract, add_tsub_cancel_right, Vector.extract_eq_pop,
    Nat.add_one_sub_one, Nat.sub_zero, Vector.getElem_cast, Vector.getElem_pop']
  congr
  · norm_num
  · -- Show the function equality via HEq
    -- The two functions are equal - they just have different variable names
    -- But we need to handle the type equality: Fin n vs Fin (min n (n + 1))
    have h_min : min n (n + 1) = n := min_eq_left (Nat.le_succ n)
    apply Function.hfunext
    · rfl
    · intro a0 a1 h_a
      have : a0 = a1 := by
        apply eq_of_heq
        assumption
      rw[this]
      apply Function.hfunext
      · rw [h_min]
      · intros b0 b1 h_b
        simp only [heq_eq_eq]
        congr
        rw [h_min]
        rw [h_min]
  · -- Show bits[n].cast = bits[n]
    -- The cast here is ZMod.cast from F p to F p, which should be identity
    rw [ZMod.cast_id']
    rfl


-- Lemma 3: The sum Σ_k bits[k] * 2^k equals fieldFromBits(bits)
omit [Fact (p > 2)] in
lemma fieldFromBits_as_sum {n : ℕ} (bits : Vector (F p) n) :
    fieldFromBits bits =
    Fin.foldl n (fun acc k => acc + bits[k] * (2^k.val : F p)) 0 := by
  -- fieldFromBits uses fromBits which sums bits[k].val * 2^k
  -- We need to show this equals the sum of bits[k] * 2^k (without .val)
  induction n
  · -- Base case: n = 0
    simp only [fieldFromBits, fromBits, Fin.foldl_zero]
    norm_cast
  · rename_i pre_n ih
    rw [fieldFromBits_succ]
    have min_pre_h : (min pre_n (pre_n + 1)) = pre_n := by omega
    calc
      _ = fieldFromBits (Vector.cast min_pre_h (bits.take pre_n)) + bits[pre_n] * 2 ^ pre_n := by
        congr
        simp only [Vector.take_eq_extract, add_tsub_cancel_right, Vector.extract_eq_pop,
          Nat.add_one_sub_one, Nat.sub_zero, Vector.cast_cast, Vector.cast_rfl]
        apply Vector.cast_heq
      _ = _ := by
        rw [ih]
        simp only [Fin.foldl_succ_last]
        congr
        ext acc k
        simp only [Vector.take_eq_extract, add_tsub_cancel_right, Vector.extract_eq_pop,
          Nat.add_one_sub_one, Nat.sub_zero, Fin.getElem_fin, Fin.coe_castSucc, add_right_inj,
          mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
        left
        repeat rw[Vector.getElem_cast]
        simp only [Vector.getElem_pop']

-- Lemma showing that evaluating the main circuit computes the correct sum
omit [Fact (p > 2)] in
lemma main_eval_eq_sum {n ops : ℕ} [hn : NeZero n]
    (env : Environment (F p))
    (input : Var (BinSumInput n ops) (F p))
    (input_val : BinSumInput n ops (F p))
    (h_eval : eval env input = input_val)
    (input_offset : ℕ) :
    Expression.eval env ((main n ops input input_offset).1) =
    Fin.foldl ops (fun acc j => acc + fieldFromBits input_val[j]) 0 := by
  -- The main function uses offset[j][k] which evaluates to input_val[j][k]
  -- We need to show the nested sum equals the sum of fieldFromBits

  -- Step 1: Apply circuit_eval_nested_sum to show how the circuit evaluates
  rw [circuit_eval_nested_sum env input input_offset]

  -- Step 2: We need to replace Expression.eval env offset[j][k] with input_val[j][k]
  -- First, let's establish this equality
  have offset_eval_elem : ∀ (j : Fin ops) (k : Fin n), Expression.eval env input[j][k] = input_val[j][k] := by
    intro j k
    -- Goal: Expression.eval env input[j][k] = input_val[j][k]
    -- We have: eval env input = input_val
    -- We need to show: Expression.eval env input[j][k] = input_val[j][k]
    -- Let's work step by step

    -- For vectors of expressions (fields n), the evaluation is element-wise
    -- So (eval env input[j])[k] = Expression.eval env (input[j][k])

    -- We can use the fact that for fields n:
    -- eval env v = Vector.map (Expression.eval env) v

    simp only [Fin.getElem_fin]

    -- For fields n, eval is defined as mapping Expression.eval over the vector
    -- So (eval env v)[i] = (v.map (Expression.eval env))[i] = Expression.eval env v[i]
    have h_fields_eval : ∀ (v : Var (fields n) (F p)) (i : Fin n),
      (eval env v)[i] = Expression.eval env v[i] := by
      intro v i
      simp only [ProvableType.eval_fields]
      -- Now we have (Vector.map (Expression.eval env) v)[i] = Expression.eval env v[i]
      -- This follows from the property of Vector.map
      have i_lt : ↑i < n := by omega
      unfold BinSumInput at *
      have vget := Vector.getElem_map (xs := v) (Expression.eval env) i_lt
      simp only [Fin.getElem_fin, Vector.getElem_map]

    -- The goal has Expression.eval env input[↑j][↑k] = input_val[↑j][↑k]
    -- We need to be careful about the coercions

    -- First, let's understand what input[↑j] is
    -- input : Var (BinSumInput n ops) (F p)
    -- input[↑j] : Var (fields n) (F p) = fields n (Expression (F p))
    -- input[↑j][↑k] : Expression (F p)

    have h_step1 := h_fields_eval input[↑j] k
    simp only [Fin.getElem_fin] at h_step1
    rw[← h_step1]
    congr
    rw[getElem_eval_vector]
    rw[h_eval]

  -- Now substitute this equality in our sum
  simp only [offset_eval_elem]

  -- Step 3: Apply sum_interchange_binsum to swap the order of summation
  rw [sum_interchange_binsum (fun j k => input_val[j][k])]

  -- Step 4: Now we need to show that each inner sum equals fieldFromBits
  -- The goal should be:
  -- Fin.foldl ops (fun acc j => acc + Fin.foldl n (fun acc' k => acc' + input_val[j][k] * 2^k) 0) 0
  -- = Fin.foldl ops (fun acc j => acc + fieldFromBits input_val[j]) 0

  -- Apply fieldFromBits_as_sum to each inner sum
  congr 1
  ext j
  rw [← fieldFromBits_as_sum]

def circuit (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) :
    FormalCircuit (F p) (BinSumInput n ops) field where
  main input := main n ops input

  localLength _ := 0
  localLength_eq := by
    simp only [circuit_norm, main]
    -- Need to show that the conditional expression equals 0
    simp only [mul_zero]
    -- Both branches of the if-then-else evaluate to 0
    split_ifs <;> simp

  output input offset := Circuit.output (main n ops input) offset
  output_eq := by
    intros
    rfl

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input :=
    -- All inputs are binary
    ∀ j k (hj : j < ops) (hk : k < n), IsBool input[j][k]

  Spec input output :=
    -- Output equals the sum of all input bits interpreted as numbers
    output = Fin.foldl ops (fun sum (j : Fin ops) =>
      sum + fieldFromBits input[j]) (0 : F p)

  soundness := by
    intros input h_assumptions offset env h_input_eval h_constraints
    intro h_constraints_hold
    -- InputLinearSum has no internal constraints, just computes the sum
    -- The soundness proof shows that the output equals the weighted sum of inputs

    -- The circuit output is the result of the nested foldl computation
    simp only [ElaboratedCircuit.output, circuit_norm]

    -- We need to show that the output equals the sum of fieldFromBits
    -- The main function computes: sum over k of (2^k * sum over j of inp[j][k])
    -- This is equivalent to: sum over j of (sum over k of (2^k * inp[j][k]))
    -- Which equals: sum over j of fieldFromBits(inp[j])

    -- The circuit has no constraints, so h_constraints_hold is trivial
    -- We just need to show the computation is correct
    simp only [main]

    -- The output is the evaluation of the circuit's output expression
    -- We need to show it equals the sum of fieldFromBits of the inputs

    -- Apply our lemma to show the circuit computes the correct sum
    exact main_eval_eq_sum h_assumptions offset env h_input_eval input

  completeness := by
    intros input_var h_uses_local_witnesses input_val h_input_eval h_assumptions
    -- InputLinearSum has no constraints, so it's always satisfiable
    -- The circuit just computes a value, no constraints to satisfy
    simp only [circuit_norm, main]
    -- The constraints are empty (True), so they're trivially satisfied

end InputLinearSum

/-
Circuit that computes the weighted sum of binary values: Σ_i bits[i] * 2^i
Assumes the inputs are binary (0 or 1).
-/
namespace BinaryWeightedSum

-- Compute Σ_i bits[i] * 2^i and verify each bit is binary
def main (n : ℕ) (bits : Vector (Expression (F p)) n) : Circuit (F p) (Expression (F p)) := do
  let (sum, _) ← Circuit.foldlRange n ((0 : Expression (F p)), (1 : Expression (F p))) fun (sum, e2) i => do
    -- Ensure bits[i] is binary
    bits[i] * (bits[i] - (1 : Expression (F p))) === (0 : Expression (F p))
    let sum := sum + bits[i] * e2
    return (sum, e2 + e2)
  return sum

-- Specific version for our use case
omit [Fact (p > 2)] in
lemma fieldFromBits_empty_expr (bits : Vector (Expression (F p)) 0) (env : Environment (F p)) :
    fieldFromBits (Vector.map (Expression.eval env) bits) = 0 := by
  -- For a vector of length 0, fieldFromBits should return 0
  simp only [fieldFromBits, fromBits]
  -- Fin.foldl 0 returns the initial value 0
  simp only [Fin.foldl_zero]
  -- ↑0 = 0
  simp

-- Lemma: map and take commute for vectors
lemma Vector.map_take {α β : Type} {n : ℕ} (f : α → β) (xs : Vector α n) (i : ℕ) :
    (xs.map f).take i = (xs.take i).map f := by
  ext j hj
  simp only [Vector.getElem_map, Vector.getElem_take]



-- Helper lemma: The Fin.foldl maintains the invariant that the first component is the partial sum
-- and the second component is the current power of 2
omit [Fact (p > 2)] in
lemma foldl_pair_inv : ∀ (n : ℕ) (bits : Vector (Expression (F p)) n) (env : Environment (F p)),
    let result := Fin.foldl n (fun acc i ↦ (acc.1 + bits[i] * acc.2, acc.2 + acc.2)) (0, 1)
    Expression.eval env result.1 = fieldFromBits (Vector.map (Expression.eval env) bits) ∧
    Expression.eval env result.2 = (2^n : F p) := by
  intro n
  induction n with
  | zero =>
    intro bits env
    simp only [Fin.getElem_fin, Fin.foldl_zero, pow_zero]
    constructor
    · -- First component: Expression.eval env 0 = fieldFromBits empty_vector
      simp only [Expression.eval, fieldFromBits_empty_expr]
    · -- Second component: Expression.eval env 1 = 2^0 = 1
      simp only [Expression.eval]
  | succ n ih =>
    intro bits env
    -- Unfold the foldl for n+1
    simp only [Fin.foldl_succ_last]

    -- Get the inductive hypothesis for bits.pop
    have ih_spec := ih (bits.pop) env

    -- Key insight: the fold with castSucc is the same as fold on bits.pop
    have h_fold_eq : ∀ (init : Expression (F p) × Expression (F p)),
      Fin.foldl n (fun acc i ↦ (acc.1 + bits[i.castSucc] * acc.2, acc.2 + acc.2)) init =
      Fin.foldl n (fun acc i ↦ (acc.1 + bits.pop[i] * acc.2, acc.2 + acc.2)) init := by
      intro init
      congr 2
      funext acc i
      simp only [Fin.getElem_fin, Fin.coe_castSucc, Nat.add_one_sub_one, Vector.getElem_pop']
    -- Apply the fold equality
    rw [h_fold_eq]

    -- Now we can use the inductive hypothesis
    rcases ih_spec with ⟨ih1, ih2⟩

    constructor
    · -- First component
      simp only [Expression.eval, ih1, ih2, InputLinearSum.fieldFromBits_succ]
      congr
      · -- Goal: LHS = fieldFromBits ((Vector.map (Expression.eval env) bits).take n)
        -- We have ih1: LHS = fieldFromBits (Vector.map (Expression.eval env) bits.pop)
        -- We need to show these are equal
        trans (fieldFromBits (Vector.map (Expression.eval env) bits.pop))
        · exact ih1
        · -- Now show: fieldFromBits (Vector.map (Expression.eval env) bits.pop) = fieldFromBits ((Vector.map (Expression.eval env) bits).take n)
          congr 1
          simp only [add_tsub_cancel_right, le_add_iff_nonneg_right, zero_le, inf_of_le_left]
          rw [Vector.map_take]
          congr 1
          have n_eq : n + 1 - 1 = min n (n + 1) := by omega
          rw [n_eq]
          simp only [Vector.pop, Vector.take]
          congr 1
          · omega
          · ext
            · simp only [Array.size_pop, Vector.size_toArray, add_tsub_cancel_right,
              Array.take_eq_extract, Array.extract_eq_pop]
            · simp only [Array.getElem_pop, Vector.getElem_toArray, Array.take_eq_extract,
              Vector.size_toArray, add_tsub_cancel_right, Array.extract_eq_pop]
          · simp only [Array.size_pop, Vector.size_toArray, add_tsub_cancel_right,
            Array.take_eq_extract, Array.extract_eq_pop, le_add_iff_nonneg_right, zero_le,
            inf_of_le_left, heq_eq_eq]
      · simp only [circuit_norm]
        -- Goal: Expression.eval env bits[↑(Fin.last n)] = Expression.eval env bits[n]
        -- Both sides evaluate the same element of bits
        -- Fin.last n has value n, and the coercion ↑ preserves this
        -- So bits[↑(Fin.last n)] = bits[n]
        congr
    · -- Second component: 2^n + 2^n = 2^(n+1)
      simp only [Expression.eval, ih2]
      ring_nf
      -- We have the_fold.2 * 2 = 2^n * 2
      -- Since ih2 says the_fold.2 = 2^n, we can substitute
      congr 1

-- Lemma: BinaryWeightedSum.main computes fieldFromBits of its input
omit [Fact (p > 2)] in
lemma main_computes_fieldFromBits (n : ℕ) (bits : Vector (Expression (F p)) n) (offset : ℕ) (env : Environment (F p)) :
    Expression.eval env (Circuit.output (main n bits) offset) = fieldFromBits (bits.map (Expression.eval env)) := by
  simp only [main, circuit_norm]
  -- Use the helper lemma
  have h := foldl_pair_inv n bits env
  -- Extract the first component
  exact h.1

def circuit (n : ℕ) : GeneralFormalCircuit (F p) (fields n) field where
  main input := main n input

  localLength _ := 0
  localLength_eq := by
    simp only [circuit_norm, main]
    split_ifs <;> simp

  output input offset := Circuit.output (main n input) offset
  output_eq := by
    intros
    rfl

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input :=
    -- All inputs are binary
    ∀ i (hi : i < n), IsBool input[i]

  Spec input output :=
    -- All inputs are binary (enforced by constraints)
    (∀ i (hi : i < n), IsBool input[i])
    -- Output equals the weighted sum of bits
    ∧ output = fieldFromBits input

  soundness := by
    simp only [GeneralFormalCircuit.Soundness]
    intros offset env input_var input h_input_eval h_constraints
    simp only[main, circuit_norm] at h_constraints ⊢
    constructor
    · -- Prove all inputs are binary
      intro i hi
      -- The constraints enforce input_var[i] * (input_var[i] - 1) = 0
      have h_constraint := h_constraints ⟨i, hi⟩
      simp only [circuit_norm] at h_constraint
      -- h_constraint : Expression.eval env input_var[i] * (Expression.eval env input_var[i] + -1) = 0
      -- We need to convert this to the standard form x * (x - 1) = 0
      have h_binary : Expression.eval env input_var[i] * (Expression.eval env input_var[i] - 1) = 0 := by
        simp only [sub_eq_add_neg]
        assumption
      -- Now apply IsBool.of_sq_sub_sq
      have h_eq : input[i] = Expression.eval env input_var[i] := by
        rw [← h_input_eval]
        simp only [ProvableType.eval_fields]
        simp only [Vector.getElem_map]
      rw [h_eq]
      exact IsBool.iff_mul_sub_one.mpr h_binary
    · rw[← h_input_eval]
      -- We need to prove that the output of the circuit equals fieldFromBits of the input
      -- The circuit computes Σ_i input_var[i] * 2^i using foldlRange
      -- We can use the lemma main_computes_fieldFromBits
      have h_lemma := main_computes_fieldFromBits n input_var offset env
      simp only [ProvableType.eval_fields]
      rw [← h_lemma]
      -- Now we need to show that Fin.foldl equals Circuit.output (main n input_var) offset
      -- This requires understanding how Circuit.foldlRange relates to Fin.foldl
      simp only [Circuit.output, main, circuit_norm]
      -- The simp unfolded the definitions and proved the equality

  completeness := by
    simp only [GeneralFormalCircuit.Completeness]
    intros offset env input_var h_witness_extends input h_input_eval h_assumptions
    -- We need to show that when inputs are binary, the constraints can be satisfied
    -- The constraints are: for each i, bits[i] * (bits[i] - 1) = 0
    -- This is satisfied when bits[i] is binary (0 or 1)

    -- We need to prove that the constraints from main hold
    -- The main function uses foldlRange to add constraints bits[i] * (bits[i] - 1) = 0
    simp only [Circuit.ConstraintsHold.Completeness, main]

    -- The constraints come from the foldlRange in main
    -- Each iteration adds a constraint bits[i] * (bits[i] - 1) = 0
    -- We know from h_assumptions that each input[i] is binary (0 or 1)

    -- For binary values, x * (x - 1) = 0 always holds:
    -- If x = 0: 0 * (0 - 1) = 0 * (-1) = 0
    -- If x = 1: 1 * (1 - 1) = 1 * 0 = 0

    -- Apply the constraint satisfaction
    simp only [circuit_norm]

    -- Now we need to prove that for each i: input_var[i] * (input_var[i] - 1) = 0
    rintro ⟨ i, h_i ⟩
    simp only [circuit_norm]
    specialize h_assumptions i h_i
    rw [← h_input_eval] at h_assumptions

    -- We need to show: Expression.eval env input_var[i] * (Expression.eval env input_var[i] - 1) = 0
    -- We know from h_assumptions that (eval env input_var)[i] is binary

    -- Use the fact that evaluating a vector gives us a vector of evaluations
    -- For fields n, eval env input_var is a Vector (F p) n
    have h_eval_eq : (eval env input_var)[i] = Expression.eval env input_var[i] := by
      -- For fields n, eval is defined as mapping Expression.eval over the vector
      -- So (eval env input_var)[i] = (input_var.map (Expression.eval env))[i]
      -- which equals Expression.eval env input_var[i]
      simp only [ProvableType.eval_fields]
      simp only [Vector.getElem_map]

    rw[h_eval_eq] at h_assumptions

    -- For binary values, x * (x - 1) = 0
    cases h_assumptions with
    | inl h => -- value = 0
      rw [h]
      ring_nf
    | inr h => -- value = 1
      rw [h]
      ring_nf

end BinaryWeightedSum

/-
Circuit that decomposes a number into binary representation and verifies each bit.
-/
namespace OutputBitsDecomposition

-- Witness output bits and verify they are binary
def main (nout : ℕ) (lin : Expression (F p)) : Circuit (F p) (Vector (Expression (F p)) nout) := do
  -- Witness output bits
  let out ← witnessVector nout fun env =>
    fieldToBits nout (lin.eval env)

  -- Use BinaryWeightedSum subcircuit to compute the sum and verify bits are binary
  let lout ← BinaryWeightedSum.circuit nout out

  -- Ensure the sum is correct
  lin === lout

  return out

def circuit (nout : ℕ) (_ : 2^nout < p) :
    FormalCircuit (F p) field (fields nout) where
  main input := main nout input

  localLength _ := nout
  localLength_eq := by
    intro offset
    simp only [circuit_norm, main]
    simp only [BinaryWeightedSum.circuit]
    simp

  output _ i := varFromOffset (fields nout) i
  output_eq := by simp +arith [circuit_norm, main]

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := input.val < 2^nout

  Spec input output :=
    -- All outputs are binary
    (∀ i (hi : i < nout), IsBool output[i])
    -- Output bits represent the input value
    ∧ fieldFromBits output = input

  soundness := by
    intros input h_assumptions offset env h_input_eval h_constraints
    intro h_constraints_hold
    -- OutputBitsDecomposition enforces:
    -- 1. Each output bit is binary (0 or 1)
    -- 2. The sum of output bits equals the input

    -- Extract the constraints from h_constraints_hold
    simp only [circuit_norm, main, BinaryWeightedSum.circuit, subcircuit_norm, Gadgets.Equality.circuit] at h_constraints_hold

    -- The constraints now come from BinaryWeightedSum subcircuit:
    -- 1. For each i: out[i] * (out[i] - 1) = 0 (binary constraint)
    -- 2. Plus our assertEq: lin = lout (sum constraint)

    constructor
    · -- First: prove all outputs are binary
      intro i hi
      -- BinaryWeightedSum enforces out[i] * (out[i] - 1) = 0 which means IsBool
      -- The output is varFromOffset which maps to the witnessed variables
      simp only [ElaboratedCircuit.output]
      simp only [varFromOffset, eval, fromVars, fromElements, toVars]
      simp only [toElements, size, fields]
      simp only [Vector.getElem_map, Vector.getElem_mapRange]
      -- The constraint tells us the witnessed variables are binary
      have h_binary_all := h_constraints_hold.1.1
      exact h_binary_all i hi

    · -- Second: prove fieldFromBits output = input
      -- BinaryWeightedSum.Spec says: lout = fieldFromBits out
      -- We have the constraint: lin = lout
      -- Therefore: fieldFromBits output = lout = lin = input

      -- First, simplify the output
      simp only [ElaboratedCircuit.output]
      simp only [varFromOffset, eval, fromVars, fromElements, toVars]

      -- From h_constraints_hold, we have:
      -- 1. All bits are binary (h_constraints_hold.1)
      -- 2. BinaryWeightedSum output = fieldFromBits of the bits (h_constraints_hold.2.1)
      -- 3. input = BinaryWeightedSum output (h_constraints_hold.2.2)

      -- Extract the parts of the constraint
      have ⟨h_binary_and_sum, h_eq⟩ := h_constraints_hold
      have ⟨h_binary, h_sum⟩ := h_binary_and_sum

      -- First simplify the goal
      simp only [toElements, size, fields]
      -- Now we need to show: fieldFromBits(...) = env
      -- We have the chain: fieldFromBits(...) = BinaryWeightedSum output = offset = env
      -- Work backwards from the goal
      rw [← h_sum]
      -- Now we need: BinaryWeightedSum output = env
      rw [← h_eq]
      -- Now we need: Expression.eval h_assumptions offset = env
      -- h_input_eval gives us this (after expanding eval)
      simp only [eval, fromVars, fromElements, toVars] at h_input_eval
      -- For field type, this should be the identity
      exact h_input_eval

  completeness := by
    intros witness_offset env lin_var h_witness_extends lin_value h_lin_eval h_assumptions
    -- We can always witness the binary decomposition of the input
    -- The circuit witnesses out = fieldToBits(input)
    -- This satisfies all constraints:
    -- 1. Binary constraints: fieldToBits produces binary values
    -- 2. Sum constraint: fieldFromBits(fieldToBits(x)) = x (when x < 2^nout)
    simp only [circuit_norm, main, BinaryWeightedSum.circuit, subcircuit_norm, Gadgets.Equality.circuit]

    -- The witnessing uses fieldToBits which:
    -- 1. Produces binary values
    -- 2. Has the property fieldFromBits(fieldToBits(x)) = x

    -- This proof requires showing that:
    -- 1. fieldToBits produces binary values (for BinaryWeightedSum constraints)
    -- 2. fieldFromBits(fieldToBits(input)) = input (for the assertEq)

    -- h_assumptions gives us that lin_value.val < 2^nout
    constructor
    · -- First: show the witnessed bits are binary
      intro i hi
      -- The circuit witnesses out[i] = fieldToBits(lin_value)[i]
      -- We need to show this is binary
      -- The key property is that fieldToBits produces values in {0, 1}

      -- h_witness_extends tells us that the environment extends the witness vector at offset witness_offset
      -- The witness vector is fieldToBits nout (lin.eval env) from the main function
      have h_witness : env.get (witness_offset + i) =
                       (fieldToBits nout (Expression.eval env lin_var))[i] := by
        -- h_witness_extends contains ExtendsVector for the witness operation
        simp only [Environment.UsesLocalWitnessesCompleteness] at h_witness_extends
        have ⟨h_extends, _⟩ := h_witness_extends
        simp only [Environment.ExtendsVector] at h_extends
        exact h_extends ⟨i, hi⟩

      rw [h_witness]
      -- Now apply the theorem about fieldToBits producing binary values
      have h_binary := fieldToBits_bits (i := i) hi (x := Expression.eval env lin_var)
      cases h_binary with
      | inl h => left; exact h
      | inr h => right; exact h

    · -- Second: show input = BinaryWeightedSum output
      -- BinaryWeightedSum computes fieldFromBits of the witnessed bits
      -- The witnessed bits are fieldToBits(input)
      -- So we need: input = fieldFromBits(fieldToBits(input))

      -- The BinaryWeightedSum main function evaluates to fieldFromBits of its input vector
      -- Its input vector is Vector.mapRange nout (fun i => var ⟨witness_offset + i⟩)
      -- When evaluated, this gives us the witness values

      -- First, let's understand what BinaryWeightedSum.main computes
      -- It computes Σ_i bits[i] * 2^i = fieldFromBits bits

      -- The expression we need to prove equal to lin_var is:
      -- BinaryWeightedSum.main nout (Vector.mapRange nout fun i ↦ var { index := witness_offset + i })

      -- When evaluated, the var expressions give us the witness values
      have h_witness_vec : Vector.map (Expression.eval env)
                           (Vector.mapRange nout fun i ↦ var { index := witness_offset + i }) =
                           fieldToBits nout (Expression.eval env lin_var) := by
        rw [Vector.ext_iff]
        intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange]
        -- Use h_witness_extends to get the witness value
        simp only [Environment.UsesLocalWitnessesCompleteness] at h_witness_extends
        have ⟨h_extends, _⟩ := h_witness_extends
        simp only [Environment.ExtendsVector] at h_extends
        simp only [Expression.eval]
        exact h_extends ⟨i, hi⟩

      -- Now we need to prove that the evaluation of lin_var equals the evaluation of BinaryWeightedSum output
      -- The LHS is Expression.eval env lin_var = lin_value
      -- The RHS is the output of BinaryWeightedSum.main applied to the witness vector

      -- Let's think about what BinaryWeightedSum.main computes:
      -- It takes a vector of bits and computes Σ_i bits[i] * 2^i
      -- When applied to fieldToBits(lin_value), it should return lin_value

      -- First, let's use h_lin_eval to replace the LHS
      have h_lhs : Expression.eval env lin_var = lin_value := h_lin_eval
      rw [h_lhs]

      -- Now we need to show that the RHS also equals lin_value
      -- The RHS is the evaluation of BinaryWeightedSum.main on the witness vector
      -- The witness vector evaluates to fieldToBits nout lin_value (by h_witness_vec)

      -- To proceed, we need to use the lemma about what BinaryWeightedSum.main computes
      -- It computes fieldFromBits of its input vector

      -- The goal is: lin_value = Expression.eval env (BinaryWeightedSum.main ...)
      -- We know lin_value = Expression.eval env lin_var
      -- And the witness vector evaluates to fieldToBits nout lin_value

      -- Apply the lemma about BinaryWeightedSum.main
      have h_bws_output := BinaryWeightedSum.main_computes_fieldFromBits nout
                           (Vector.mapRange nout fun i ↦ var { index := witness_offset + i })
                           (witness_offset + nout) env

      -- Simplify the RHS using our lemma
      rw [h_bws_output]

      -- Now we need: lin_value = fieldFromBits (fieldToBits nout lin_value)
      -- This follows from fieldFromBits_fieldToBits with appropriate bounds

      -- We need lin_value < 2^nout for the theorem to apply
      -- This is given by h_assumptions
      have h_lt : lin_value.val < 2^nout := h_assumptions

      -- Now we use h_witness_vec and h_lhs to rewrite
      -- h_witness_vec tells us the witness vector equals fieldToBits nout (Expression.eval env lin_var)
      -- h_lhs tells us Expression.eval env lin_var = lin_value
      rw [h_lhs] at h_witness_vec

      -- Now we can rewrite the goal using h_witness_vec
      -- The goal has fieldFromBits (Vector.map ...) and h_witness_vec tells us this equals fieldToBits nout lin_value
      rw [h_witness_vec]

      -- Now the goal is: lin_value = fieldFromBits (fieldToBits nout lin_value)
      -- This follows from fieldFromBits_fieldToBits (with symmetry)
      exact (fieldFromBits_fieldToBits h_lt).symm

end OutputBitsDecomposition

/-
template BinSum(n, ops) {
    var nout = nbits((2**n - 1)*ops);
    signal input in[ops][n];
    signal output out[nout];

    var lin = 0;
    var lout = 0;

    var k;
    var j;
    var e2;

    // Calculate input linear sum
    e2 = 1;
    for (k=0; k<n; k++) {
        for (j=0; j<ops; j++) {
            lin += in[j][k] * e2;
        }
        e2 = e2 + e2;
    }

    // Calculate output bits
    e2 = 1;
    for (k=0; k<nout; k++) {
        out[k] <-- (lin >> k) & 1;

        // Ensure out is binary
        out[k] * (out[k] - 1) === 0;

        lout += out[k] * e2;

        e2 = e2+e2;
    }

    // Ensure the sum is correct
    lin === lout;
}
-/
-- n: number of bits per operand
-- ops: number of operands to sum
def main (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) (hnout : 2^(nbits ((2^n - 1) * ops)) < p)
    (inp : BinSumInput n ops (Expression (F p))) : Circuit (F p) (Vector (Expression (F p)) (nbits ((2^n - 1) * ops))) := do
  let nout := nbits ((2^n - 1) * ops)

  -- Use InputLinearSum subcircuit to calculate the sum
  let lin ← subcircuit (InputLinearSum.circuit n ops hops) inp

  -- Use OutputBitsDecomposition subcircuit to decompose into bits
  let out ← subcircuit (OutputBitsDecomposition.circuit nout hnout) lin

  return out

-- n: number of bits per operand
-- ops: number of operands to sum
def circuit (n ops : ℕ) [hn : NeZero n] (hops : 0 < ops) (hnout : 2^(nbits ((2^n - 1) * ops)) < p) :
    FormalCircuit (F p) (BinSumInput n ops) (fields (nbits ((2^n - 1) * ops))) where
  main input := main n ops hops hnout input

  localLength _ := nbits ((2^n - 1) * ops)
  localLength_eq := by
    intros
    simp only [circuit_norm, main, subcircuit]
    -- The localLength of InputLinearSum is 0
    -- The localLength of OutputBitsDecomposition is nout
    simp only [InputLinearSum.circuit, OutputBitsDecomposition.circuit]
    simp only [zero_add]

  output _ i := varFromOffset (fields (nbits ((2^n - 1) * ops))) i

  output_eq := by
    intros input offset
    simp only [circuit_norm, main, subcircuit]
    -- The output of the main circuit is the output of OutputBitsDecomposition
    simp only [OutputBitsDecomposition.circuit]
    rfl

  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input :=
    -- All inputs are binary
    ∀ j k (hj : j < ops) (hk : k < n), IsBool input[j][k]

  Spec input output :=
    let nout := nbits ((2^n - 1) * ops)
    -- All outputs are binary
    (∀ i (hi : i < nout), IsBool output[i])
    -- Sum of inputs equals the value represented by output bits
    ∧ fieldFromBits output =
        Fin.foldl ops (fun sum (j : Fin ops) =>
          sum + fieldFromBits input[j]) (0 : F p)

  soundness := by
    intros input h_assumptions offset env h_input_eval h_circuit_constraints
    -- Extract what h_circuit_constraints says
    intro h_constraints_hold
    -- h_circuit_constraints contains our assumptions about the input (they are binary)
    -- h_constraints_hold contains the fact that circuit constraints hold

    -- We need to analyze what constraints are generated by our main circuit
    simp only [circuit_norm, main, subcircuit, subcircuit_norm] at h_constraints_hold
    -- Unfold the subcircuit definitions to access their specs
    simp only [InputLinearSum.circuit, OutputBitsDecomposition.circuit] at h_constraints_hold

    -- Now we can see the constraints from both subcircuits
    -- The constraints are:
    -- 1. From InputLinearSum: none (it just computes)
    -- 2. From OutputBitsDecomposition: binary constraints and sum constraint

    -- If the subcircuits were sound, we would have:
    -- - InputLinearSum.Spec: its output equals the sum of inputs
    -- - OutputBitsDecomposition.Spec: outputs are binary and represent the input

    -- Extract the two parts of the constraint
    obtain ⟨h_input_sum, h_output_decomp⟩ := h_constraints_hold

    -- We need to prove the output specification
    constructor
    · -- First: all outputs are binary
      intro i hi
      -- The output is varFromOffset at position offset + input
      simp only [varFromOffset, eval, fromVars, fromElements, toVars, fields, size]
      -- Apply the binary constraint from OutputBitsDecomposition
      -- First we need to prove that the sum is less than 2^nbits((2^n - 1) * ops)
      have h_sum_bound : (Expression.eval h_assumptions ((InputLinearSum.main n ops offset).output input)).val <
                         2^(nbits ((2^n - 1) * ops)) := by
        -- First we need to prove that inputs are binary for h_input_sum
        have h_inputs_binary_local : ∀ j k (hj : j < ops) (hk : k < n), IsBool (eval h_assumptions offset)[j][k] := by
          intro j k hj hk
          rw [h_input_eval]
          exact h_circuit_constraints j k hj hk
        -- Apply InputLinearSum spec to know what the output equals
        have h_sum_val := h_input_sum h_inputs_binary_local
        -- Use our lemma about sum bounds
        apply sum_bound_of_binary_inputs hops hnout (eval h_assumptions offset) h_inputs_binary_local
        exact h_sum_val
      have h_binary := (h_output_decomp h_sum_bound).1 i hi
      simp only [varFromOffset] at h_binary
      exact h_binary

    · -- Second: the sum property
      -- We know inputs are binary from h_circuit_constraints
      have h_inputs_binary : ∀ j k (hj : j < ops) (hk : k < n), IsBool (eval h_assumptions offset)[j][k] := by
        intro j k hj hk
        rw [h_input_eval]
        exact h_circuit_constraints j k hj hk

      -- Apply InputLinearSum spec with binary inputs
      have h_lin_sum := h_input_sum h_inputs_binary

      -- Apply OutputBitsDecomposition spec
      -- We need the same sum bound as before
      have h_sum_bound : (Expression.eval h_assumptions ((InputLinearSum.main n ops offset).output input)).val <
                         2^(nbits ((2^n - 1) * ops)) := by
        -- Use our lemma about sum bounds
        apply sum_bound_of_binary_inputs hops hnout (eval h_assumptions offset) h_inputs_binary
        exact h_lin_sum
      have h_output_sum := (h_output_decomp h_sum_bound).2

      -- Chain the equalities
      -- The goal is about ElaboratedCircuit.output which is varFromOffset
      simp only [ElaboratedCircuit.output]
      -- Now we need to connect this with our hypotheses
      -- h_output_sum tells us about fieldFromBits of the output
      have h_output_eq : fieldFromBits (eval h_assumptions (varFromOffset (fields (nbits ((2^n - 1) * ops))) input)) =
                         fieldFromBits (Vector.map (Expression.eval h_assumptions)
                           (varFromOffset (fields (nbits ((2^n - 1) * ops))) (input + 0))) := by
        congr 1
      rw [h_output_eq, h_output_sum, h_lin_sum, h_input_eval]

  completeness := by
    intros witness_offset env inputs_var h_witness_extends inputs_value
    -- We need to show that when inputs are binary, the circuit constraints can be satisfied
    -- The completeness follows from:
    -- 1. InputLinearSum has no constraints, so it's trivially complete
    -- 2. OutputBitsDecomposition witnesses the correct binary decomposition

    -- The circuit constraints come from the subcircuits
    simp only [circuit_norm, main, subcircuit, subcircuit_norm]
    simp only [InputLinearSum.circuit, OutputBitsDecomposition.circuit]

    -- We have implications to handle
    intro h_inputs_eval h_inputs_binary
    -- Now we need to prove the conjunction
    constructor
    · -- First part: inputs remain binary after evaluation
      intro j k hj hk
      rw [h_inputs_eval]
      exact h_inputs_binary j k hj hk

    · -- Second part: OutputBitsDecomposition completeness
      -- We need to prove that the sum is less than 2^nbits((2^n - 1) * ops)
      -- We have the sum from InputLinearSum
      have h_sum_eq : Expression.eval env ((InputLinearSum.main n ops inputs_var).output witness_offset) =
                       Fin.foldl ops (fun sum j => sum + fieldFromBits (eval env inputs_var)[j]) 0 := by
        -- This follows from InputLinearSum.Spec
        -- We need to extract the relevant part from h_witness_extends
        simp only [subcircuit_norm, main, circuit_norm, InputLinearSum.circuit] at h_witness_extends
        -- h_witness_extends tells us that InputLinearSum.circuit is satisfied
        -- Extract the first part of the conjunction which gives us the InputLinearSum.Spec
        have h_input_spec := h_witness_extends.1
        -- We need to prove the inputs are binary to apply h_input_spec
        have h_inputs_binary_eval : ∀ j k (hj : j < ops) (hk : k < n), IsBool (eval env inputs_var)[j][k] := by
          intro j k hj hk
          rw [h_inputs_eval]
          exact h_inputs_binary j k hj hk
        -- Apply the spec
        exact h_input_spec h_inputs_binary_eval
      -- Now apply our lemma
      have h_binary_eval : ∀ j k (hj : j < ops) (hk : k < n), IsBool (eval env inputs_var)[j][k] := by
        intro j k hj hk
        rw [h_inputs_eval]
        exact h_inputs_binary j k hj hk
      apply sum_bound_of_binary_inputs hops hnout (eval env inputs_var) h_binary_eval
      exact h_sum_eq

end BinSum

end Circomlib
