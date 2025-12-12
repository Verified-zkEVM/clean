import Clean.Circuit
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Bits
import Clean.Utils.Fin
import Clean.Utils.Vector
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean
import Clean.Circomlib.Bitify

-- set_option diagnostics true

namespace Circomlib
open Utils.Bits
open Expression
-- open ProvableType
variable {p : ℕ} [Fact p.Prime]

-- Define a 2D vector type for BinSub inputs
-- Represents 2 operands, each with n bits
-- This is a vector of 2 elements, where each element is a vector of n field elements
@[reducible]
def BinSubInput (n : ℕ) := ProvableVector (fields n) 2

-- Instance for NonEmptyProvableType for fields when n > 0
instance {n : ℕ} [hn : NeZero n] : NonEmptyProvableType (fields n) where
  nonempty := Nat.pos_of_ne_zero hn.out

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/binsub.circom

The BinSub template takes two binary numbers as input and outputs their difference in binary form.
The circuit computes: (in[0] + 2^n) - in[1] = out + aux*2^n
where aux is the borrow bit.
Note that the input bits must be guaranteed to be binary (0 or 1) by the caller.
The circuit ensures that:
1. All output bits are binary (0 or 1)
2. The aux bit is binary (0 or 1)
3. The equation (in[0] + 2^n) - in[1] = out + aux*2^n holds
-/

def nbits (a : ℕ) : ℕ :=
  if a = 0 then 1 else Nat.log2 a + 1

namespace BinSub

def inputLinearSub
  (n : ℕ)
  (inp : BinSubInput n (Expression (F p)))
  : Expression (F p) :=
  -- Calculate input linear sub
  Fin.foldl n (fun lin k => lin + inp[0][k] * (2^k.val : F p) - (inp[1][k] * (2^k.val : F p))) (2^n : F p)

-- Lemma showing that evaluating the main circuit computes the correct sub
lemma inputLinearSub_eval_eq_sub {n : ℕ} [hn : NeZero n]
  (env : Environment (F p))
  (input : Var (BinSubInput n) (F p))
  (input_val : BinSubInput n (F p))
  (h_eval : ProvableType.eval env input = input_val) :
    Expression.eval env (inputLinearSub n input) =
    fieldFromBits input_val[0] + 2^n - fieldFromBits input_val[1] := by

    -- Step 1: The circuit evaluation computes the difference
    simp only [inputLinearSub, circuit_norm, eval_foldl]

    -- Step 2: Replace Expression.eval env input[j][k] with input_val[j][k]
    simp only [ProvableType.getElem_eval_fields, getElem_eval_vector, h_eval]
    -- Step 3: Split the Fin.foldl into its components
    have hh := Fin.foldl_split_mul_add_distrib (α:=F p) (fun j k => input_val[j][Fin.val k]) (fun i => 2^i) (n:=n)
    simp_all only [Fin.getElem_fin, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ]
    -- Step 4: Conclude the proof by reducing the fieldFromBits function to a fold
    simp [fieldFromBits_as_sum]

lemma foldl_powerof2
  {n : ℕ}
  (env : Environment (F p))
  (f : Expression (F p) × Expression (F p) → ℕ → Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i ↦ (f acc i, acc.2 + acc.2)) (0, 1)).2 = (2^n : F p) := by
      induction n with
      | zero => simp_all only [Fin.foldl_zero, pow_zero, circuit_norm]
      | succ n' ihn' => simp_all +arith [Fin.foldl_succ_last, circuit_norm, two_mul, pow_succ, mul_comm]

lemma foldl_explicit
  {n : ℕ}
  {m : ℕ}
  (h_le : m <= n)
  (env : Environment (F p))
  (offset : ℕ)
  (h_bool : ∀ i ≤ n, env.get (offset + i) = 0 ∨ env.get (offset + i) + (-1) = 0) :
    Fin.foldl m (fun acc k ↦ acc + env.get (offset + k) * 2^k.val) 0 =
    Expression.eval env (Fin.foldl m (fun acc i ↦ (acc.1 + var { index := offset + i } * acc.2, acc.2 + acc.2)) (0, 1)).1 := by
      induction m with
      | zero => simp_all +arith [Expression.eval]
      | succ m' ihm' =>
        specialize (ihm' (Nat.le_of_add_right_le h_le))
        conv_lhs => rw [Fin.foldl_succ_last]
        conv_rhs => rw [Fin.foldl_succ_last]
        simp_all +arith [circuit_norm]
        cases h_bool m' (Nat.le_of_add_right_le h_le) with
        | inl h0 => right; assumption
        | inr h1 => left; rw [foldl_powerof2 env (n:=m') (fun acc i => acc.1 + var { index := offset + ↑i } * acc.2)]

-- lemma sub_bound_of_binary_inputs
--   {n : ℕ}
--   (hnout : 2^(n+1) < p)
--   (input_val : BinSubInput n (F p))
--   (h_binary : ∀ j k (hj : j < 2) (hk : k < n), IsBool input_val[j][k]) :
--     (fieldFromBits input_val[0]).val + 2^n - (fieldFromBits input_val[1]).val < 2^n := by
--     -- Each input[j] is n-bit binary, so fieldFromBits inputs[j] ≤ 2^n - 1
--     -- The sum of ops such numbers is at most 2 * (2^n - 1)
--     -- We need to show this is < 2^(nbits(2 * (2^n - 1)))

--     -- First, bound each individual fieldFromBits
--     have h_individual_bound : ∀ j (hj : j < 2), (fieldFromBits input_val[j]).val ≤ 2^n - 1 := by
--       intro j hj
--       -- Use the fieldFromBits bound
--       have h_lt := fieldFromBits_lt input_val[j] (h_binary j · hj)
--       -- We have fieldFromBits inputs[j] < 2^n, so its value is ≤ 2^n - 1
--       omega

--     have h_log_bound (n : ℕ) : 2 * (2 ^ n - 1) < 2 ^ nbits ((2 ^ n - 1) * 2) := by
--       simp only [nbits]
--       rw [mul_comm]
--       split_ifs with h <;> simp [h, Nat.lt_log2_self]

--     -- The sum is bounded by ops * (2^n - 1)
--     have h_sum_bound : (Fin.foldl 2 (fun sum j => sum + fieldFromBits input_val[j]) 0).val ≤ 2 * (2^n - 1) := by
--       -- Apply our general lemma about foldl sum bounds
--       apply Fin.foldl_sum_val_bound (fun j => fieldFromBits input_val[j]) (2^n - 1)
--       · -- Prove each element is bounded
--         intro j
--         exact h_individual_bound j j.isLt
--       · -- Prove no overflow: ops * (2^n - 1) < p
--         -- This follows from hnout and the definition of nbits
--         apply Nat.lt_trans (h_log_bound _) hnout

--     -- Apply the bound we just proved
--     apply Nat.lt_of_le_of_lt h_sum_bound (h_log_bound n)

/-
template BinSub(n) {
    signal input in[2][n];
    signal output out[n];

    signal aux;

    var lin = 2**n;
    var lout = 0;

    var i;

    for (i=0; i<n; i++) {
        lin = lin + in[0][i]*(2**i);
        lin = lin - in[1][i]*(2**i);
    }

    for (i=0; i<n; i++) {
        out[i] <-- (lin >> i) & 1;

        // Ensure out is binary
        out[i] * (out[i] - 1) === 0;

        lout = lout + out[i]*(2**i);
    }

    aux <-- (lin >> n) & 1;
    aux*(aux-1) === 0;
    lout = lout + aux*(2**n);

    // Ensure the sum
    lin === lout;
}
-/
-- n: number of bits per operand
def main (n : ℕ) [NeZero n] (inp : BinSubInput n (Expression (F p))) := do
  -- Calculate input linear sum: lin = 2^n + in[0] - in[1]
  let lin := Fin.foldl n (fun lin i =>
      let e2 : Expression (F p) := (2^i.val : F p)
      lin + inp[0][i] * e2 - inp[1][i] * e2)
    (2^n : F p)

  -- Witness output bits
  let out ← witnessVector n fun env =>
    fieldToBits n (lin.eval env)

  -- Witness aux bit
  let aux ← witness fun env =>
    let lin_val := lin.eval env
    -- Extract the nth bit (borrow bit)
    if (lin_val.val / (2^n)) % 2 = 1 then (1 : F p) else (0 : F p)

  -- Calculate output linear sum and constrain bits
  let (lout, _) ← Circuit.foldlRange n ((0 : Expression (F p)), (1 : Expression (F p))) fun (lout, e2) i => do
    -- Ensure out[i] is binary
    out[i] * (out[i] - (1 : Expression (F p))) === (0 : Expression (F p))
    let lout := lout + out[i] * e2
    return (lout, e2 + e2)

  -- Ensure aux is binary
  aux * (aux - (1 : Expression (F p))) === (0 : Expression (F p))

  -- Add aux contribution to lout
  let lout := lout + aux * ((2^n : F p) : Expression (F p))

  -- Ensure the equation holds
  lin === lout

  return out

-- n: number of bits per operand
def circuit (n : ℕ) [hn : NeZero n]
  -- [NonEmptyProvableType (fields n)]
  (hnout : 2^(n+1) < p) : FormalCircuit (F p) (BinSubInput n) (fields n) where
  main input := main n input

  localLength _ := n+1
  localLength_eq := by simp [main, circuit_norm]

  output _ i := varFromOffset (fields n) i

  output_eq := by intros input offset; rfl

  subcircuitsConsistent := by simp +arith [main, circuit_norm]

  Assumptions input :=
    -- All inputs are binary
    ∀ j i (hj : j < 2) (hi : i < n), IsBool input[j][i]

  Spec input output :=
    -- All output bits are binary
    (∀ i (hi : i < n), IsBool output[i])
    -- The equation (in[0] + 2^n) - in[1] = out + aux*2^n holds
    -- where aux is either 0 or 1 (the borrow bit)
    ∧ ∃ aux : F p, IsBool aux ∧
        fieldFromBits input[0] + (2^n : F p) - fieldFromBits input[1] =
          fieldFromBits output + aux * (2^n : F p)

  soundness := by
    intros offset env input input_val h_input_eval h_assumptions h_constraints_hold

    -- We need to analyze what constraints are generated by our main circuit
    simp only [circuit_norm, main] at *

    -- Extract the three parts of the constraint
    obtain ⟨h_zero_prod, h_output_binary, h_output_sum ⟩ := h_constraints_hold

    constructor
    . intros i h_lt
      have h_nil : (env.get (offset + i)) = 0 ∨ (env.get (offset + i) + (-1)) = 0 := mul_eq_zero.mp (h_zero_prod ⟨i, h_lt⟩)
      cases h_nil with
      | inl hl =>
          rw [hl]
          simp_all only [IsBool, id_eq, mul_eq_zero, zero_ne_one, or_false]
      | inr hr =>
          have h_tmp : env.get (offset + i) = 1 := by (rw [add_eq_zero_iff_eq_neg, neg_neg] at hr; exact hr)
          rw [h_tmp]
          simp_all only [IsBool, id_eq, mul_eq_zero, add_neg_cancel, one_ne_zero, or_true]
    . use env.get (offset + n)
      constructor
      . have h_nil : (env.get (offset + n)) = 0 ∨ (env.get (offset + n) + (-1))  = 0 := mul_eq_zero.mp h_output_binary
        cases h_nil with
        | inl hl =>
            rw [hl]
            simp_all only [IsBool, id_eq, mul_eq_zero, zero_ne_one, or_false]
        | inr hr =>
            have h_tmp : env.get (offset + n) = 1 := by (rw [add_eq_zero_iff_eq_neg, neg_neg] at hr; exact hr)
            rw [h_tmp]
            simp_all only [IsBool, id_eq, mul_eq_zero, add_neg_cancel, one_ne_zero, or_true]
      . rw [Vector.map_mapRange]
        simp_all +arith [fieldFromBits_as_sum,Vector.getElem_mapRange,circuit_norm]

        have h_bool : ∀ i ≤ n, env.get (offset + ↑i) = 0 ∨ env.get (offset + ↑i) + -1 = 0 := by
          intros i h_le
          apply Nat.lt_or_eq_of_le at h_le
          cases h_le with
          | inl hlt => apply h_zero_prod ⟨i, hlt⟩
          | inr heq => simp_all +arith [add_comm]

        have h_foldl_ev := @foldl_explicit p _ n n (le_refl n) env offset h_bool

        simp +arith [<-h_foldl_ev] at h_output_sum
        rw [<-h_output_sum]
        rw [eval_foldl]
        simp [circuit_norm, <-h_input_eval]
        have hh := Fin.foldl_split_mul_add_distrib (α:=F p) (fun j k => input_val[j][Fin.val k]) (fun i => 2^i) (n:=n)
        conv_rhs =>
          arg 2
          intro acc i
          simp only [Finset.sum_sub_distrib, add_sub, add_comm, add_assoc]
          simp only [ProvableType.getElem_eval_fields,eval_vector_eq_get]

        simp [h_input_eval]

        simp_all
        conv_lhs => rw [<-hh]
        simp +arith [<-add_assoc]

        . intros e i
          simp [*,circuit_norm]

  completeness := by
    sorry
end BinSub

end Circomlib
