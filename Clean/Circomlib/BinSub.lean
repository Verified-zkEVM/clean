import Clean.Circuit
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Bits
import Clean.Utils.Fin
import Clean.Utils.Vector
import Clean.Gadgets.Bits
import Clean.Gadgets.Boolean
import Clean.Circomlib.Bitify

namespace Circomlib
open Utils.Bits
open Expression
variable {p : ℕ} [Fact p.Prime]

-- Define a 2D vector type for BinSub inputs
-- Represents 2 operands, each with n bits
-- This is a vector of 2 elements, where each element is a vector of n field elements
@[reducible]
def BinSubInput (n : ℕ) := ProvableVector (fields n) 2

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
namespace BinSub
-- Instance for NonEmptyProvableType for fields when n > 0
instance {n : ℕ} [hn : NeZero n] : NonEmptyProvableType (fields n) where
  nonempty := Nat.pos_of_ne_zero hn.out

def nbits (a : ℕ) : ℕ :=
  if a = 0 then 1 else Nat.log2 a + 1

def inputLinearSub (n : ℕ) (inp : BinSubInput n (Expression (F p))) : Expression (F p) :=
  Fin.foldl n (fun lin k => lin + inp[0][k] * (2^k.val : F p) - (inp[1][k] * (2^k.val : F p))) (2^n : F p)

-- Lemma: evaluating `inputLinearSub` corresponds to the circuit's desired output
lemma inputLinearSub_eval_eq_sub {n : ℕ} [hn : NeZero n] (env : Environment (F p)) (input : Var (BinSubInput n) (F p)) (input_val : BinSubInput n (F p)) (h_eval : ProvableType.eval env input = input_val) :
    Expression.eval env (inputLinearSub n input) =
      fieldFromBits input_val[0] + 2^n - fieldFromBits input_val[1] := by
  simp only [inputLinearSub, circuit_norm, eval_foldl]
  simp only [ProvableType.getElem_eval_fields, getElem_eval_vector, h_eval]
  have h_foldl_split := Fin.foldl_split_mul_add_distrib (α:=F p) (fun j k => input_val[j][Fin.val k]) (fun i => 2^i) (n:=n)
  simp_all only [Fin.getElem_fin, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ]
  simp [fieldFromBits_as_sum]

-- Lemma: (Left) folding `n` times over an accumulator that starts as `(0, 1)`, and doubling each time the right element of the accumulator, results in having `2^n` as the right element of the pair
lemma foldl_acc1_powerof2 {n : ℕ} (env : Environment (F p)) (f : Expression (F p) × Expression (F p) → ℕ → Expression (F p)) :
  Expression.eval env (Fin.foldl n (fun acc i ↦ (f acc i, acc.2 + acc.2)) (0, 1)).2 = (2^n : F p) := by
  induction n with
  | zero => simp_all only [Fin.foldl_zero, pow_zero, circuit_norm]
  | succ n' ihn' => simp_all +arith [Fin.foldl_succ_last, circuit_norm, two_mul, pow_succ, mul_comm]

-- Lemma: Conversion to bitstring equals the evaluation of the conversion with explicit accumulator and variables
lemma foldl_explicit {n : ℕ} {m : ℕ} (h_le : m <= n) (env : Environment (F p)) (offset : ℕ) (h_bool : ∀ i : Fin n, IsBool (env.get (offset + i))) :
  Fin.foldl m (fun acc k ↦ acc + env.get (offset + k) * 2^k.val) 0 =
    Expression.eval env (Fin.foldl m (fun acc i ↦ (acc.1 + var { index := offset + i } * acc.2, acc.2 + acc.2)) (0, 1)).1 := by
  induction m with
  | zero => simp_all +arith [Expression.eval]
  | succ m' ihm' =>
    specialize (ihm' (Nat.le_of_add_right_le h_le))
    conv_lhs => rw [Fin.foldl_succ_last]
    conv_rhs => rw [Fin.foldl_succ_last]
    simp_all +arith [circuit_norm]
    cases h_bool ⟨m', Nat.lt_of_add_one_le h_le⟩ with
    | inl h0 => rw [h0]; norm_num
    | inr h1 => rw [h1]; left; rw [foldl_acc1_powerof2 env (n:=m') (fun acc i => acc.1 + var { index := offset + ↑i } * acc.2)]

-- Lemma: The value of `in0 + 2^n - in1` in the field is equal to the integer arithmetic result `in0.val + 2^n - in1.val`, provided inputs are small enough (`< 2^n`) and the modulus `p` is large enough (`> 2^(n+1)`).
lemma lin_val_eq {p : ℕ} [Fact p.Prime] {n : ℕ} (in0 in1 : F p)
    (h0 : in0.val < 2^n) (h1 : in1.val < 2^n) (h_p : 2^(n+1) < p) :
    (in0 + (2^n : F p) - in1).val = in0.val + 2^n - in1.val := by
      have h_sub_eq : (in0 + 2^n - in1 : F p).val = (in0.val + 2^n - in1.val) % p := by
        norm_num [ ← ZMod.val_natCast ];
        rw [ Nat.cast_sub ] <;> norm_num;
        linarith;
      rw [ h_sub_eq, Nat.mod_eq_of_lt ( by rw [ pow_succ' ] at h_p; omega ) ]

-- Lemma: The value of `in0 + 2^n - in1` is bound by `2^(n+1)`.
lemma lin_bound {p : ℕ} [Fact p.Prime] {n : ℕ} (in0 in1 : F p)  (h0 : in0.val < 2^n) (h1 : in1.val < 2^n) (h_p : 2^(n+1) < p) :
  (in0 + (2^n : F p) - in1).val < 2^(n+1) := by
  rw [lin_val_eq in0 in1 h0 h1 h_p]; omega

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
def circuit (n : ℕ) [hn : NeZero n] (hnout : 2^(n+1) < p) :
  FormalCircuit (F p) (BinSubInput n) (fields n) where
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
    -- All inputs are binary
    (∀ j i (hj : j < 2) (hi : i < n), IsBool input[j][i])
    -- All output bits are binary
    ∧ (∀ i (hi : i < n), IsBool output[i])
    -- The equation (in[0] + 2^n) - in[1] = out + aux*2^n holds
    -- where aux is either 0 or 1 (the borrow bit)
    ∧ ∃ aux : F p, IsBool aux ∧
        fieldFromBits input[0] + (2^n : F p) - fieldFromBits input[1] =
          fieldFromBits output + aux * (2^n : F p)

  soundness := by
    intros i₀ env input input_val h_input_eval h_assumptions h_constraints_hold

    -- We need to analyze what constraints are generated by our main circuit
    simp only [circuit_norm, main] at *

    -- Extract the three parts of the constraint
    obtain ⟨ h_zero_prod, h_output_binary, h_output_sum ⟩ := h_constraints_hold

    constructor <;> try constructor
    . exact h_assumptions
    . intros i h_lt
      have h_nil : (env.get (i₀ + i)) = 0 ∨ (env.get (i₀ + i) + (-1)) = 0 := mul_eq_zero.mp (h_zero_prod ⟨i, h_lt⟩)
      cases h_nil with
      | inl hl =>
          rw [hl]
          simp_all only [IsBool, id_eq, mul_eq_zero, zero_ne_one, or_false]
      | inr hr =>
          have h_tmp : env.get (i₀ + i) = 1 := by (rw [add_eq_zero_iff_eq_neg, neg_neg] at hr; exact hr)
          rw [h_tmp]
          simp_all only [IsBool, id_eq, mul_eq_zero, add_neg_cancel, one_ne_zero, or_true]
    . use env.get (i₀ + n)
      constructor
      . have h_nil : (env.get (i₀ + n)) = 0 ∨ (env.get (i₀ + n) + (-1)) = 0 := mul_eq_zero.mp h_output_binary
        cases h_nil with
        | inl hl =>
            rw [hl]
            simp_all only [IsBool, id_eq, mul_eq_zero, zero_ne_one, or_false]
        | inr hr =>
            have h_tmp : env.get (i₀ + n) = 1 := by (rw [add_eq_zero_iff_eq_neg, neg_neg] at hr; exact hr)
            rw [h_tmp]
            simp_all only [IsBool, id_eq, mul_eq_zero, add_neg_cancel, one_ne_zero, or_true]
      . rw [Vector.map_mapRange]
        simp_all +arith [fieldFromBits_as_sum,Vector.getElem_mapRange,circuit_norm]

        -- Step 2: Establish that the 'out' bits in the environment are binary
        have h_out_binary : ∀ (i : Fin n), IsBool (env.get (i₀ + ↑i)) := by
          rintro ⟨i, h⟩
          specialize (h_zero_prod ⟨i, h⟩)
          unfold IsBool
          cases h_zero_prod with
          | inl hl => left; assumption
          | inr hr =>
            right
            simp only [add_eq_zero_iff_eq_neg.mp hr]
            norm_num

        have h_foldl_ev := @foldl_explicit p _ n n (le_refl n) env i₀ h_out_binary

        simp +arith [<-h_foldl_ev] at h_output_sum
        rw [<-h_output_sum]
        rw [eval_foldl]
        . /- case h.right -/
          simp [circuit_norm]
          conv_lhs => simp [<-h_input_eval]
          have h_foldl_split := Fin.foldl_split_mul_add_distrib (α:=F p) (fun j k => input_val[j][Fin.val k]) (fun i => 2^i) (n:=n)

          conv_rhs =>
            arg 2
            intro acc i
            simp only [Finset.sum_sub_distrib, add_sub, add_comm, add_assoc]
            simp only [ProvableType.getElem_eval_fields,eval_vector_eq_get]

          simp [h_input_eval]

          simp_all
          conv_lhs => rw [<-h_foldl_split]
          simp +arith [<-add_assoc]

        . intros e i
          simp [*,circuit_norm]

  completeness := by
    -- Introduce inputs and assumptions
    intros i₀ env input h_env input_val h_input_eval h_isbool
    simp only [circuit_norm, main] at *

    -- Decompose the witness generation assumption (h_env) into parts for 'out' and 'aux'
    rcases h_env with ⟨h_env_out, h_env_aux⟩

    -- Step 1: Simplify the evaluation of the linear combination 'lin'
    -- We use the existing lemma to show 'lin' equals (in[0] + 2^n - in[1])
    have h_lin_val : Expression.eval env (inputLinearSub n input) =
        fieldFromBits input_val[0] + 2^n - fieldFromBits input_val[1] := by apply inputLinearSub_eval_eq_sub; assumption

    -- Step 2: Establish that the 'out' bits in the environment are binary
    have h_out_binary : ∀ (i : Fin n), IsBool (env.get (i₀ + ↑i)) := by
      rintro ⟨i, h⟩
      simp only [h_env_out ⟨i, h⟩]
      set f2b := (Expression.eval env (Fin.foldl n (fun lin i ↦ lin + input[0][i.val] * Expression.const (@HPow.hPow (F p) ℕ (F p) instHPow 2 i) - input[1][i.val] * Expression.const (@HPow.hPow (F p) ℕ (F p) instHPow 2 i)) (Expression.const (2 ^ n)))) with ←heq
      have h_f2b_bits (i : Fin n) : (fieldToBits n f2b)[i] = 0 ∨ (fieldToBits n f2b)[i] = 1 := fieldToBits_bits i.val i.isLt
      apply h_f2b_bits ⟨i, h⟩

    -- Step 3: Establish that the 'aux' bit is binary
    -- This follows from h_env_aux structure (if ... then 1 else 0)
    have h_aux_binary : IsBool (env.get (i₀ + n)) := by
      rw [h_env_aux]
      split_ifs <;> simp [IsBool]

    -- Step 4: Prove the reconstruction equation: lin = (sum of low bits) + aux * 2^n
    -- We define the sum of the output bits as 'lout_val'
    have h_reconstruction :
      Expression.eval env (inputLinearSub n input) = Expression.eval env (Fin.foldl n (fun acc i => (acc.1 + var { index := i₀ + ↑i } * acc.2, acc.2 + acc.2)) (0, 1)).1 +
            env.get (i₀ + n) * 2 ^ n := by
          -- 2. Convert Circuit Fold to Summation
          rw [←foldl_explicit (le_refl n) env i₀ h_out_binary]

          -- 3. Define 'lin' for clarity and prove it equals the reconstruction
          set lin := Expression.eval env (inputLinearSub n input)

          -- We verify the equation by lifting to Natural numbers (ZMod.val)
          -- This avoids modular arithmetic issues since we know 2^(n+1) < p
          apply ZMod.val_injective

          -- 4. Analyze the Summation Term (Lower Bits)
          -- The sum corresponds to 'fieldFromBits' applied to the bits of 'lin'
          -- Ideally: (Sum ...) = lin.val % 2^n
          have h_sum_mod : (Fin.foldl n (fun acc k ↦ acc + env.get (i₀ + ↑k) * 2 ^ k.val) 0).val = lin.val % 2^n := by
            have h_lin_mod : Fin.foldl n (fun (acc : F p) (k : Fin n) => acc + env.get (i₀ + k) * 2^k.val) 0 = fieldFromBits (fieldToBits n lin) := by
              have h_foldl_eq_fieldFromBits : ∀ (bits : Vector (F p) n), (∀ i : Fin n, IsBool (bits[i])) → Fin.foldl n (fun (acc : F p) (k : Fin n) => acc + bits[k] * 2 ^ k.val) 0 = fieldFromBits bits := by
                exact fun bits a ↦ Eq.symm (fieldFromBits_as_sum bits);
              convert h_foldl_eq_fieldFromBits _ _;
              · (expose_names; exact h_env_out x_1);
              · exact fun i => h_env_out i ▸ h_out_binary i;
            rw [h_lin_mod, Utils.Bits.fieldFromBits_fieldToBits_mod];
            rcases p with ( _ | _ | p ) <;> norm_cast;
            erw [ ZMod.val_cast_of_lt ];
            exact lt_of_le_of_lt ( Nat.mod_le _ _ ) ( Nat.lt_of_lt_of_le ( ZMod.val_lt _ ) ( by linarith [ pow_succ' 2 n ] ) )

          -- 5. Analyze the Aux Term (Upper Bit)
          -- aux = (lin / 2^n) % 2
          have h_aux_div : (env.get (i₀ + n)).val = lin.val / 2^n := by
            rw [h_env_aux]
            split_ifs with h_if
            · -- Case: Bit is 1
              -- We need to show (lin / 2^n) % 2 = 1 implies lin / 2^n = 1
              -- This requires bounding lin < 2^(n+1)
              convert h_if using 1;
              · convert h_if.symm using 1;
                exact ZMod.val_one p;
              · have h_aux_one : lin.val / 2 ^ n < 2 := by
                  have h_lin_lt : lin.val < 2^(n+1) := by
                    have h_lin_lt : (fieldFromBits input_val[0]).val < 2^n ∧ (fieldFromBits input_val[1]).val < 2^n := by
                      have h_lin_lt : ∀ (bits : Vector (F p) n), (∀ i (_ : i < n), IsBool bits[i]) → (fieldFromBits bits).val < 2^n := by exact fieldFromBits_lt;
                      exact ⟨ h_lin_lt _ fun i hi => h_isbool 0 i ( by decide ) hi, h_lin_lt _ fun i hi => h_isbool 1 i ( by decide ) hi ⟩;
                    rw [ h_lin_val ];
                    convert lin_bound _ _ h_lin_lt.1 h_lin_lt.2 hnout using 1
                  exact Nat.div_lt_of_lt_mul h_lin_lt;
                convert h_if using 1;
                exact Eq.symm ( Nat.mod_eq_of_lt h_aux_one )
            · -- Case: Bit is 0
              rw [ ZMod.val_zero, Nat.div_eq_of_lt ];
              have h_div_lt : lin.val < 2^(n+1) := by
                have h_div : lin.val < 2^(n+1) := by
                  have h_lin_val : lin = fieldFromBits input_val[0] + 2^n - fieldFromBits input_val[1] := by
                    exact h_lin_val
                  rw [ h_lin_val ];
                  apply Circomlib.BinSub.lin_bound;
                  · exact fieldFromBits_lt input_val[0] fun i ↦
                      h_isbool 0 i (of_decide_eq_true (id (Eq.refl true)));
                  · exact fieldFromBits_lt input_val[1] fun i ↦
                      h_isbool 1 i (of_decide_eq_true (id (Eq.refl true)));
                  · exact hnout;
                exact h_div;
              contrapose! h_if;
              rw [ Nat.mod_eq_of_lt ];
              · exact Nat.le_antisymm ( Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith! [ pow_succ' 2 n ] ) ( Nat.div_pos h_if <| by positivity );
              · exact Nat.div_lt_of_lt_mul h_div_lt

          -- 6. Combine to prove Euclidean Division: lin = (lin % 2^n) + (lin / 2^n) * 2^n
          rw [ZMod.val_add, ZMod.val_mul]
          simp only [h_sum_mod, h_aux_div]
          have hh := (Nat.mod_add_div lin.val (2^n)).symm
          -- Since $2^n \cdot (lin.val / 2^n)$ is an integer, we can apply the definition of modulo.
          have h_mod : lin.val % p = (lin.val % 2^n + 2^n * (lin.val / 2^n)) % p := by
            rw [ ← hh ];
          convert h_mod using 1;
          · exact Eq.symm ( Nat.mod_eq_of_lt ( show lin.val < p from ZMod.val_lt _ ) );
          · norm_num [ mul_comm, ZMod.val_natCast ];
            norm_cast;
            erw [ ZMod.val_cast_of_lt ] ; linarith [ Nat.pow_le_pow_right two_pos ( show n ≤ n + 1 by linarith ) ]


    -- Final Goal: Prove the conjunction of constraints
    constructor
    · -- Constraint 1: Output bits are binary
      intro i
      specialize h_out_binary i
      rcases h_out_binary with (h0 | h1)
      . rw [h0]; norm_num
      . rw [h1]; norm_num
    · constructor
      · -- Constraint 2: Aux bit is binary
        rcases h_aux_binary with (h0 | h1)
        . rw [h0]; norm_num
        . rw [h1]; norm_num
      · -- Constraint 3: The linear sum check (lin === lout)
        -- This matches our h_reconstruction lemma exactly
        exact h_reconstruction


end BinSub

end Circomlib
