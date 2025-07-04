import Clean.Circuit
import Clean.Utils.Field
import Clean.Gadgets.Boolean

open IsBool

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
-/

namespace Circomlib
variable {p : ℕ} [Fact p.Prime]

namespace XOR
/-
template XOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - 2*a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a + b - 2*a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := IsBool input.1 ∧ IsBool input.2
  Spec input output :=
    output.val = input.1.val ^^^ input.2.val
    ∧ IsBool output

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ h_a, h_b ⟩ h_hold
    simp only [circuit_norm, main] at h_env h_hold ⊢
    rcases h_env with ⟨ _, _ ⟩
    simp_all only [h_hold]
    constructor
    · rcases h_a with h_a | h_a <;> rcases h_b with h_b | h_b <;>
        simp only [h_a, h_b] <;> norm_num
    · convert xor_is_bool h_a h_b using 1
      ring_nf

  completeness := by
    simp_all only [circuit_norm, main]
end XOR

namespace AND
/-
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := IsBool input.1 ∧ IsBool input.2
  Spec input output :=
    output.val = input.1.val &&& input.2.val
    ∧ IsBool output

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ h_a, h_b ⟩ h_hold
    simp only [circuit_norm, main] at h_env h_hold ⊢
    rcases h_env with ⟨ _, _ ⟩
    simp_all only [h_hold]
    constructor
    · rcases h_a with h_a | h_a <;> rcases h_b with h_b | h_b <;>
        simp [h_a, h_b]
    · convert and_is_bool h_a h_b using 1

  completeness := by
    simp_all only [circuit_norm, main]
end AND

namespace OR
/-
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a + b - a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := IsBool input.1 ∧ IsBool input.2
  Spec input output :=
    output.val = input.1.val ||| input.2.val
    ∧ IsBool output

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ h_a, h_b ⟩ h_hold
    simp only [circuit_norm, main] at h_env h_hold ⊢
    rcases h_env with ⟨ _, _ ⟩
    simp_all only [h_hold]
    constructor
    · rcases h_a with h_a | h_a <;> rcases h_b with h_b | h_b <;>
        simp [h_a, h_b]
    · convert or_is_bool h_a h_b using 1
      ring_nf

  completeness := by
    simp_all only [circuit_norm, main]
end OR

namespace NOT
/-
template NOT() {
    signal input in;
    signal output out;

    out <== 1 + in - 2*in;
}
-/
def main (input : Expression (F p)) := do
  let inp := input
  let out <== 1 + inp - 2*inp
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := IsBool input
  Spec input output :=
    output.val = 1 - input.val
    ∧ IsBool output

  soundness := by
    rintro _ _ _ _ h_env h_in h_hold
    simp only [circuit_norm, main] at h_env h_hold ⊢
    simp_all only [h_hold]
    constructor
    · rcases h_in with h_in | h_in <;> subst h_in <;> ring_nf <;> simp [ZMod.val_one]
    · convert @IsBool.not_is_bool (F p) _ _ h_in using 1
      ring_nf

  completeness := by
    simp_all only [circuit_norm, main]
end NOT

namespace NAND
/-
template NAND() {
    signal input a;
    signal input b;
    signal output out;

    out <== 1 - a*b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== 1 - a*b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := IsBool input.1 ∧ IsBool input.2
  Spec input output :=
    output.val = 1 - (input.1.val &&& input.2.val)
    ∧ IsBool output

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ h_a, h_b ⟩ h_hold
    simp only [circuit_norm, main] at h_env h_hold ⊢
    rcases h_env with ⟨ _, _ ⟩
    simp_all only [h_hold]
    constructor
    · rcases h_a with h_a | h_a <;> rcases h_b with h_b | h_b <;>
        simp [h_a, h_b, ZMod.val_one]
    · convert nand_is_bool h_a h_b using 1
      ring_nf

  completeness := by
    simp_all only [circuit_norm, main]
end NAND

namespace NOR
/-
template NOR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b + 1 - a - b;
}
-/
def main (input : Expression (F p) × Expression (F p)) := do
  let a := input.1
  let b := input.2
  let out <== a*b + 1 - a - b
  return out

def circuit : FormalCircuit (F p) fieldPair field where
  main
  localLength _ := 1
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]

  Assumptions input := IsBool input.1 ∧ IsBool input.2
  Spec input output :=
    output.val = 1 - (input.1.val ||| input.2.val)
    ∧ IsBool output

  soundness := by
    rintro _ _ ⟨ _, _ ⟩ ⟨ _, _ ⟩ h_env ⟨ h_a, h_b ⟩ h_hold
    simp only [circuit_norm, main] at h_env h_hold ⊢
    rcases h_env with ⟨ _, _ ⟩
    simp_all only [h_hold]
    constructor
    · rcases h_a with h_a | h_a <;> rcases h_b with h_b | h_b <;>
        simp [h_a, h_b, ZMod.val_one]
    · convert nor_is_bool h_a h_b using 1
      ring_nf

  completeness := by
    simp_all only [circuit_norm, main]
end NOR

namespace MultiAND
/-
template MultiAND(n) {
    signal input in[n];
    signal output out;
    component and1;
    component and2;
    component ands[2];
    if (n==1) {
        out <== in[0];
    } else if (n==2) {
        and1 = AND();
        and1.a <== in[0];
        and1.b <== in[1];
        out <== and1.out;
    } else {
        and2 = AND();
        var n1 = n\2;
        var n2 = n-n\2;
        ands[0] = MultiAND(n1);
        ands[1] = MultiAND(n2);
        var i;
        for (i=0; i<n1; i++) ands[0].in[i] <== in[i];
        for (i=0; i<n2; i++) ands[1].in[i] <== in[n1+i];
        and2.a <== ands[0].out;
        and2.b <== ands[1].out;
        out <== and2.out;
    }
}
-/

def main : {n : ℕ} → Vector (Expression (F p)) n → Circuit (F p) (Expression (F p))
  | 0, _ =>
    -- Edge case: return 1 for empty AND
    return (1 : F p)
  | 1, input =>
    -- Single input: return the input itself
    return input.get 0
  | 2, input =>
    -- Two inputs: use standard AND
    AND.circuit.main (input.get 0, input.get 1)
  | n + 3, input => do
    -- More than two inputs: recursive case
    let n1 := (n + 3) / 2
    let n2 := (n + 3) - n1

    -- Create proof that n1 + n2 = n + 3
    have h_sum : n1 + n2 = n + 3 := by
      unfold n1 n2
      omega

    -- Split input vector into two halves
    let input1 : Vector (Expression (F p)) n1 :=
      ⟨input.toArray.extract 0 n1, by simp [Array.size_extract, min_eq_left]; unfold n1; omega⟩
    let input2 : Vector (Expression (F p)) n2 :=
      ⟨input.toArray.extract n1 (n + 3), by simp [Array.size_extract]; unfold n2; rfl⟩

    -- Recursive calls
    let out1 ← main input1
    let out2 ← main input2

    -- Combine results with AND
    AND.circuit.main (out1, out2)

-- Helper lemma: localLength distributes over append
theorem Operations.localLength_append (ops1 ops2 : Operations (F p)) :
    Operations.localLength (ops1 ++ ops2) = Operations.localLength ops1 + Operations.localLength ops2 := by
  induction ops1 with
  | nil => simp [Operations.localLength]
  | cons op ops1 ih =>
    cases op with
    | witness m _ => simp [Operations.localLength, ih, Nat.add_assoc]
    | assert _ => simp [Operations.localLength, ih]
    | lookup _ => simp [Operations.localLength, ih]
    | subcircuit s => simp [Operations.localLength, ih, Nat.add_assoc]

-- Helper lemma: localLength of bind
theorem Circuit.localLength_bind {α β : Type} (f : Circuit (F p) α) (g : α → Circuit (F p) β) (offset : ℕ) :
    (f >>= g).localLength offset = f.localLength offset + (g (f.output offset)).localLength (offset + f.localLength offset) := by
  simp [Circuit.localLength, Circuit.bind_def, Operations.localLength_append]

-- Helper lemma for localLength
theorem main_localLength (n : ℕ) (input : Var (fields n) (F p)) (offset : ℕ) :
    (main input).localLength offset = n - 1 := by
  -- Use strong induction on n
  induction n using Nat.strong_induction_on generalizing offset with
  | _ n IH =>
    -- Match on the structure of n as in main's definition
    match n with
    | 0 =>
      -- For n = 0, main returns (1 : F p)
      simp only [main]
      rfl
    | 1 =>
      -- For n = 1, main returns input.get 0
      simp only [main]
      rfl
    | 2 =>
      -- For n = 2, main calls AND.circuit.main
      simp only [main]
      simp only [Fin.isValue, Nat.add_one_sub_one]
      -- We need to use the fact that AND.circuit has localLength = 1
      -- The ElaboratedCircuit.main preserves this property
      have h := AND.circuit.localLength_eq (input.get 0, input.get 1) offset
      rw [show AND.circuit.localLength _ = 1 from rfl] at h
      exact h
    | m + 3 =>
      -- For n ≥ 3, main makes recursive calls
      -- The circuit is built using do notation with recursive calls
      -- We need to analyze the structure carefully

      -- Define n1 and n2 as in the main function
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1

      -- We have n1 + n2 = m + 3
      have h_sum : n1 + n2 = m + 3 := by
        unfold n1 n2
        omega

      -- Both n1 and n2 are less than m + 3
      have h_n1_lt : n1 < m + 3 := by
        unfold n1
        omega
      have h_n2_lt : n2 < m + 3 := by
        unfold n2
        omega

      -- Now we need to prove that the localLength of the entire circuit equals m + 3 - 1
      -- The circuit structure is roughly:
      -- 1. Create input1 and input2 (no local signals)
      -- 2. Recursively call main on input1 (localLength = n1 - 1 by IH)
      -- 3. Recursively call main on input2 (localLength = n2 - 1 by IH)
      -- 4. Call AND.circuit.main (localLength = 1)
      -- Total: (n1 - 1) + (n2 - 1) + 1 = n1 + n2 - 1 = m + 3 - 1
      rw [main]
      repeat rw [Circuit.localLength_bind]

      -- Apply IH to the recursive calls
      -- Need to be careful about the input vectors
      simp only [IH _ h_n1_lt, IH _ h_n2_lt]

      -- For the final AND.circuit.main call, use its localLength_eq property
      -- The AND circuit has localLength = 1
      simp only [Circuit.output]

      -- Use the fact that AND.circuit has localLength = 1
      have h_and : ∀ (inp : Expression (F p) × Expression (F p)) (off : ℕ),
        (AND.circuit.main inp).localLength off = 1 := by
        intro inp off
        have := AND.circuit.localLength_eq inp off
        rw [show AND.circuit.localLength _ = 1 from rfl] at this
        exact this

      rw [h_and]

      -- Now simplify the arithmetic: (n1 - 1) + (n2 - 1) + 1 = m + 3 - 1
      conv => rhs; rw [← h_sum]
      omega


-- Helper lemma: forAll for bind operations
theorem Circuit.forAll_bind {α β : Type} (f : Circuit (F p) α) (g : α → Circuit (F p) β)
    (condition : Condition (F p)) (offset : ℕ) :
    Operations.forAll offset condition ((f >>= g).operations offset) ↔
    Operations.forAll offset condition (f.operations offset) ∧
    Operations.forAll (offset + f.localLength offset) condition
      ((g (f.output offset)).operations (offset + f.localLength offset)) := by
  simp only [Circuit.operations, Circuit.bind_def, Circuit.localLength, Circuit.output]
  conv => rhs; arg 2; arg 1; rw [add_comm]
  exact @Operations.forAll_append (F p) _ condition offset (f offset).2
    (g (f offset).1 (offset + Operations.localLength (f offset).2)).2

-- Helper lemma: SubcircuitsConsistent preserved by bind
theorem Circuit.subcircuitsConsistent_bind {α β : Type} (f : Circuit (F p) α) (g : α → Circuit (F p) β) (offset : ℕ)
    (hf : Operations.SubcircuitsConsistent offset (f.operations offset))
    (hg : Operations.SubcircuitsConsistent (offset + f.localLength offset)
          ((g (f.output offset)).operations (offset + f.localLength offset))) :
    Operations.SubcircuitsConsistent offset ((f >>= g).operations offset) := by
  simp only [Operations.SubcircuitsConsistent] at hf hg ⊢
  rw [Circuit.forAll_bind]
  exact ⟨hf, hg⟩

-- Helper theorem for subcircuitsConsistent
theorem main_subcircuitsConsistent (n : ℕ) (input : Var (fields n) (F p)) (offset : ℕ) :
    Operations.SubcircuitsConsistent offset ((main input).operations offset) := by
  -- Use strong induction on n
  induction n using Nat.strong_induction_on generalizing offset with
  | _ n IH =>
    -- Match on the structure of n as in main's definition
    match n with
    | 0 =>
      -- For n = 0, main returns (1 : F p)
      simp only [main, Circuit.operations, Circuit.pure_def]
      simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    | 1 =>
      -- For n = 1, main returns input.get 0
      simp only [main, Circuit.operations, Circuit.pure_def]
      simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    | 2 =>
      -- For n = 2, main calls AND.circuit.main
      simp only [main, Circuit.operations]
      -- Use the fact that AND.circuit is subcircuits consistent
      exact AND.circuit.subcircuitsConsistent (input.get 0, input.get 1) offset
    | m + 3 =>
      -- For n ≥ 3, main makes recursive calls
      rw [main]

      -- Define n1 and n2 as in the main function
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1

      -- We have n1 < m + 3 and n2 < m + 3
      have h_n1_lt : n1 < m + 3 := by unfold n1; omega
      have h_n2_lt : n2 < m + 3 := by unfold n2; omega

      -- The circuit structure is:
      -- 1. Pure operations creating input1 and input2 (no subcircuits)
      -- 2. main input1 >>= λ out1 => (has subcircuits by IH)
      -- 3. main input2 >>= λ out2 => (has subcircuits by IH)
      -- 4. AND.circuit.main (out1, out2) (has subcircuits)

      -- We need to show SubcircuitsConsistent for the combined operations
      -- After rw [main], we have a circuit structure with recursive calls
      simp only [Circuit.operations]

      -- The structure is: main input1 >>= (λ out1 => main input2 >>= (λ out2 => AND.circuit.main (out1, out2)))
      -- Apply Circuit.subcircuitsConsistent_bind for the first bind
      apply Circuit.subcircuitsConsistent_bind
      · -- First recursive call: main input1
        let input1 : Var (fields n1) (F p) :=
          ⟨input.toArray.extract 0 n1, by simp; unfold n1; omega⟩
        apply IH n1 h_n1_lt input1
      · -- Rest: main input2 >>= AND.circuit.main
        -- Apply bind lemma again
        apply Circuit.subcircuitsConsistent_bind
        · -- Second recursive call: main input2
          let input2 : Var (fields n2) (F p) :=
            ⟨input.toArray.extract n1 (m + 3), by simp; unfold n2; rfl⟩
          apply IH n2 h_n2_lt input2
        · -- Final AND circuit
          apply AND.circuit.subcircuitsConsistent


-- Extract Assumptions and Spec outside the circuit
def MultiAND_Assumptions (n : ℕ) (input : fields n (F p)) : Prop :=
  ∀ i : Fin n, (input.get i = 0 ∨ input.get i = 1)

def MultiAND_Spec (n : ℕ) (input : fields n (F p)) (output : F p) : Prop :=
  output.val = (input.toList.map (·.val)).foldl (· &&& ·) 1 ∧ (output = 0 ∨ output = 1)

-- Helper lemma: A vector of length 1 has toList = [v.get 0]
theorem Vector.toList_length_one {α : Type} (v : Vector α 1) :
    v.toList = [v.get 0] := by
  -- Try using cases on the vector
  cases v using Vector.casesOn with
  | mk arr h =>
      cases arr using Array.casesOn with
      | mk lst =>
        -- h says arr.size = 1, and arr = Array.mk lst
        -- So lst.length = 1
        simp only [List.size_toArray] at h
        -- Now we know lst has length 1, so it must be [x] for some x
        match lst with
        | [] => simp at h
        | [x] =>
          -- Goal: v.toList = [v.get 0]
          -- v.toList = arr.toList = lst = [x]
          -- v.get 0 = arr[0] = lst[0] = x
          rfl
        | _ :: _ :: _ => simp [List.length] at h

-- Helper lemma: A vector of length 2 has toList = [v.get 0, v.get 1]
theorem Vector.toList_length_two {α : Type} (v : Vector α 2) :
    v.toList = [v.get 0, v.get 1] := by
  -- Use the same approach as for length 1
  cases v using Vector.casesOn with
  | mk arr h =>
      cases arr using Array.casesOn with
      | mk lst =>
        simp only [List.size_toArray] at h
        match lst with
        | [] => simp at h
        | [_] => simp [List.length] at h
        | [x, y] => rfl
        | _ :: _ :: _ :: _ => simp [List.length] at h


-- Helper theorem for soundness
theorem main_soundness {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ∀ (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields n) (F p))
      (input : fields n (F p)),
    eval env input_var = input →
    MultiAND_Assumptions n input →
    Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset) →
    MultiAND_Spec n input (env ((main input_var).output offset)) := by
  -- Use strong induction on n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro offset env input_var input h_env h_assumptions h_hold
    -- Match on the structure of n as in main's definition
    match n with
    | 0 =>
      -- For n = 0, main returns (1 : F p)
      simp only [main, Circuit.output, Circuit.pure_def] at h_hold ⊢
      simp only [MultiAND_Spec]
      constructor
      · -- Prove output.val = empty fold = 1
        simp only [Expression.eval]
        -- For n=0, input is a Vector of length 0, so input.toList = []
        have : input.toList = [] := by
          cases input using Vector.casesOn
          rename_i l h
          simp at h
          subst h
          rfl
        rw [this]
        simp only [List.map_nil, List.foldl_nil]
        -- Need to prove ZMod.val 1 = 1
        simp only [ZMod.val_one]
      · -- Prove output = 0 ∨ output = 1
        right
        -- env ((1 : F p)) = 1
        rfl
    | 1 =>
      -- For n = 1, main returns input.get 0
      simp only [main, Circuit.output, Circuit.pure_def] at h_hold ⊢
      simp only [MultiAND_Spec]
      -- We know from h_env that eval env input_var = input
      -- And from h_assumptions that input.get 0 = 0 ∨ input.get 0 = 1
      have h_input0 := h_assumptions (0 : Fin 1)
      -- Need to relate eval env (input_var.get 0) to input.get 0
      have h_eval_eq : env (input_var.get 0) = input.get 0 := by
        -- We have h_env : eval env input_var = input
        -- Use eval_fields to expand eval
        rw [ProvableType.eval_fields] at h_env
        -- Now h_env : input_var.map (Expression.eval env) = input
        -- Apply this equality to index 0 using getElem notation
        have : (input_var.map (Expression.eval env))[0] = input[0] := by
          rw [h_env]
        -- Use Vector.getElem_map: (v.map f)[i] = f v[i]
        rw [Vector.getElem_map] at this
        -- Convert from getElem notation to get notation
        change env (input_var.get 0) = input.get 0
        convert this
      constructor
      · -- Prove output.val = single element fold
        simp only [h_eval_eq]
        -- For n=1, we need to show: (input.get 0).val = (input.toList.map (·.val)).foldl (· &&& ·) 1
        -- Use our Vector.toList_length_one lemma
        rw [Vector.toList_length_one]
        -- Now we have: (input.get 0).val = ([input.get 0].map (·.val)).foldl (· &&& ·) 1
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        -- This simplifies to: (input.get 0).val = 1 &&& (input.get 0).val
        -- For binary values, 1 &&& x = x
        cases h_input0 with
        | inl h0 =>
          rw [h0]
          simp only [ZMod.val_zero]
          rfl
        | inr h1 =>
          rw [h1]
          simp only [ZMod.val_one]
          rfl
      · -- Prove output = 0 ∨ output = 1
        simp only [h_eval_eq]
        exact h_input0
    | 2 =>
      -- For n = 2, main calls AND.circuit.main
      simp only [main] at h_hold ⊢
      simp only [MultiAND_Spec]
      -- We have h_env : eval env input_var = input
      -- And h_assumptions : ∀ i : Fin 2, (input.get i = 0 ∨ input.get i = 1)
      -- We need to show output.val = fold and (output = 0 ∨ output = 1)

      -- Get the two input values
      have h_input0 := h_assumptions (0 : Fin 2)
      have h_input1 := h_assumptions (1 : Fin 2)

      -- The main function calls AND.circuit.main with (input_var.get 0, input_var.get 1)
      -- We need to show the inputs evaluate correctly
      have h_eval0 : env (input_var.get 0) = input.get 0 := by
        rw [ProvableType.eval_fields] at h_env
        have : (input_var.map (Expression.eval env))[0] = input[0] := by rw [h_env]
        rw [Vector.getElem_map] at this
        exact this

      have h_eval1 : env (input_var.get 1) = input.get 1 := by
        rw [ProvableType.eval_fields] at h_env
        have : (input_var.map (Expression.eval env))[1] = input[1] := by rw [h_env]
        rw [Vector.getElem_map] at this
        exact this

      -- Now use AND.circuit.soundness
      have h_and_spec := AND.circuit.soundness offset env (input_var.get 0, input_var.get 1)
        (input.get 0, input.get 1)
        (by simp only [ProvableType.eval_fieldPair, h_eval0, h_eval1])
        ⟨h_input0, h_input1⟩ h_hold

      -- h_and_spec gives us the AND specification
      rcases h_and_spec with ⟨h_val, h_binary⟩

      -- TODO: complete n=2 case - need to connect AND circuit output to main output
      constructor
      · -- Prove output.val = fold
        simp only [Vector.toList_length_two]
        -- Now goal is: output.val = [input.get 0, input.get 1].map(·.val).foldl(· &&& ·) 1
        simp only [List.map_cons, List.map_nil]
        -- Goal: output.val = [(input.get 0).val, (input.get 1).val].foldl (· &&& ·) 1
        -- Apply foldl_cons twice to expand [a, b].foldl f init
        rw [List.foldl_cons, List.foldl_cons, List.foldl_nil]
        -- Goal: output.val = (1 &&& (input.get 0).val) &&& (input.get 1).val
        -- Simplify 1 &&& x = x for binary values
        have h1 : 1 &&& (input.get 0).val = (input.get 0).val := by
          cases h_input0 with
          | inl h => rw [h]; simp only [ZMod.val_zero]; rfl
          | inr h => rw [h]; simp only [ZMod.val_one]; rfl
        rw [h1]
        -- Now goal is: output.val = (input.get 0).val &&& (input.get 1).val
        -- This is exactly h_val from AND.circuit.soundness
        exact h_val
      · -- Prove output = 0 ∨ output = 1
        exact h_binary
    | m + 3 =>
      -- For n ≥ 3, main makes recursive calls
      simp only [main] at h_hold ⊢
      simp only [MultiAND_Spec]

      -- Define n1 and n2 as in the main function
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1

      -- We have n1 + n2 = m + 3
      have h_sum : n1 + n2 = m + 3 := by unfold n1 n2; omega

      -- Both n1 and n2 are less than m + 3
      have h_n1_lt : n1 < m + 3 := by unfold n1; omega
      have h_n2_lt : n2 < m + 3 := by unfold n2; omega

      -- Extract the two input vectors
      let input1 : fields n1 (F p) :=
        ⟨input.toArray.extract 0 n1, by simp [Array.size_extract, min_eq_left]; unfold n1; omega⟩
      let input2 : fields n2 (F p) :=
        ⟨input.toArray.extract n1 (m + 3), by simp [Array.size_extract]; unfold n2; rfl⟩

      -- The corresponding variable vectors
      let input_var1 : Var (fields n1) (F p) :=
        ⟨input_var.toArray.extract 0 n1, by simp [Array.size_extract, min_eq_left]; unfold n1; omega⟩
      let input_var2 : Var (fields n2) (F p) :=
        ⟨input_var.toArray.extract n1 (m + 3), by simp [Array.size_extract]; unfold n2; rfl⟩

      -- Show eval preserves the split
      have h_eval1 : eval env input_var1 = input1 := by 
        sorry -- Technical proof: eval preserves vector extraction
        
      have h_eval2 : eval env input_var2 = input2 := by 
        sorry -- Technical proof: eval preserves vector extraction

      -- Show assumptions hold for subvectors
      have h_assumptions1 : MultiAND_Assumptions n1 input1 := by
        intro i
        -- input1 is extracted from input, so input1.get i = input.get j for some j
        -- Specifically, input1.get i = input.get i (since extract starts at 0)
        have : input1.get i = input.get ⟨i.val, by omega⟩ := by
          -- input1 = ⟨input.toArray.extract 0 n1, _⟩
          -- So input1.get i = (input.toArray.extract 0 n1)[i]
          simp only [input1, Vector.get]
          -- extract preserves elements: arr.extract start len[i] = arr[start + i]
          have h_extract : (input.toArray.extract 0 n1)[i.val]'(by 
            simp only [Array.size_extract]
            have h1 : i.val < n1 := i.isLt
            have h2 : input.size = m + 3 := by simp only [Vector.size_toArray]
            rw [h2, min_eq_left (Nat.le_of_lt h_n1_lt)]
            exact h1) = 
                          input.toArray[i.val]'(by 
                            have h1 : i.val < n1 := i.isLt
                            have h2 : n1 ≤ m + 3 := Nat.le_of_lt h_n1_lt
                            have h3 : input.size = m + 3 := by simp only [Vector.size_toArray]
                            rw [h3]
                            omega) := by
            rw [Array.getElem_extract]
            simp
          exact h_extract
        rw [this]
        exact h_assumptions ⟨i.val, by omega⟩

      have h_assumptions2 : MultiAND_Assumptions n2 input2 := by
        intro i
        -- input2 is extracted from input starting at n1, so input2.get i = input.get (n1 + i)
        have : input2.get i = input.get ⟨n1 + i.val, by omega⟩ := by
          simp only [input2, Vector.get]
          have h_extract : (input.toArray.extract n1 (m + 3))[i.val]'(by simp; exact i.isLt) = 
                          input.toArray[n1 + i.val]'(by 
                            have : n1 + i.val < input.size := by
                              have h1 : i.val < n2 := i.isLt
                              have h2 : input.size = m + 3 := by simp only [Vector.size_toArray]
                              rw [h2]
                              omega
                            exact this) := by
            rw [Array.getElem_extract]
          exact h_extract
        rw [this]
        exact h_assumptions ⟨n1 + i.val, by omega⟩

      -- The main function for m+3 is defined as:
      -- do
      --   let out1 ← main input_var1  
      --   let out2 ← main input_var2
      --   ElaboratedCircuit.main (out1, out2)
      
      -- This is two binds: first bind main input_var1 with (fun out1 => ...), 
      -- then bind main input_var2 with (fun out2 => ElaboratedCircuit.main (out1, out2))
      
      -- For now, we'll use sorry to complete the proof structure
      -- The key insight is that we need to:
      -- 1. Use bind lemmas to decompose h_hold 
      -- 2. Apply IH to get specs for recursive calls
      -- 3. Use AND.circuit.soundness for the final combination
      
      -- Apply IH to first recursive call
      have h_spec1 : MultiAND_Spec n1 input1 (env ((main input_var1).output offset)) := by
        apply IH n1 h_n1_lt offset env input_var1 input1 h_eval1 h_assumptions1
        -- Need to show: ConstraintsHold.Soundness env ((main input_var1).operations offset)
        -- h_hold gives us constraints hold for the whole do-block
        -- Use bind_soundness to decompose it
        rw [Circuit.ConstraintsHold.bind_soundness] at h_hold
        exact h_hold.1
      
      -- Apply IH to second recursive call  
      have h_spec2 : MultiAND_Spec n2 input2 (env ((main input_var2).output (offset + (main input_var1).localLength offset))) := by
        apply IH n2 h_n2_lt (offset + (main input_var1).localLength offset) env input_var2 input2 h_eval2 h_assumptions2
        -- Need to show: ConstraintsHold.Soundness env ((main input_var2).operations (offset + (main input_var1).localLength offset))
        -- From h_hold.2, we have constraints hold for the rest after the first call
        rw [Circuit.ConstraintsHold.bind_soundness] at h_hold
        -- h_hold.2 is about the second bind
        rw [Circuit.ConstraintsHold.bind_soundness] at h_hold
        exact h_hold.2.1
        
      -- Now we need to show the final output satisfies the spec
      -- The output is the AND of the two recursive outputs
      
      -- First, let's understand what the output is
      -- The do-block output is ElaboratedCircuit.main (out1, out2) where
      -- out1 = (main input_var1).output offset
      -- out2 = (main input_var2).output (offset + (main input_var1).localLength offset)
      
      -- We need the constraint holds for the AND circuit
      -- Extract it from h_hold
      have h_hold' := h_hold
      rw [Circuit.ConstraintsHold.bind_soundness] at h_hold'
      rw [Circuit.ConstraintsHold.bind_soundness] at h_hold'
      -- h_hold'.2.2 should be the constraint holds for the AND circuit
      
      -- The recursive case is complex due to:
      -- 1. Managing offsets correctly for the do-block
      -- 2. Extracting constraint holds for each subcircuit
      -- 3. Applying AND.circuit.soundness at the right offset
      -- 4. Proving that the vector splits and recombines correctly
      
      -- For now, we'll use sorry to complete the recursive case
      sorry

def circuit (n : ℕ) : FormalCircuit (F p) (fields n) field where
  main
  localLength _ := n - 1
  localLength_eq := by
    intro input offset
    exact main_localLength n input offset
  subcircuitsConsistent := by
    intro input offset
    exact main_subcircuitsConsistent n input offset

  Assumptions := MultiAND_Assumptions n
  Spec := MultiAND_Spec n

  soundness := by
    intro offset env input_var input h_env h_assumptions h_hold
    exact main_soundness n offset env input_var input h_env h_assumptions h_hold
  completeness := by sorry

end MultiAND

end Circomlib
