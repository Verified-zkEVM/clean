import Clean.Circuit
import Clean.Utils.Field
import Clean.Gadgets.Boolean
import Clean.Utils.Bitwise
import Clean.Utils.Vector
import Clean.Utils.BinaryOps
import Clean.Circuit.Theorems
import Mathlib.Data.Nat.Bitwise

open IsBool

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/gates.circom
-/

namespace Circomlib
variable {p : ℕ} [Fact p.Prime]

-- Import the moved lemmas
open Circuit (bind_output_eq bind_localLength_eq bind_forAll)
open Operations (append_localLength)
open BinaryOps (List.foldl_and_IsBool List.and_foldl_eq_foldl)

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
    rcases h_env.symm with ⟨ _, _ ⟩
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
    rcases h_env.symm with ⟨ _, _ ⟩
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
    rcases h_env.symm with ⟨ _, _ ⟩
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
    rw [h_env] at h_hold
    simp_all only [h_hold]
    constructor
    · rcases h_in with h_in | h_in <;> rw [h_in] <;> ring_nf <;> simp [ZMod.val_one]
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
    rcases h_env.symm with ⟨ _, _ ⟩
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
    rcases h_env.symm with ⟨ _, _ ⟩
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
    return (1 : F p)
  | 1, input =>
    return input[0]
  | 2, input =>
    AND.circuit.main (input[0], input[1])
  | n + 3, input => do
    let n1 := (n + 3) / 2
    let n2 := (n + 3) - n1

    let input1 : Vector (Expression (F p)) n1 := input.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega)
    let input2 : Vector (Expression (F p)) n2 := input.drop n1 |>.cast (by omega)

    let out1 ← main input1
    let out2 ← main input2

    AND.circuit.main (out1, out2)




-- Helper lemma for localLength
theorem localLength_eq (n : ℕ) (input : Var (fields n) (F p)) (offset : ℕ) :
    (main input).localLength offset = n - 1 := by
  induction n using Nat.strong_induction_on generalizing offset with
  | _ n IH =>
    match n with
    | 0 =>
      simp only [main]
      rfl
    | 1 =>
      simp only [main]
      rfl
    | 2 =>
      simp only [main]
      simp only [Fin.isValue, Nat.add_one_sub_one]
      have h := AND.circuit.localLength_eq (input[0], input[1]) offset
      rw [show AND.circuit.localLength _ = 1 from rfl] at h
      exact h
    | m + 3 =>
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1
      have h_sum : n1 + n2 = m + 3 := by
        unfold n1 n2
        omega
      have h_n1_lt : n1 < m + 3 := by
        unfold n1
        omega
      have h_n2_lt : n2 < m + 3 := by
        unfold n2
        omega
      rw [main]
      repeat rw [bind_localLength_eq]
      simp only [IH _ h_n1_lt, IH _ h_n2_lt]
      simp only [Circuit.output]
      have h_and : ∀ (inp : Expression (F p) × Expression (F p)) (off : ℕ),
        (AND.circuit.main inp).localLength off = 1 := by
        intro inp off
        have := AND.circuit.localLength_eq inp off
        rw [show AND.circuit.localLength _ = 1 from rfl] at this
        exact this

      rw [h_and]
      conv => rhs; rw [← h_sum]
      omega



-- Helper lemma: SubcircuitsConsistent preserved by bind
theorem Circuit.subcircuitsConsistent_bind {α β : Type} (f : Circuit (F p) α) (g : α → Circuit (F p) β) (offset : ℕ)
    (hf : Operations.SubcircuitsConsistent offset (f.operations offset))
    (hg : Operations.SubcircuitsConsistent (offset + f.localLength offset)
          ((g (f.output offset)).operations (offset + f.localLength offset))) :
    Operations.SubcircuitsConsistent offset ((f >>= g).operations offset) := by
  simp only [Operations.SubcircuitsConsistent] at hf hg ⊢
  rw [bind_forAll]
  exact ⟨hf, hg⟩

-- Helper theorem for subcircuitsConsistent
theorem subcircuitsConsistent (n : ℕ) (input : Var (fields n) (F p)) (offset : ℕ) :
    Operations.SubcircuitsConsistent offset ((main input).operations offset) := by
  induction n using Nat.strong_induction_on generalizing offset with
  | _ n IH =>
    match n with
    | 0 =>
      simp only [main, Circuit.operations, Circuit.pure_def]
      simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    | 1 =>
      simp only [main, Circuit.operations, Circuit.pure_def]
      simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    | 2 =>
      simp only [main, Circuit.operations]
      exact AND.circuit.subcircuitsConsistent (input[0], input[1]) offset
    | m + 3 =>
      rw [main]
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1
      have h_n1_lt : n1 < m + 3 := by unfold n1; omega
      have h_n2_lt : n2 < m + 3 := by unfold n2; omega
      simp only [Circuit.operations]
      apply Circuit.subcircuitsConsistent_bind
      ·
        let input1 : Var (fields n1) (F p) := input.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega)
        apply IH n1 h_n1_lt input1
      · apply Circuit.subcircuitsConsistent_bind
        · let input2 : Var (fields n2) (F p) := input.drop n1 |>.cast (by omega)
          apply IH n2 h_n2_lt input2
        · apply AND.circuit.subcircuitsConsistent


-- Helper lemma: UsesLocalWitnesses and UsesLocalWitnessesCompleteness are equivalent for MultiAND.main
lemma main_usesLocalWitnesses_iff_completeness (n : ℕ) (input : Var (fields n) (F p)) (offset1 offset2 : ℕ) (env : Environment (F p)) :
    offset1 = offset2 ->
    (env.UsesLocalWitnesses offset1 ((main input).operations offset2) ↔
     env.UsesLocalWitnessesCompleteness offset1 ((main input).operations offset2)) := by
  induction n using Nat.strong_induction_on generalizing offset1 offset2 with
  | _ n IH =>
    match n with
    | 0 =>
      intros
      simp [main, Circuit.operations, Circuit.pure_def]
      constructor <;> intro <;> trivial
    | 1 =>
      intros
      simp [main, Circuit.operations, Circuit.pure_def]
      constructor <;> intro <;> trivial
    | 2 =>
      intros
      subst offset2
      simp only [main]
      constructor
      ·
        intro h_witnesses
        apply Environment.can_replace_usesLocalWitnessesCompleteness
        · apply AND.circuit.subcircuitsConsistent
        · exact h_witnesses
      · intro h_completeness
        simp only [AND.circuit, subcircuit_norm, AND.main, bind_pure, Fin.isValue, bind_pure_comp, circuit_norm] at h_completeness ⊢
        simp only [Fin.isValue, Nat.add_zero, id_eq]
        unfold Environment.UsesLocalWitnesses Operations.forAllFlat
        unfold Operations.forAll


        constructor
        · simp only [Environment.ExtendsVector, Vector.getElem_mk]
          intro i
          fin_cases i
          simp only [Fin.val_zero, add_zero, List.getElem_toArray]
          exact h_completeness
        · simp only [Operations.forAll]
          trivial
    | m + 3 =>
      intros
      subst offset2
      simp only [main]
      constructor
      · intro h_witnesses
        let n1 := (m + 3) / 2
        let n2 := (m + 3) - n1
        apply Environment.can_replace_usesLocalWitnessesCompleteness
        · rw [← main]
          apply subcircuitsConsistent
        · exact h_witnesses
      · intro h_completeness
        simp only [circuit_norm, subcircuit_norm] at h_completeness ⊢
        rcases h_completeness with ⟨ h_c1, h_c2, h_c3 ⟩

        rw[Environment.UsesLocalWitnesses, Operations.forAllFlat]

        rw [Operations.forAll_append]
        constructor
        · rw[← Operations.forAllFlat, ← Environment.UsesLocalWitnesses]
          rw[IH]
          · aesop
          · omega
          · trivial
        rw [Operations.forAll_append]
        constructor
        · rw[← Operations.forAllFlat, ← Environment.UsesLocalWitnesses]
          rw[IH]
          · aesop
          · omega
          · omega
        · simp only [AND.circuit] at h_c3 ⊢
          simp only [AND.main, circuit_norm] at h_c3 ⊢
          constructor
          · exact h_c3
          · simp only [Gadgets.Equality.circuit, Gadgets.Equality.elaborated, Gadgets.Equality.main, subcircuit_norm]
            rw [Circuit.forEach]
            simp_all [toVars, assertZero, var, circuit_norm, Operations.toFlat, FlatOperation.forAll]

-- Extract Assumptions and Spec outside the circuit
def Assumptions (n : ℕ) (input : fields n (F p)) : Prop :=
  ∀ (i : ℕ) (h : i < n), IsBool input[i]

def Spec (n : ℕ) (input : fields n (F p)) (output : F p) : Prop :=
  output.val = (input.map (·.val)).foldl (· &&& ·) 1 ∧ IsBool output

/-- If eval env v = w for vectors v and w, then evaluating extracted subvectors preserves equality -/
lemma eval_toArray_extract_eq {n : ℕ} (start finish : ℕ) {env : Environment (F p)}
    {v : Var (fields n) (F p)} {w : fields n (F p)}
    (h_eval : w = eval env v)
    (h_bounds : finish ≤ n) (h_start : start ≤ finish) :
    ProvableType.eval (α := fields (finish - start)) env
      ⟨v.toArray.extract start finish, by simp [Array.size_extract]; omega⟩ =
    ⟨w.toArray.extract start finish, by simp [Array.size_extract]; omega⟩ := by
  -- Work with the definition of eval for fields
  simp only [ProvableType.eval_fields]
  -- Need to show the mapped vectors are equal
  apply Vector.ext
  intro i hi
  -- Simplify the map operations
  simp only [Vector.getElem_map]
  -- Key insight: the i-th element of extracted array corresponds to (start + i)-th of original
  have h_idx : start + i < n := by omega
  -- Show LHS
  have size_proof : (v.toArray.extract start finish).size = finish - start := by
    simp [Array.size_extract]
    omega
  have lhs : Expression.eval env (⟨v.toArray.extract start finish, size_proof⟩ : Vector _ _)[i] =
             Expression.eval env v[start + i] := by
    congr 1
    show (v.toArray.extract start finish)[i]'(size_proof ▸ hi) = v.toArray[start + i]'(by simp [v.size_toArray]; exact h_idx)
    rw [Array.getElem_extract]
  rw [lhs]
  have size_proof2 : (w.toArray.extract start finish).size = finish - start := by
    simp [Array.size_extract]
    omega
  have rhs : (⟨w.toArray.extract start finish, size_proof2⟩ : Vector _ _)[i] =
             w[start + i] := by
    show (w.toArray.extract start finish)[i]'(size_proof2 ▸ hi) = w.toArray[start + i]'(by simp [w.size_toArray]; exact h_idx)
    rw [Array.getElem_extract]
  rw [rhs]
  have h_eval' := h_eval
  simp only [ProvableType.eval_fields] at h_eval'
  have : w = Vector.map (Expression.eval env) v := h_eval'
  have : w[start + i] = (Vector.map (Expression.eval env) v)[start + i] := by
    rw [this]
  simp only [Vector.getElem_map] at this
  exact this.symm

/-- Helper to show that extracting a subvector preserves element access -/
lemma extract_preserves_element {p n n1 : ℕ} (input : fields n (F p)) (i : ℕ) (hi : i < n1) (h_n1_lt : n1 ≤ n) :
    let input1 : fields n1 (F p) := ⟨input.toArray.extract 0 n1, by simp [Array.size_extract, Vector.size_toArray]; exact h_n1_lt⟩
    input1[i]'hi = input[i]'(by omega) := by
  simp only [getElem]
  have h_extract : (input.toArray.extract 0 n1)[i]'(by
    simp only [Array.size_extract]
    have h1 : i < n1 := hi
    have h2 : input.toArray.size = n := by simp [Vector.size_toArray]
    rw [h2, min_eq_left h_n1_lt]
    exact h1) =
                  input.toArray[i]'(by
                    have h1 : i < n1 := hi
                    have h2 : input.toArray.size = n := by simp [Vector.size_toArray]
                    rw [h2]
                    omega) := by
    rw [Array.getElem_extract]
    simp
  exact h_extract

/-- Helper to show that extracting a subvector from an offset preserves element access -/
lemma extract_from_offset_preserves_element {p n n1 n2 : ℕ} (input : fields n (F p))
    (i : ℕ) (hi : i < n2) (h_sum : n1 + n2 = n) :
    let input2 : fields n2 (F p) := ⟨input.toArray.extract n1 n, by simp [Array.size_extract, Vector.size_toArray]; omega⟩
    input2[i]'hi = input[n1 + i]'(by omega) := by
  simp only [getElem]
  have h_extract : (input.toArray.extract n1 n)[i]'(by
    simp only [Array.size_extract]
    have h1 : i < n2 := hi
    have h2 : input.toArray.size = n := by simp [Vector.size_toArray]
    rw [h2]
    omega) =
                  input.toArray[n1 + i]'(by
                    have : n1 + i < input.size := by
                      have h1 : i < n2 := hi
                      have h2 : input.size = n := by simp only [Vector.size_toArray]
                      rw [h2]
                      omega
                    exact this) := by
    rw [Array.getElem_extract]
  exact h_extract

lemma Vector.foldl_empty' {α β : Type} (init : β) (f : β → α → β) (v : Vector α 0) :
    Vector.foldl f init v = init := by
  rcases v with ⟨ a, ah ⟩
  rcases a with ⟨ l ⟩
  cases l with
  | nil => rfl
  | cons _ _ => contradiction

/-- Key lemma: folding with &&& over a split vector equals the &&& of the folds over each part -/
lemma Vector.foldl_and_split {n1 n2 n3 : ℕ} (v : Vector ℕ n3)
    (v1 : Vector ℕ n1) (v2 : Vector ℕ n2) (h_sum : n1 + n2 = n3)
    (h_split : v = h_sum ▸ (v1 ++ v2)) :
    Vector.foldl (· &&& ·) 1 v =
    Vector.foldl (· &&& ·) 1 v1 &&& Vector.foldl (· &&& ·) 1 v2 := by
  -- Substitute v with the appended vectors
  rw [h_split]
  -- The key insight: after substituting h_sum, the transport becomes identity
  subst h_sum
  -- Now the goal simplifies since the transport is on a reflexive equality
  -- Apply Vector.foldl_append
  rw [Vector.foldl_append]
  -- After append, we have: foldl (· &&& ·) (foldl (· &&& ·) 1 v1) v2
  -- We need to show this equals (foldl 1 v1) &&& (foldl 1 v2)
  -- Use List.and_foldl_eq_foldl from BinaryOps
  symm
  -- The key is that we need to use the fact that a satisfies IsBool
  -- because it's the result of folding with &&& starting from 1
  generalize h1 : Vector.foldl (· &&& ·) 1 v1 = a
  generalize h2 : Vector.foldl (· &&& ·) 1 v2 = b
  -- Now we need: Vector.foldl (· &&& ·) a v2 = a &&& b
  rw [← h2]
  
  -- First, establish that a is boolean
  have h_a_bool : IsBool a := by
    rw [← h1]
    -- Convert to List operations to use List.foldl_and_IsBool
    rw [Vector.foldl_mk, ← Array.foldl_toList]
    exact List.foldl_and_IsBool v1.toList
  
  -- Convert to List operations
  have : ∀ (init : ℕ) (vec : Vector ℕ n2),
         Vector.foldl (· &&& ·) init vec = List.foldl (· &&& ·) init vec.toList := by
    intros init vec
    rw [Vector.foldl_mk, ← Array.foldl_toList]
  rw [this, this]
  
  -- Apply the lemma
  rw [List.and_foldl_eq_foldl]
  
  -- Now we need to show that a &&& 1 = a when IsBool a
  rw [land_one_of_IsBool a h_a_bool]

/-- Soundness for n = 0 case -/
lemma soundness_zero {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 0) (F p))
    (input : fields 0 (F p)) (_h_env : input = eval env input_var)
    (_h_assumptions : Assumptions 0 input)
    (_h_hold : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset)) :
    Spec 0 input (env ((main input_var).output offset)) := by
  simp only [main, Circuit.output, Circuit.pure_def] at _h_hold ⊢
  simp only [Spec]
  constructor
  · simp [Expression.eval, Vector.foldl_empty', ZMod.val_one]
  · right
    rfl

/-- Soundness for n = 1 case -/
lemma soundness_one {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 1) (F p))
    (input : fields 1 (F p)) (h_env : input = eval env input_var)
    (h_assumptions : Assumptions 1 input)
    (_h_hold : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset)) :
    Spec 1 input (env ((main input_var).output offset)) := by
  simp only [main, Circuit.output, Circuit.pure_def] at _h_hold ⊢
  simp only [Spec]
  have h_input0 := h_assumptions 0 (by norm_num : 0 < 1)
  have h_eval_eq : env input_var[0] = input[0] := by
    simp [h_env, circuit_norm]
  constructor
  · simp only [h_eval_eq]
    -- For a vector of length 1, foldl f init [x] = f init x
    have h_fold_one : ∀ (v : Vector (F p) 1),
      Vector.foldl (fun x1 x2 => x1 &&& x2) 1 (v.map (·.val)) = 1 &&& v[0].val := by
      intro v
      -- Use Vector.foldl definition
      rw [Vector.foldl_mk, ← Array.foldl_toList]
      have h_toList : (v.map (·.val)).toList = [v[0].val] := by
        rw [Vector.toList_length_one]
        simp only [Vector.getElem_map]
      rw [h_toList]
      simp only [List.foldl_cons, List.foldl_nil]
    rw [h_fold_one]
    -- For binary values, 1 &&& x = x
    exact (one_land_of_IsBool input[0].val (val_of_IsBool h_input0)).symm
  · simp only [h_eval_eq]
    exact h_input0

/-- Soundness for n = 2 case -/
lemma soundness_two {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 2) (F p))
    (input : fields 2 (F p)) (h_env : input = eval env input_var)
    (h_assumptions : Assumptions 2 input)
    (h_hold : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset)) :
    Spec 2 input (env ((main input_var).output offset)) := by
  simp only [main] at h_hold ⊢
  simp only [Spec]
  have h_input0 := h_assumptions 0 (by norm_num : 0 < 2)
  have h_input1 := h_assumptions 1 (by norm_num : 1 < 2)
  have h_eval0 : env input_var[0] = input[0] := by simp [h_env, circuit_norm]
  have h_eval1 : env input_var[1] = input[1] := by simp [h_env, circuit_norm]
  have h_and_spec := AND.circuit.soundness offset env (input_var[0], input_var[1])
    (input[0], input[1])
    (by simp only [ProvableType.eval_fieldPair, h_eval0, h_eval1])
    ⟨h_input0, h_input1⟩ h_hold

  rcases h_and_spec with ⟨h_val, h_binary⟩
  constructor
  · -- Prove output.val = fold
    -- For a vector of length 2, we need to show the fold equals input[0] &&& input[1]
    have h_fold_two : Vector.foldl (fun x1 x2 => x1 &&& x2) 1 (input.map (·.val)) = input[0].val &&& input[1].val := by
      rw [Vector.foldl_mk, ← Array.foldl_toList]
      have h_toList : (input.map (·.val)).toList = [input[0].val, input[1].val] := by
        rw [Vector.toList_length_two]
        simp only [Vector.getElem_map]
      rw [h_toList]
      simp only [List.foldl_cons, List.foldl_nil]
      -- The fold gives us (1 &&& input[0].val) &&& input[1].val
      -- We need to show that 1 &&& x = x for binary x
      rw [one_land_of_IsBool input[0].val (val_of_IsBool h_input0)]
    rw [h_fold_two]
    exact h_val
  · -- Prove output = 0 ∨ output = 1
    exact h_binary

/-- Completeness for n = 0 case -/
lemma completeness_zero {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 0) (F p))
    (input : fields 0 (F p))
    (_h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (_h_env : input = eval env input_var)
    (_h_assumptions : Assumptions 0 input) :
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  simp [main, Circuit.ConstraintsHold.Completeness]

/-- Completeness for n = 1 case -/
lemma completeness_one {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 1) (F p))
    (input : fields 1 (F p))
    (_h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (_h_env : input = eval env input_var)
    (_h_assumptions : Assumptions 1 input) :
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  simp [main, Circuit.ConstraintsHold.Completeness]

/-- Completeness for n = 2 case -/
lemma completeness_two {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 2) (F p))
    (input : fields 2 (F p))
    (h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (h_env : input = eval env input_var)
    (h_assumptions : Assumptions 2 input) :
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  simp only [main, circuit_norm] at h_local_witnesses ⊢

  have h_binary0 : IsBool input[0] := h_assumptions 0 (by norm_num)
  have h_binary1 : IsBool input[1] := h_assumptions 1 (by norm_num)

  apply AND.circuit.completeness
  · exact h_local_witnesses
  · subst h_env
    simp_all only [forall_eq', id_eq, Fin.isValue]
    rfl
  · simp only [Assumptions] at h_assumptions
    constructor
    · simp only [ProvableType.eval_fieldPair]
      have h_eval0 : env input_var[0] = input[0] :=
        by simp[h_env, circuit_norm]
      change IsBool (env input_var[0])
      rw [h_eval0]
      exact h_binary0
    · simp only [ProvableType.eval_fieldPair]
      have h_eval1 : env input_var[1] = input[1] :=
        by simp[h_env, circuit_norm]
      change IsBool (env input_var[1])
      rw [h_eval1]
      exact h_binary1


theorem soundness {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ∀ (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields n) (F p))
      (input : fields n (F p)),
    input = eval env input_var →
    Assumptions n input →
    Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset) →
    Spec n input (env ((main input_var).output offset)) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro offset env input_var input h_env h_assumptions h_hold
    match n with
    | 0 => exact soundness_zero offset env input_var input h_env h_assumptions h_hold
    | 1 => exact soundness_one offset env input_var input h_env h_assumptions h_hold
    | 2 => exact soundness_two offset env input_var input h_env h_assumptions h_hold
    | m + 3 =>
      simp only [main] at h_hold ⊢
      simp only [Spec]
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1
      have h_sum : n1 + n2 = m + 3 := by unfold n1 n2; omega
      have h_n1_lt : n1 < m + 3 := by unfold n1; omega
      have h_n2_lt : n2 < m + 3 := by unfold n2; omega
      let input1 : fields n1 (F p) := input.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega)
      let input2 : fields n2 (F p) := input.drop n1 |>.cast (by omega)
      let input_var1 : Var (fields n1) (F p) := input_var.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega)
      let input_var2 : Var (fields n2) (F p) := input_var.drop n1 |>.cast (by omega)
      have h_eval1 : input1 = eval env input_var1 := by
        simp only [input_var1, input1]
        -- Both are casts of take operations
        -- Need to show: take input n1 = eval env (take input_var n1)
        apply Vector.ext
        intro i hi
        -- Need to show: input[i] = (eval env (Vector.cast _ (Vector.take input_var n1)))[i]
        simp only [ProvableType.eval_fields, Vector.getElem_map, Vector.getElem_cast, Vector.getElem_take]
        -- The i-th element of take is just the i-th element
        have hi' : i < n1 := hi
        have hi'' : i < m + 3 := by omega
        -- Use h_env to show equality
        -- Use h_env to show equality
        have : input[i] = (eval env input_var)[i] := by
          rw [h_env]
        simp only [ProvableType.eval_fields, Vector.getElem_map] at this ⊢
        exact this

      have h_eval2 : input2 = eval env input_var2 := by
        simp only [input_var2, input2]
        -- Both are casts of drop operations
        -- Need to show: drop input n1 = eval env (drop input_var n1)
        apply Vector.ext
        intro i hi
        -- Need to show: input[n1 + i] = (eval env (Vector.cast _ (Vector.drop input_var n1)))[i]
        simp only [ProvableType.eval_fields, Vector.getElem_map, Vector.getElem_cast, Vector.getElem_drop]
        -- The i-th element of drop is the (n1 + i)-th element of original
        have hi' : n1 + i < m + 3 := by omega
        -- Use h_env to show equality
        have : input[n1 + i] = (eval env input_var)[n1 + i] := by
          rw [h_env]
        simp only [ProvableType.eval_fields, Vector.getElem_map] at this
        exact this

      have h_assumptions1 : Assumptions n1 input1 := by
        intro i hi
        -- input1[i] = input[i] since input1 is take of input
        simp only [input1]
        have : (input.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega))[i]'hi = input[i]'(by omega) := by
          rw [Vector.getElem_cast, Vector.getElem_take]
        rw [this]
        apply h_assumptions i (by omega)
      have h_assumptions2 : Assumptions n2 input2 := by
        intro i hi
        -- input2[i] = input[n1 + i] since input2 is drop of input
        simp only [input2]
        have : (input.drop n1 |>.cast (by omega))[i]'hi = input[n1 + i]'(by omega) := by
          rw [Vector.getElem_cast, Vector.getElem_drop]
        rw [this]
        apply h_assumptions (n1 + i) (by omega)
      have h_spec1 : Spec n1 input1 (env ((main input_var1).output offset)) := by
        apply IH n1 h_n1_lt offset env input_var1 input1 h_eval1 h_assumptions1
        rw [Circuit.ConstraintsHold.bind_soundness] at h_hold
        exact h_hold.1
      have h_spec2 : Spec n2 input2 (env ((main input_var2).output (offset + (main input_var1).localLength offset))) := by
        apply IH n2 h_n2_lt (offset + (main input_var1).localLength offset) env input_var2 input2 h_eval2 h_assumptions2
        rw [Circuit.ConstraintsHold.bind_soundness] at h_hold
        rw [Circuit.ConstraintsHold.bind_soundness] at h_hold
        exact h_hold.2.1
      have h_hold' := h_hold
      rw [Circuit.ConstraintsHold.bind_soundness] at h_hold'
      rw [Circuit.ConstraintsHold.bind_soundness] at h_hold'
      let out1 := (main input_var1).output offset
      let out2 := (main input_var2).output (offset + (main input_var1).localLength offset)
      have h_and_spec := AND.circuit.soundness
        (offset + (main input_var1).localLength offset + (main input_var2).localLength (offset + (main input_var1).localLength offset))
        env
        (out1, out2)
        (env out1, env out2)
        (by simp only [ProvableType.eval_fieldPair])
        ⟨by rcases h_spec1 with ⟨_, h_binary1⟩; exact h_binary1,
         by rcases h_spec2 with ⟨_, h_binary2⟩; exact h_binary2⟩
        h_hold'.2.2

      rcases h_spec1 with ⟨h_val1, h_binary1⟩
      rcases h_spec2 with ⟨h_val2, h_binary2⟩
      rcases h_and_spec with ⟨h_and_val, h_and_binary⟩
      constructor
      · -- The goal is to show the output equals the fold over the entire input
        -- We have h_val1, h_val2 showing the outputs equal folds over input1, input2
        -- And h_and_val showing the final output is their AND
        -- So we need to relate the fold over the whole input to the AND of the two sub-folds

        -- The goal is about the output of the entire circuit
        -- which is the AND of the two recursive calls
        -- h_and_val tells us this output equals out1.val &&& out2.val
        -- h_val1, h_val2 tell us what out1.val and out2.val are

        -- First simplify the goal by using our hypotheses
        -- The LHS is the output of the entire circuit
        -- The RHS is the fold over the entire input
        -- We know from h_and_val that the output equals out1.val &&& out2.val
        -- We know from h_val1, h_val2 what out1.val and out2.val are

        -- Rewrite using these facts
        trans (Vector.foldl (fun x1 x2 => x1 &&& x2) 1 (input1.map (·.val)) &&&
               Vector.foldl (fun x1 x2 => x1 &&& x2) 1 (input2.map (·.val)))
        · -- Show LHS equals this intermediate expression
          convert h_and_val using 1
          simp only [ProvableType.eval_fieldPair, out1, out2]
          simp only [h_val1, h_val2]

        -- Now we need to show that folding over input equals folding over input1 &&& folding over input2
        -- We're working with Vector.foldl throughout (more idiomatic)

        -- We need the fact that the mapped vectors also split correctly
        have h_append : input1.cast (by omega : n1 = n1) ++ input2.cast (by omega : n2 = n2) =
                          input.cast (by omega : m + 3 = n1 + n2) := by
            -- input1 = input.take n1 |>.cast _ and input2 = input.drop n1 |>.cast _
            simp only [input1, input2]
            -- Apply Vector.append_take_drop
            -- We need to show the cast operations give the right result
            -- We need to show the casted vectors equal the original
            have h_eq : n1 + n2 = m + 3 := by omega
            simp only [Vector.cast_cast]
            rw [← Vector.append_take_drop (n := n1) (m := n2) (v := input.cast h_eq.symm)]
            -- Now use append_take_drop
            congr 1

        -- Now apply Vector.foldl_and_split to the mapped vectors
        symm
        refine Vector.foldl_and_split (Vector.map (·.val) input) (Vector.map (·.val) input1) (Vector.map (·.val) input2) ?_ ?_
        · -- First goal: n1 + n2 = m + 3
          exact h_sum
        · -- Second goal: Vector.map (·.val) input = h_sum ▸ (Vector.map (·.val) input1 ++ Vector.map (·.val) input2)
          -- Use the fact that h_append gives us the relationship between input and input1 ++ input2
          -- First, apply map to both sides of h_append
          have h_map_append : Vector.map (·.val) (input.cast (by omega : m + 3 = n1 + n2)) =
                             Vector.map (·.val) (input1.cast (by omega : n1 = n1) ++ input2.cast (by omega : n2 = n2)) := by
            congr 1
            exact h_append.symm

          -- Simplify the RHS
          simp only [Vector.map_append] at h_map_append

          -- Now we need to show that the transport (▸) equals the cast and map
          -- The key is that for vectors of the same underlying data, cast and transport are equal
          -- Let's prove this step by step

          -- First, show that map preserves casts
          have h1 : Vector.map (·.val) input = (Vector.map (·.val) (input.cast (by omega : m + 3 = n1 + n2))).cast h_sum := by
            ext i
            simp only [Vector.getElem_map, Vector.getElem_cast]

          -- Now show that cast of append equals append after removing redundant casts
          have h2 : Vector.map (·.val) (input1.cast (by omega : n1 = n1)) = Vector.map (·.val) input1 := by
            ext i
            simp only [Vector.getElem_map, Vector.getElem_cast]

          have h3 : Vector.map (·.val) (input2.cast (by omega : n2 = n2)) = Vector.map (·.val) input2 := by
            ext i
            simp only [Vector.getElem_map, Vector.getElem_cast]

          -- Combine everything
          rw [h1, h_map_append, h2, h3]

          -- Finally, show that cast and transport are equal
          have h_cast_transport : ∀ {n m : ℕ} (h : n = m) (v : Vector ℕ n),
                                  Vector.cast h v = h ▸ v := by
            intros n m h v
            subst h
            rfl

          rw [h_cast_transport]

      · exact h_and_binary

lemma main_output_binary (n : ℕ) (offset : ℕ) (env : Environment (F p))
    (input_var : Var (fields n) (F p)) (input : fields n (F p))
    (h_eval : input = eval env input_var)
    (h_assumptions : Assumptions n input)
    (h_constraints : Circuit.ConstraintsHold env ((main input_var).operations offset)) :
    let output := env ((main input_var).output offset)
    IsBool output := by
  have h_soundness : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset) := by
    apply Circuit.can_replace_soundness
    exact h_constraints
  have h_spec := soundness n offset env input_var input h_eval h_assumptions h_soundness
  exact h_spec.2

lemma main_output_binary_from_completeness (n : ℕ) (offset : ℕ) (env : Environment (F p))
    (input_var : Var (fields n) (F p)) (input : fields n (F p))
    (h_eval : input = eval env input_var)
    (h_assumptions : Assumptions n input)
    (h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (h_completeness : Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset)) :
    let output := env ((main input_var).output offset)
    IsBool output := by
  apply main_output_binary
  · assumption
  · assumption
  apply Circuit.can_replace_completeness (n := offset)
  · apply subcircuitsConsistent
  · rw [main_usesLocalWitnesses_iff_completeness]
    · exact h_local_witnesses
    · rfl
  · exact h_completeness

theorem completeness {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ∀ (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields n) (F p))
      (input : fields n (F p)),
    env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset) →
    input = eval env input_var →
    Assumptions n input →
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro offset env input_var input h_local_witnesses h_env h_assumptions
    match n with
    | 0 => exact completeness_zero offset env input_var input h_local_witnesses h_env h_assumptions
    | 1 => exact completeness_one offset env input_var input h_local_witnesses h_env h_assumptions
    | 2 => exact completeness_two offset env input_var input h_local_witnesses h_env h_assumptions
    | m + 3 =>
      simp [main]
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1
      let input_var1 : Var (fields n1) (F p) := input_var.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega)
      let input_var2 : Var (fields n2) (F p) := input_var.drop n1 |>.cast (by omega)

      let input1 : fields n1 (F p) := input.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega)
      let input2 : fields n2 (F p) := input.drop n1 |>.cast (by omega)

      have h_eval1 : input1 = eval env input_var1 := by
        simp only [input_var1, input1]
        apply Vector.ext
        intro i hi
        -- Need to show: input[i] = (eval env (Vector.cast _ (Vector.take input_var n1)))[i]
        simp only [ProvableType.eval_fields, Vector.getElem_map, Vector.getElem_cast, Vector.getElem_take]
        have hi' : i < n1 := hi
        have hi'' : i < m + 3 := by omega
        -- Use h_env to show equality
        have : input[i] = (eval env input_var)[i] := by
          rw [h_env]
        simp only [ProvableType.eval_fields, Vector.getElem_map] at this ⊢
        exact this

      have h_eval2 : input2 = eval env input_var2 := by
        simp only [input_var2, input2]
        apply Vector.ext
        intro i hi
        -- We need to show: input[n1 + i] = (eval env (Vector.cast ⋯ (Vector.drop input_var n1)))[i]
        simp only [ProvableType.eval_fields, Vector.getElem_map, Vector.getElem_cast, Vector.getElem_drop]
        -- Now we need: input[n1 + i] = (eval env input_var)[n1 + i]
        have hi' : n1 + i < m + 3 := by omega
        -- Use the fact that input = eval env input_var
        have := congrArg (fun v => v[n1 + i]'hi') h_env
        simp only [ProvableType.eval_fields, Vector.getElem_map] at this
        exact this
      have h_assumptions1 : Assumptions n1 input1 := by
        intro i hi
        -- input1[i] = input[i] since input1 is take of input
        simp only [input1]
        have : (input.take n1 |>.cast (by simp only [Nat.min_def, n1]; split <;> omega))[i]'hi = input[i]'(by omega) := by
          rw [Vector.getElem_cast, Vector.getElem_take]
        rw [this]
        apply h_assumptions i (by omega)
      have h_assumptions2 : Assumptions n2 input2 := by
        intro i hi
        -- input2[i] = input[n1 + i] since input2 is drop of input
        simp only [input2]
        have : (input.drop n1 |>.cast (by omega))[i]'hi = input[n1 + i]'(by omega) := by
          rw [Vector.getElem_cast, Vector.getElem_drop]
        rw [this]
        apply h_assumptions (n1 + i) (by omega)

      have h_n1_lt : n1 < m + 3 := by
        unfold n1
        omega
      have h_n2_lt : n2 < m + 3 := by
        unfold n2
        omega
      have h_main_eq : (main input_var).operations offset =
        ((main input_var1 >>= fun out1 =>
          main input_var2 >>= fun out2 =>
          AND.circuit.main (out1, out2)).operations offset) := by
        simp only [main, AND.circuit, input_var1, input_var2]
        -- The main function now uses take/drop, and input_var1, input_var2 are defined using take/drop
        -- Need to show the expressions are equal
        -- The expressions are equal by definition of input_var1 and input_var2
        rfl

      -- Note that n1 = (m + 3) / 2 by definition
      -- The goal uses extract, but we can show this equals our take/drop version
      -- because Vector.take n1 = Vector.extract 0 n1 and Vector.drop n1 = Vector.extract n1

      -- First, let's establish that the extract-based expressions equal our variables
      have h_extract_eq_var1 : Vector.cast (by simp only [Nat.min_def, n1]; split <;> omega)
                                          (Vector.extract input_var 0 ((m + 3) / 2)) = input_var1 := by
        simp only [input_var1, Vector.take_eq_extract, n1]

      have h_extract_eq_var2 : Vector.cast (by simp only [n1, n2]; omega)
                                          (Vector.extract input_var ((m + 3) / 2)) = input_var2 := by
        simp only [input_var2, Vector.drop_eq_cast_extract, n1]
        rfl

      -- We need to show that the goal equals what we can prove
      -- Since n1 = (m + 3) / 2, the extract expressions are the same
      suffices Circuit.ConstraintsHold.Completeness env
        ((main input_var1 >>= fun out1 =>
          main input_var2 >>= fun out2 =>
          AND.circuit.main (out1, out2)).operations offset) by
        -- Show that the goal equals this
        convert this

      rw [h_main_eq] at h_local_witnesses
      rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_local_witnesses

      rw [Circuit.ConstraintsHold.bind_completeness]
      constructor
      · apply IH n1 h_n1_lt offset env input_var1
        · exact h_local_witnesses.1
        · exact h_eval1
        · exact h_assumptions1

      · rw [Circuit.ConstraintsHold.bind_completeness]
        constructor
        · apply IH n2 h_n2_lt _ env input_var2
          · have h_rest := h_local_witnesses.2
            rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_rest
            exact h_rest.1
          · exact h_eval2
          · exact h_assumptions2

        · let out1 := (main input_var1).output offset
          let out2 := (main input_var2).output (offset + (main input_var1).localLength offset)

          apply AND.circuit.completeness
          · have h_rest := h_local_witnesses.2
            rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_rest
            exact h_rest.2
          · rfl
          · have h_comp1 : Circuit.ConstraintsHold.Completeness env ((main input_var1).operations offset) := by
              apply IH n1 h_n1_lt offset env input_var1
              · exact h_local_witnesses.1
              · exact h_eval1
              · exact h_assumptions1

            have h_comp2 : Circuit.ConstraintsHold.Completeness env ((main input_var2).operations (offset + (main input_var1).localLength offset)) := by
              apply IH n2 h_n2_lt (offset + (main input_var1).localLength offset) env input_var2
              · have h_rest := h_local_witnesses.2
                rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_rest
                exact h_rest.1
              · exact h_eval2
              · exact h_assumptions2

            constructor
            · apply main_output_binary_from_completeness n1 offset env input_var1 input1
              · exact h_eval1
              · exact h_assumptions1
              · exact h_local_witnesses.1
              · exact h_comp1

            · have h_rest := h_local_witnesses.2
              rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_rest
              apply main_output_binary_from_completeness n2 (offset + (main input_var1).localLength offset) env input_var2 input2
              · exact h_eval2
              · exact h_assumptions2
              · exact h_rest.1
              · exact h_comp2

def circuit (n : ℕ) : FormalCircuit (F p) (fields n) field where
  main
  localLength _ := n - 1
  localLength_eq := localLength_eq n
  subcircuitsConsistent := subcircuitsConsistent n

  Assumptions := Assumptions n
  Spec := Spec n

  -- TODO: Future work - update the FormalCircuit Soundness definition to have
  -- h_env : input = eval env input_var instead of eval env input_var = input
  -- for more natural theorem statements
  soundness := by
    intro offset env input_var input h_env h_assumptions h_hold
    exact soundness n offset env input_var input h_env.symm h_assumptions h_hold
  completeness := by
    intro offset env input_var h_local_witnesses input h_env h_assumptions
    exact completeness n offset env input_var input h_local_witnesses h_env.symm h_assumptions

end MultiAND

end Circomlib
