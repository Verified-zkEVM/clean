import Clean.Circuit
import Clean.Utils.Field
import Clean.Gadgets.Boolean
import Clean.Utils.Bitwise
import Clean.Utils.Vector
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
open Bitwise (and_zero_absorb and_one_id_binary and_comm_binary and_assoc_binary)
open Vector (mem_toList_iff_get)
open Circuit (bind_output_eq)

section HelperLemmas

/-- Extract individual field element from vector evaluation -/
lemma eval_get_eq {n : ℕ} {env : Environment (F p)} {input_var : Var (fields n) (F p)}
    {input : fields n (F p)} (h_env : eval env input_var = input) (i : Fin n) :
    env (input_var.get i) = input.get i := by
  change env input_var[i] = input[i]
  rw [ProvableType.eval_fields] at h_env
  have h_eq : (input_var.map (Expression.eval env))[i] = input[i] :=
    congrArg (·[i]) h_env
  rw[← h_eq]
  simp_all only [Vector.getElem_map]
  aesop

end HelperLemmas

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
    return (1 : F p)
  | 1, input =>
    return input.get 0
  | 2, input =>
    AND.circuit.main (input.get 0, input.get 1)
  | n + 3, input => do
    let n1 := (n + 3) / 2
    let n2 := (n + 3) - n1

    have h_sum : n1 + n2 = n + 3 := by
      unfold n1 n2
      omega

    let input1 : Vector (Expression (F p)) n1 :=
      ⟨input.toArray.extract 0 n1, by simp [Array.size_extract, min_eq_left]; unfold n1; omega⟩
    let input2 : Vector (Expression (F p)) n2 :=
      ⟨input.toArray.extract n1 (n + 3), by simp [Array.size_extract]; unfold n2; rfl⟩

    let out1 ← main input1
    let out2 ← main input2

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

-- Key lemma: foldl with AND over binary values gives binary result
theorem List.foldl_and_binary (l : List ℕ) :
    (∀ x ∈ l, x = 0 ∨ x = 1) → (List.foldl (· &&& ·) 1 l = 0 ∨ List.foldl (· &&& ·) 1 l = 1) := by
  intro h_all_binary
  induction l with
  | nil =>
    simp only [List.foldl_nil]
    right; trivial
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h_x_binary : x = 0 ∨ x = 1 := h_all_binary x (List.Mem.head xs)
    have h_xs_binary : ∀ y ∈ xs, y = 0 ∨ y = 1 := fun y hy =>
      h_all_binary y (List.Mem.tail x hy)
    have h_tail_binary := ih h_xs_binary
    cases h_x_binary with
    | inl h_x_zero =>
      rw [h_x_zero]
      simp only [HAnd.hAnd, AndOp.and]
      left
      suffices h : List.foldl (· &&& ·) (1 &&& 0) xs = 0 by
        simp only [List.foldl_cons, HAnd.hAnd, AndOp.and] at h ⊢
        exact h
      have h_one_zero : (1 : ℕ) &&& 0 = 0 := by
        simp only [HAnd.hAnd, AndOp.and]
        rfl
      rw [h_one_zero]
      clear h_one_zero h_x_zero h_all_binary h_xs_binary h_tail_binary ih
      generalize hxs : xs = xs'
      clear xs hxs
      induction xs' with
      | nil => simp [List.foldl_nil]
      | cons y ys ih =>
        simp only [List.foldl_cons, HAnd.hAnd, AndOp.and]
        have h_zero_y : (0 : ℕ).land y = 0 := by
          unfold Nat.land
          simp [Nat.bitwise]
        rw [h_zero_y]
        exact ih
    | inr h_x_one =>
      rw [h_x_one]
      have h_one_one : (1 : ℕ) &&& 1 = 1 := by
        simp only [HAnd.hAnd, AndOp.and]
        rfl
      rw [h_one_one]
      exact h_tail_binary


-- Helper lemma: if all elements of a vector are binary, then all elements of its list are binary
theorem Vector.toList_binary {n : ℕ} (v : Vector (F p) n) :
    (∀ i : Fin n, v.get i = 0 ∨ v.get i = 1) →
    (∀ x ∈ v.toList, x = 0 ∨ x = 1) := by
  intro h_vec x h_mem
  rw [Vector.mem_toList_iff_get] at h_mem
  rcases h_mem with ⟨i, hi⟩
  rw [hi]
  exact h_vec i

/-- For binary values and binary lists, a &&& foldl orig l = foldl (a &&& orig) l -/
theorem List.and_foldl_eq_foldl_of_all_binary (a : ℕ) (orig : ℕ) (l : List ℕ)
    (_ha : a = 0 ∨ a = 1) (hl : ∀ x ∈ l, x = 0 ∨ x = 1) :
    a &&& List.foldl (· &&& ·) orig l = List.foldl (· &&& ·) (a &&& orig) l := by
  induction l generalizing orig with
  | nil =>
    simp only [List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hhd : hd = 0 ∨ hd = 1 := hl hd (List.Mem.head _)
    have htl : ∀ x ∈ tl, x = 0 ∨ x = 1 := fun x hx => hl x (List.mem_cons_of_mem hd hx)
    rw [ih (orig &&& hd) htl]
    congr 1
    simp only [HAnd.hAnd, AndOp.and]
    show a &&& (orig &&& hd) = (a &&& orig) &&& hd
    exact (Nat.land_assoc a orig hd).symm

-- Helper lemma: localLength of bind
theorem Circuit.localLength_bind {α β : Type} (f : Circuit (F p) α) (g : α → Circuit (F p) β) (offset : ℕ) :
    (f >>= g).localLength offset = f.localLength offset + (g (f.output offset)).localLength (offset + f.localLength offset) := by
  simp [Circuit.localLength, Circuit.bind_def, Operations.localLength_append]

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
      have h := AND.circuit.localLength_eq (input.get 0, input.get 1) offset
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
      repeat rw [Circuit.localLength_bind]
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
      exact AND.circuit.subcircuitsConsistent (input.get 0, input.get 1) offset
    | m + 3 =>
      rw [main]
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1
      have h_n1_lt : n1 < m + 3 := by unfold n1; omega
      have h_n2_lt : n2 < m + 3 := by unfold n2; omega
      simp only [Circuit.operations]
      apply Circuit.subcircuitsConsistent_bind
      ·
        let input1 : Var (fields n1) (F p) :=
          ⟨input.toArray.extract 0 n1, by simp; unfold n1; omega⟩
        apply IH n1 h_n1_lt input1
      · apply Circuit.subcircuitsConsistent_bind
        · let input2 : Var (fields n2) (F p) :=
            ⟨input.toArray.extract n1 (m + 3), by simp; unfold n2; rfl⟩
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
        simp only [AND.circuit, subcircuit_norm, AND.main, HasAssignEq.assign_eq, bind_pure, Fin.isValue, bind_pure_comp, circuit_norm] at h_completeness ⊢
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
        have h_n1_lt : n1 < m + 3 := Nat.div_lt_self (by omega) (by norm_num)
        have h_n2_lt : n2 < m + 3 := by simp only [n2, n1]; omega
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
  ∀ i : Fin n, (input.get i = 0 ∨ input.get i = 1)

def Spec (n : ℕ) (input : fields n (F p)) (output : F p) : Prop :=
  output.val = (input.toList.map (·.val)).foldl (· &&& ·) 1 ∧ (output = 0 ∨ output = 1)




/-- If eval env v = w for vectors v and w, then evaluating extracted subvectors preserves equality -/
lemma eval_toArray_extract_eq {n : ℕ} (start stop : ℕ) {env : Environment (F p)}
    {v : Var (fields n) (F p)} {w : fields n (F p)}
    (h_eval : eval env v = w)
    (h_bounds : stop ≤ n) (h_start : start ≤ stop) :
    ProvableType.eval (α := fields (stop - start)) env
      ⟨v.toArray.extract start stop, by simp [Array.size_extract]; omega⟩ =
    ⟨w.toArray.extract start stop, by simp [Array.size_extract]; omega⟩ := by
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
  have size_proof : (v.toArray.extract start stop).size = stop - start := by
    simp [Array.size_extract]
    omega
  have lhs : Expression.eval env (⟨v.toArray.extract start stop, size_proof⟩ : Vector _ _)[i] =
             Expression.eval env v[start + i] := by
    congr 1
    show (v.toArray.extract start stop)[i]'(size_proof ▸ hi) = v.toArray[start + i]'(by simp [v.size_toArray]; exact h_idx)
    rw [Array.getElem_extract]
  rw [lhs]
  have size_proof2 : (w.toArray.extract start stop).size = stop - start := by
    simp [Array.size_extract]
    omega
  have rhs : (⟨w.toArray.extract start stop, size_proof2⟩ : Vector _ _)[i] =
             w[start + i] := by
    show (w.toArray.extract start stop)[i]'(size_proof2 ▸ hi) = w.toArray[start + i]'(by simp [w.size_toArray]; exact h_idx)
    rw [Array.getElem_extract]
  rw [rhs]
  have h_eval' := h_eval
  simp only [ProvableType.eval_fields] at h_eval'
  have : Vector.map (Expression.eval env) v = w := h_eval'
  have : (Vector.map (Expression.eval env) v)[start + i] = w[start + i] := by
    rw [this]
  simp only [Vector.getElem_map] at this
  exact this

/-- Folding AND over a list with a binary initial accumulator
    is equivalent to ANDing the initial value with the fold starting from 1 -/
lemma List.foldl_and_eq_and_foldl {p : ℕ} [Fact p.Prime]
    (l : List (F p)) (init : ℕ) (h_init : init = 0 ∨ init = 1)
    (h_binary : ∀ x ∈ l, x = 0 ∨ x = 1) :
    List.foldl (fun x1 x2 ↦ x1 &&& x2) init (@List.map (F p) ℕ (fun x ↦ ZMod.val x) l) =
    init &&& List.foldl (fun x1 x2 ↦ x1 &&& x2) 1 (@List.map (F p) ℕ (fun x ↦ ZMod.val x) l) := by
  -- Let's use the existing lemma List.and_foldl_eq_foldl_of_all_binary
  -- First, we need to establish that the mapped list elements are binary
  have h_mapped_binary : ∀ x ∈ (@List.map (F p) ℕ (fun x ↦ ZMod.val x) l), x = 0 ∨ x = 1 := by
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have h_y_binary := h_binary y hy
    cases h_y_binary with
    | inl h => left; simp [h, ZMod.val_zero]
    | inr h => right; simp [h, ZMod.val_one]

  rw [List.and_foldl_eq_foldl_of_all_binary init 1 _ h_init h_mapped_binary]
  cases h_init with
  | inl h0 => rw [h0, and_zero_absorb]
  | inr h1 => rw [h1, and_one_id_binary 1 (Or.inr rfl)]


/-- Helper to show that extracting a subvector preserves element access -/
lemma extract_preserves_element {p n n1 : ℕ} (input : fields n (F p)) (i : Fin n1) (h_n1_lt : n1 ≤ n) :
    let input1 : fields n1 (F p) := ⟨input.toArray.extract 0 n1, by simp [Array.size_extract, Vector.size_toArray]; exact h_n1_lt⟩
    input1.get i = input.get ⟨i.val, by omega⟩ := by
  simp only [Vector.get]
  have h_extract : (input.toArray.extract 0 n1)[i.val]'(by
    simp only [Array.size_extract]
    have h1 : i.val < n1 := i.isLt
    have h2 : input.toArray.size = n := by simp [Vector.size_toArray]
    rw [h2, min_eq_left h_n1_lt]
    exact h1) =
                  input.toArray[i.val]'(by 
                    have h1 : i.val < n1 := i.isLt
                    have h2 : input.toArray.size = n := by simp [Vector.size_toArray]
                    rw [h2]
                    omega) := by
    rw [Array.getElem_extract]
    simp
  exact h_extract

/-- Helper to show that extracting a subvector from an offset preserves element access -/
lemma extract_from_offset_preserves_element {p n n1 n2 : ℕ} (input : fields n (F p)) 
    (i : Fin n2) (h_sum : n1 + n2 = n) :
    let input2 : fields n2 (F p) := ⟨input.toArray.extract n1 n, by simp [Array.size_extract, Vector.size_toArray]; omega⟩
    input2.get i = input.get ⟨n1 + i.val, by omega⟩ := by
  simp only [Vector.get]
  have h_extract : (input.toArray.extract n1 n)[i.val]'(by 
    simp only [Array.size_extract]
    have h1 : i.val < n2 := i.isLt
    have h2 : input.toArray.size = n := by simp [Vector.size_toArray]
    rw [h2]
    omega) =
                  input.toArray[n1 + i.val]'(by
                    have : n1 + i.val < input.size := by
                      have h1 : i.val < n2 := i.isLt
                      have h2 : input.size = n := by simp only [Vector.size_toArray]
                      rw [h2]
                      omega
                    exact this) := by
    rw [Array.getElem_extract]
  exact h_extract

/-- Helper to show that mapping .val over a binary vector produces binary values -/
lemma map_val_binary {p n : ℕ} [Fact p.Prime] (input : fields n (F p)) 
    (h_assumptions : Assumptions n input) :
    ∀ x ∈ input.toList.map (·.val), x = 0 ∨ x = 1 := by
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩
  -- Use Vector.toList_binary to convert vector property to list property
  have h_vec_binary := Vector.toList_binary input h_assumptions
  have h_y_binary := h_vec_binary y hy
  cases h_y_binary with
  | inl h => left; simp [h, ZMod.val_zero]
  | inr h => right; simp [h, ZMod.val_one]

/-- Helper to show assumptions hold for the first part of a split -/
lemma assumptions_split_left {p m : ℕ} [Fact p.Prime] 
    (input : fields (m + 3) (F p)) (h_assumptions : Assumptions (m + 3) input) :
    Assumptions ((m + 3) / 2) 
      (⟨input.toArray.extract 0 ((m + 3) / 2), by simp [Array.size_extract]; omega⟩ : fields ((m + 3) / 2) (F p)) := by
  intro i
  rw [extract_preserves_element input i (by omega : (m + 3) / 2 ≤ m + 3)]
  exact h_assumptions ⟨i.val, by omega⟩

/-- Helper to show assumptions hold for the second part of a split -/
lemma assumptions_split_right {p m : ℕ} [Fact p.Prime] 
    (input : fields (m + 3) (F p)) (h_assumptions : Assumptions (m + 3) input) :
    Assumptions ((m + 3) - (m + 3) / 2) 
      (⟨input.toArray.extract ((m + 3) / 2) (m + 3), by simp [Array.size_extract]⟩ : fields ((m + 3) - (m + 3) / 2) (F p)) := by
  intro i
  have h_sum : (m + 3) / 2 + ((m + 3) - (m + 3) / 2) = m + 3 := by omega
  rw [extract_from_offset_preserves_element input i h_sum]
  exact h_assumptions ⟨(m + 3) / 2 + i.val, by omega⟩

/-- Helper to show evaluation preserves for the first part of a split -/
lemma eval_split_left {p m : ℕ} [Fact p.Prime] {env : Environment (F p)}
    {input : fields (m + 3) (F p)} {input_var : Var (fields (m + 3)) (F p)}
    (h_env : eval env input_var = input) :
    let n1 := (m + 3) / 2
    let input_var1 : Var (fields n1) (F p) := ⟨input_var.toArray.extract 0 n1, by simp [Array.size_extract]; omega⟩
    let input1 : fields n1 (F p) := ⟨input.toArray.extract 0 n1, by simp [Array.size_extract]; omega⟩
    eval env input_var1 = input1 := by
  apply eval_toArray_extract_eq 0 _ h_env <;> omega

/-- Helper to show evaluation preserves for the second part of a split -/
lemma eval_split_right {p m : ℕ} [Fact p.Prime] {env : Environment (F p)}
    {input : fields (m + 3) (F p)} {input_var : Var (fields (m + 3)) (F p)}
    (h_env : eval env input_var = input) :
    let n1 := (m + 3) / 2
    let n2 := (m + 3) - n1
    let input_var2 : Var (fields n2) (F p) := ⟨input_var.toArray.extract n1 (m + 3), by simp [Array.size_extract]; omega⟩
    let input2 : fields n2 (F p) := ⟨input.toArray.extract n1 (m + 3), by simp [Array.size_extract]; omega⟩
    eval env input_var2 = input2 := by
  apply eval_toArray_extract_eq _ (m + 3) h_env <;> omega

/-- Soundness for n = 0 case -/
lemma soundness_zero {p : ℕ} [Fact p.Prime] 
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 0) (F p))
    (input : fields 0 (F p)) (_h_env : eval env input_var = input)
    (_h_assumptions : Assumptions 0 input)
    (_h_hold : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset)) :
    Spec 0 input (env ((main input_var).output offset)) := by
  simp only [main, Circuit.output, Circuit.pure_def] at _h_hold ⊢
  simp only [Spec]
  constructor
  · simp only [Expression.eval]
    have : input.toList = [] := by
      cases input using Vector.casesOn
      rename_i l h
      simp at h
      subst h
      rfl
    rw [this]
    simp only [List.map_nil, List.foldl_nil, ZMod.val_one]
  · right
    rfl

/-- Soundness for n = 1 case -/
lemma soundness_one {p : ℕ} [Fact p.Prime] 
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 1) (F p))
    (input : fields 1 (F p)) (h_env : eval env input_var = input)
    (h_assumptions : Assumptions 1 input)
    (_h_hold : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset)) :
    Spec 1 input (env ((main input_var).output offset)) := by
  simp only [main, Circuit.output, Circuit.pure_def] at _h_hold ⊢
  simp only [Spec]
  have h_input0 := h_assumptions (0 : Fin 1)
  have h_eval_eq : env (input_var.get 0) = input.get 0 := eval_get_eq h_env 0
  constructor
  · simp only [h_eval_eq]
    rw [Vector.toList_length_one]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    cases h_input0 with
    | inl h0 => rw [h0]; simp only [ZMod.val_zero]; rfl
    | inr h1 => rw [h1]; simp only [ZMod.val_one]; rfl
  · simp only [h_eval_eq]
    exact h_input0

/-- Soundness for n = 2 case -/
lemma soundness_two {p : ℕ} [Fact p.Prime] 
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 2) (F p))
    (input : fields 2 (F p)) (h_env : eval env input_var = input)
    (h_assumptions : Assumptions 2 input)
    (h_hold : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset)) :
    Spec 2 input (env ((main input_var).output offset)) := by
  simp only [main] at h_hold ⊢
  simp only [Spec]
  have h_input0 := h_assumptions (0 : Fin 2)
  have h_input1 := h_assumptions (1 : Fin 2)
  have h_eval0 : env (input_var.get 0) = input.get 0 := eval_get_eq h_env 0
  have h_eval1 : env (input_var.get 1) = input.get 1 := eval_get_eq h_env 1
  have h_and_spec := AND.circuit.soundness offset env (input_var.get 0, input_var.get 1)
    (input.get 0, input.get 1)
    (by simp only [ProvableType.eval_fieldPair, h_eval0, h_eval1])
    ⟨h_input0, h_input1⟩ h_hold
  
  rcases h_and_spec with ⟨h_val, h_binary⟩
  constructor
  · -- Prove output.val = fold
    simp only [Vector.toList_length_two]
    simp only [List.map_cons, List.map_nil]
    rw [List.foldl_cons, List.foldl_cons, List.foldl_nil]
    have h1 : 1 &&& (input.get 0).val = (input.get 0).val := by
      cases h_input0 with
      | inl h => rw [h]; simp only [ZMod.val_zero]; rfl
      | inr h => rw [h]; simp only [ZMod.val_one]; rfl
    rw [h1]
    exact h_val
  · -- Prove output = 0 ∨ output = 1
    exact h_binary

/-- Completeness for n = 0 case -/
lemma completeness_zero {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 0) (F p))
    (input : fields 0 (F p))
    (_h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (_h_env : eval env input_var = input)
    (_h_assumptions : Assumptions 0 input) :
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  simp [main, Circuit.ConstraintsHold.Completeness]

/-- Completeness for n = 1 case -/
lemma completeness_one {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 1) (F p))
    (input : fields 1 (F p))
    (_h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (_h_env : eval env input_var = input)
    (_h_assumptions : Assumptions 1 input) :
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  simp [main, Circuit.ConstraintsHold.Completeness]

/-- Completeness for n = 2 case -/
lemma completeness_two {p : ℕ} [Fact p.Prime]
    (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields 2) (F p))
    (input : fields 2 (F p))
    (h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (h_env : eval env input_var = input)
    (h_assumptions : Assumptions 2 input) :
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  simp only [main, circuit_norm] at h_local_witnesses ⊢
  
  -- From h_assumptions, we know both inputs are binary
  have h_binary0 : input[0] = 0 ∨ input[0] = 1 := h_assumptions 0
  have h_binary1 : input[1] = 0 ∨ input[1] = 1 := h_assumptions 1
  
  apply AND.circuit.completeness
  · exact h_local_witnesses
  · subst h_env
    simp_all only [forall_eq', id_eq, Fin.isValue]
    rfl
  · simp only [Assumptions] at h_assumptions
    constructor
    · -- First component is binary
      simp only [ProvableType.eval_fieldPair]
      have h_eval0 : env (input_var.get 0) = input.get 0 := 
        eval_get_eq h_env 0
      change env (input_var.get 0) = 0 ∨ env (input_var.get 0) = 1
      rw [h_eval0]
      exact h_binary0
    · -- Second component is binary
      simp only [ProvableType.eval_fieldPair]
      have h_eval1 : env (input_var.get 1) = input.get 1 := 
        eval_get_eq h_env 1
      change env (input_var.get 1) = 0 ∨ env (input_var.get 1) = 1
      rw [h_eval1]
      exact h_binary1


-- Helper theorem for soundness
theorem soundness {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ∀ (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields n) (F p))
      (input : fields n (F p)),
    eval env input_var = input →
    Assumptions n input →
    Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset) →
    Spec n input (env ((main input_var).output offset)) := by
  -- Use strong induction on n
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
      let input1 : fields n1 (F p) :=
        ⟨input.toArray.extract 0 n1, by simp [Array.size_extract, min_eq_left]; unfold n1; omega⟩
      let input2 : fields n2 (F p) :=
        ⟨input.toArray.extract n1 (m + 3), by simp [Array.size_extract]; unfold n2; rfl⟩
      let input_var1 : Var (fields n1) (F p) :=
        ⟨input_var.toArray.extract 0 n1, by simp [Array.size_extract, min_eq_left]; unfold n1; omega⟩
      let input_var2 : Var (fields n2) (F p) :=
        ⟨input_var.toArray.extract n1 (m + 3), by simp [Array.size_extract]; unfold n2; rfl⟩
      let h_eval1' :=
              eval_toArray_extract_eq 0 n1 h_env (by omega) (by omega)
      have h_eval1 : eval env input_var1 = input1 := by
        simp only [input_var1, input1]
        norm_num at h_eval1' ⊢
        assumption

      have h_eval2 : eval env input_var2 = input2 :=
        eval_toArray_extract_eq n1 (m + 3) h_env (by omega) (by omega)

      have h_assumptions1 : Assumptions n1 input1 := by
        intro i
        rw [extract_preserves_element input i (Nat.le_of_lt h_n1_lt)]
        exact h_assumptions ⟨i.val, by omega⟩
      have h_assumptions2 : Assumptions n2 input2 := by
        intro i
        rw [extract_from_offset_preserves_element input i h_sum]
        exact h_assumptions ⟨n1 + i.val, by omega⟩
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
      · have h_input_split : input.toList = input1.toList ++ input2.toList := by
          have := Vector.toList_extract_append input n1 (by omega : n1 ≤ m + 3)
          simp only [input1, input2] at this ⊢
          exact this
        rw [h_input_split, List.map_append, List.foldl_append]
        have h_input1_vals_binary := map_val_binary input1 h_assumptions1
        have h_foldl1_binary := List.foldl_and_binary _ h_input1_vals_binary
        have h_input2_vals_binary := map_val_binary input2 h_assumptions2


        -- First, let's understand what we're proving:
        -- LHS: The do-block output value
        -- RHS: foldl (foldl 1 input1) input2

        -- From h_and_val, we know the AND circuit output equals out1.val &&& out2.val
        -- From h_val1 and h_val2, we know:
        -- - out1.val = foldl 1 input1
        -- - out2.val = foldl 1 input2

        -- So we need to show the do-block output equals the AND circuit output
        -- and then use our lemma about &&& and foldl

        -- The challenge is connecting the do-block notation to h_and_val
        -- Since h_and_val is about the ElaboratedCircuit.main output at a specific offset
        -- and the goal is about the do-block output at offset 0

        -- The key insight: the do-block output is the AND circuit output
        -- We need to connect the do-block notation to ElaboratedCircuit.output

        -- From h_and_val, we know:
        -- ElaboratedCircuit.output (out1, out2) at the final offset
        -- evaluates to out1.val &&& out2.val

        -- The do-block output should be the same as ElaboratedCircuit.output
        -- This is a fundamental property of how do-blocks work in the circuit framework

        -- Apply the lemma about foldl with AND
        -- We need to provide the binary assumptions for input2
        have h_input2_binary : ∀ x ∈ input2.toList, x = 0 ∨ x = 1 := by
          -- Use Vector.toList_binary to convert vector property to list property
          apply Vector.toList_binary
          exact h_assumptions2

        rw [List.foldl_and_eq_and_foldl _ _ h_foldl1_binary h_input2_binary]

        -- We need to show the do-block output equals (foldl 1 input1) &&& (foldl 1 input2)
        -- The key insight: ElaboratedCircuit.main in the goal IS AND.circuit.main
        -- and the offsets match exactly with what h_and_val tells us about

        -- First, notice that ElaboratedCircuit.output in h_and_val is at the same offset
        -- as the ElaboratedCircuit.main.output in the goal

        -- The goal has the output of ElaboratedCircuit.main applied to (out1_expr, out2_expr)
        -- where out1_expr and out2_expr are the outputs of the recursive main calls

        -- h_and_val tells us about ElaboratedCircuit.output (out1, out2) at the same offset
        -- and out1, out2 are defined as the outputs of those same recursive calls

        -- So we can directly use h_and_val
        convert h_and_val using 1

        -- Now we need to show the arguments match
        congr 1
        · -- First component
          rw [h_val1]
        · -- Second component
          rw [h_val2]

      · -- Prove output is binary
        -- The output is from AND circuit, so it's binary
        -- We can use h_and_binary which tells us the AND circuit output is 0 or 1

        -- Similar to the previous case, the do-block output IS the AND circuit output
        -- at the appropriate offset, which h_and_binary tells us is binary

        -- Use the same reasoning as before: ElaboratedCircuit.main is AND.circuit.main
        -- and the output at the given offset is what h_and_binary describes
        exact h_and_binary

-- Helper lemma: MultiAND with binary inputs produces binary output
-- This captures the essential property we need for both soundness and completeness
lemma main_output_binary (n : ℕ) (offset : ℕ) (env : Environment (F p))
    (input_var : Var (fields n) (F p)) (input : fields n (F p))
    (h_eval : eval env input_var = input)
    (h_assumptions : Assumptions n input)
    (h_constraints : Circuit.ConstraintsHold env ((main input_var).operations offset)) :
    let output := env ((main input_var).output offset)
    output = 0 ∨ output = 1 := by
  -- The key insight: we can use soundness to get this property!
  -- If the constraints hold, then by soundness, the spec holds
  -- The spec includes that the output is binary

  -- Apply main_soundness
  have h_spec := soundness n offset env input_var input h_eval h_assumptions

  -- But wait, main_soundness requires ConstraintsHold.Soundness, not just ConstraintsHold
  -- We need to convert using can_replace_soundness
  have h_soundness : Circuit.ConstraintsHold.Soundness env ((main input_var).operations offset) := by
    apply Circuit.can_replace_soundness
    exact h_constraints

  -- Now apply soundness
  have h_spec := soundness n offset env input_var input h_eval h_assumptions h_soundness

  -- Extract the binary part from the spec
  exact h_spec.2

-- Helper lemma for completeness: extract binary from completeness + local witnesses
lemma main_output_binary_from_completeness (n : ℕ) (offset : ℕ) (env : Environment (F p))
    (input_var : Var (fields n) (F p)) (input : fields n (F p))
    (h_eval : eval env input_var = input)
    (h_assumptions : Assumptions n input)
    (h_local_witnesses : env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset))
    (h_completeness : Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset)) :
    let output := env ((main input_var).output offset)
    output = 0 ∨ output = 1 := by
  apply main_output_binary
  · assumption
  · assumption

  apply Circuit.can_replace_completeness (n := offset)
  · apply subcircuitsConsistent
  · -- Convert UsesLocalWitnessesCompleteness to UsesLocalWitnesses
    rw [main_usesLocalWitnesses_iff_completeness]
    · exact h_local_witnesses
    · rfl
  · exact h_completeness

-- Helper theorem for circuit completeness
theorem completeness {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ∀ (offset : ℕ) (env : Environment (F p)) (input_var : Var (fields n) (F p))
      (input : fields n (F p)),
    env.UsesLocalWitnessesCompleteness offset ((main input_var).operations offset) →
    eval env input_var = input →
    Assumptions n input →
    Circuit.ConstraintsHold.Completeness env ((main input_var).operations offset) := by
  -- Use strong induction on n to handle the recursive structure
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro offset env input_var input h_local_witnesses h_env h_assumptions
    match n with
    | 0 => exact completeness_zero offset env input_var input h_local_witnesses h_env h_assumptions
    | 1 => exact completeness_one offset env input_var input h_local_witnesses h_env h_assumptions
    | 2 => exact completeness_two offset env input_var input h_local_witnesses h_env h_assumptions
    | m + 3 =>
      -- Recursive case: split into two halves and apply IH
      simp [main]
      -- Need to handle the recursive structure with proper offset management

      -- The do-block computes three circuits:
      -- 1. main on first half
      -- 2. main on second half
      -- 3. AND circuit on the outputs

      -- The completeness for the recursive case follows from h_local_witnesses
      -- which provides witnesses for the entire circuit including all sub-circuits

      -- The conversion from UsesLocalWitnessesCompleteness to ConstraintsHold.Completeness
      -- for the recursive structure is circuit-specific

      -- The recursive case requires showing that:
      -- 1. The witness assignment from h_local_witnesses can be restricted to each recursive call
      -- 2. The outputs from recursive calls satisfy the AND circuit's assumptions
      -- 3. The witness assignment includes proper values for the AND circuit

      -- Define the same n1, n2 as in the main function
      let n1 := (m + 3) / 2
      let n2 := (m + 3) - n1

      -- Extract the input variables and values
      let input_var1 : Var (fields n1) (F p) := ⟨input_var.toArray.extract 0 n1, by simp; unfold n1; omega⟩
      let input_var2 : Var (fields n2) (F p) := ⟨input_var.toArray.extract n1 (m + 3), by simp; unfold n2; rfl⟩

      -- Get the actual input values
      have h_eval1 : eval env input_var1 = ⟨input.toArray.extract 0 n1, by simp; unfold n1; omega⟩ := by
        apply eval_toArray_extract_eq 0 n1 h_env
        · omega
        · omega

      have h_eval2 : eval env input_var2 = ⟨input.toArray.extract n1 (m + 3), by simp; unfold n2; rfl⟩ := by
        apply eval_toArray_extract_eq n1 (m + 3) h_env
        · omega
        · omega

      let input1 : fields n1 (F p) := ⟨input.toArray.extract 0 n1, by simp; unfold n1; omega⟩
      let input2 : fields n2 (F p) := ⟨input.toArray.extract n1 (m + 3), by simp; unfold n2; rfl⟩

      -- Show assumptions hold for subvectors
      have h_assumptions1 : Assumptions n1 input1 := by
        intro i
        rw [extract_preserves_element input i (by unfold n1; omega)]
        exact h_assumptions ⟨i.val, by omega⟩

      have h_assumptions2 : Assumptions n2 input2 := by
        intro i
        have h_sum : n1 + n2 = m + 3 := by unfold n1 n2; omega
        rw [extract_from_offset_preserves_element input i h_sum]
        exact h_assumptions ⟨n1 + i.val, by omega⟩

      -- The key insight: h_local_witnesses provides witnesses for the entire circuit
      -- This includes witnesses for both recursive calls and the AND circuit

      -- For a do-block circuit, ConstraintsHold.Completeness IS UsesLocalWitnessesCompleteness
      -- So we already have what we need from h_local_witnesses

      -- The goal is about the do-block expansion of main input_var
      -- But h_local_witnesses is about (main input_var).operations offset
      -- These are the same by the definition of main for m+3

      -- The goal is ConstraintsHold.Completeness for the do-block
      -- We have UsesLocalWitnessesCompleteness from h_local_witnesses

      -- First, prove some facts about n1 and n2
      have h_n1_lt : n1 < m + 3 := by
        unfold n1
        omega

      have h_n2_lt : n2 < m + 3 := by
        unfold n2
        omega

      -- Next, we need to show that for m+3, main input_var expands to the do-block
      -- This is true by the definition of main
      have h_main_eq : (main input_var).operations offset =
        ((main input_var1 >>= fun out1 =>
          main input_var2 >>= fun out2 =>
          AND.circuit.main (out1, out2)).operations offset) := by
        -- This follows from the definition of main for case m+3
        simp only [main, AND.circuit]
        -- The do-block notation expands to nested binds
        rfl

      -- Now rewrite h_local_witnesses using this equality
      rw [h_main_eq] at h_local_witnesses

      -- The do-block is: main input_var1 >>= (λ out1 => main input_var2 >>= (λ out2 => AND.circuit.main (out1, out2)))
      -- Use the bind_completeness lemma to decompose it

      -- First, rewrite h_local_witnesses to extract the parts
      rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_local_witnesses

      rw [Circuit.ConstraintsHold.bind_completeness]
      constructor
      · -- First recursive call: main input_var1
        -- Apply IH to get completeness from UsesLocalWitnessesCompleteness
        apply IH n1 h_n1_lt offset env input_var1
        · -- Extract UsesLocalWitnessesCompleteness for first recursive call
          exact h_local_witnesses.1
        · exact h_eval1
        · -- Need h_assumptions1
          exact h_assumptions1

      · -- Rest: main input_var2 >>= AND.circuit.main
        rw [Circuit.ConstraintsHold.bind_completeness]
        constructor
        · -- Second recursive call: main input_var2
          apply IH n2 h_n2_lt _ env input_var2
          · -- Extract UsesLocalWitnessesCompleteness for second recursive call
            -- h_local_witnesses already has bind_usesLocalWitnesses applied once
            -- Need to rewrite h_local_witnesses.2 with bind_usesLocalWitnesses
            have h_rest := h_local_witnesses.2
            rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_rest
            exact h_rest.1
          · exact h_eval2
          · -- Need h_assumptions2
            exact h_assumptions2

        · -- Final AND circuit
          -- We need to apply AND.circuit.completeness
          -- First, we need to know the outputs of the recursive calls
          let out1 := (main input_var1).output offset
          let out2 := (main input_var2).output (offset + (main input_var1).localLength offset)

          -- Apply AND.circuit.completeness
          apply AND.circuit.completeness
          · -- Extract UsesLocalWitnessesCompleteness for AND circuit
            -- h_local_witnesses.2 is about the second bind, need to apply bind_usesLocalWitnesses again
            have h_rest := h_local_witnesses.2
            rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_rest
            exact h_rest.2
          · -- eval env (out1, out2) = (env out1, env out2)
            rfl
          · -- Need to show AND assumptions: both outputs are binary
            -- The AND circuit requires both inputs to be binary (0 or 1)
            -- We get this from the Spec of the recursive calls

            -- We already proved h_assumptions1 and h_assumptions2 in the IH applications above
            -- Now we need to get the outputs are binary from the soundness

            -- First, we need h_assumptions1 and h_assumptions2 again
            -- (These were already computed above, but we need them again for the AND circuit)
            have h_assumptions1' : Assumptions n1 input1 := h_assumptions1

            have h_assumptions2' : Assumptions n2 input2 := h_assumptions2

            -- Get completeness from the IH for both recursive calls
            have h_comp1 : Circuit.ConstraintsHold.Completeness env ((main input_var1).operations offset) := by
              apply IH n1 h_n1_lt offset env input_var1
              · -- Extract UsesLocalWitnessesCompleteness for first recursive call
                exact h_local_witnesses.1
              · exact h_eval1
              · exact h_assumptions1

            have h_comp2 : Circuit.ConstraintsHold.Completeness env ((main input_var2).operations (offset + (main input_var1).localLength offset)) := by
              apply IH n2 h_n2_lt (offset + (main input_var1).localLength offset) env input_var2
              · -- Extract UsesLocalWitnessesCompleteness for second recursive call
                have h_rest := h_local_witnesses.2
                rw [Circuit.ConstraintsHold.bind_usesLocalWitnesses] at h_rest
                exact h_rest.1
              · exact h_eval2
              · exact h_assumptions2

            -- The outputs are binary because of the Spec from recursive calls
            -- We can use the subcircuits' UsesLocalWitnesses property

            -- The goal asks for AND.circuit.Assumptions (eval env (out1, out2))
            -- which expands to: (env out1 = 0 ∨ env out1 = 1) ∧ (env out2 = 0 ∨ env out2 = 1)

            -- For the recursive calls, we have Completeness which implies the constraints hold
            -- Since we also have UsesLocalWitnesses, we can apply can_replace_completeness

            constructor
            · -- Show env out1 is binary
              apply main_output_binary_from_completeness n1 offset env input_var1 input1
              · exact h_eval1
              · exact h_assumptions1
              · exact h_local_witnesses.1
              · exact h_comp1

            · -- Show env out2 is binary
              have h_rest := h_local_witnesses.2
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

  soundness := soundness n
  completeness := by
    intro offset env input_var h_local_witnesses input h_env h_assumptions
    exact completeness n offset env input_var input h_local_witnesses h_env h_assumptions

end MultiAND

end Circomlib
