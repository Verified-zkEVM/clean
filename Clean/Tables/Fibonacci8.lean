import Clean.Utils.Vector
import Clean.Circuit.Extensions
import Clean.Table.Theorems
import Clean.Gadgets.Addition8.Addition8

/-
  8-bit Fibonacci inductive table definition. The i-th row of the table
  contains the values of the Fibonacci sequence at i and i+1, modulo 256.

  x        | y
  ...
  fib(i)   | fib(i+1)
  fib(i+1) | fib(i+2)
  ...

-/
namespace Tables.Fibonacci8Table
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

structure RowType (F : Type) where
  x: F
  y: F

instance : ProvableType RowType where
  size := 2
  toElements x := #v[x.x, x.y]
  fromElements v :=
    let ⟨ .mk [x, y], _ ⟩ := v
    ⟨ x, y ⟩

/--
  inductive contraints that are applied every two rows of the trace.
-/
def fibRelation : TwoRowsConstraint RowType (F p) := do
  let curr ← TableConstraint.getCurrRow
  let next_x ← copyToVar curr.y
  let next_y ← Gadgets.Addition8.circuit { x := curr.x, y := curr.y }
  assignVar (.next 0) next_x
  assign (.next 1) next_y

/--
  boundary constraints that are applied at the beginning of the trace.
  This is our "base case" for the Fibonacci sequence.
-/
def boundaryFib : SingleRowConstraint RowType (F p) :=
  assignCurrRow { x := 0, y := 1 }

def fibTable : List (TableOperation RowType (F p)) := [
  boundary (.fromStart 0) boundaryFib,
  everyRowExceptLast fibRelation,
]

def fib8 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib8 n + fib8 (n + 1)) % 256

def Spec {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.ForAllRowsOfTraceWithIndex fun row index =>
    (row.x.val = fib8 index) ∧
    (row.y.val = fib8 (index + 1))

lemma fib8_less_than_256 (n : ℕ) : fib8 n < 256 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fib8]
  | one => simp [fib8]
  | more _ _ _ => simp [fib8]; apply Nat.mod_lt; simp

-- TODO kinda pointless to use `assignCurrRow` if the easiest way to unfold it is by making the steps explicit
omit p_large_enough in
lemma boundaryFib_eq : boundaryFib (p:=p) = (do
    assign (.curr 0) 0
    assign (.curr 1) 1)
  := rfl

omit p_large_enough in
lemma boundary_step (first_row : Row (F p) RowType) (aux_env : Environment (F p)) :
  Circuit.ConstraintsHold.Soundness (boundaryFib.windowEnv ⟨<+> +> first_row, rfl⟩ aux_env) boundaryFib.operations
    → ZMod.val first_row.x = fib8 0 ∧ ZMod.val first_row.y = fib8 1 := by
  -- abstract away `env`
  set env := boundaryFib.windowEnv ⟨<+> +> first_row, rfl⟩ aux_env

  -- simplify constraints
  simp only [boundaryFib]
  simp_assign_row
  simp only [circuit_norm, table_norm, Nat.reduceAdd, Nat.reduceMod, zero_add, neg_eq_zero]
  intro ⟨ boundary1, boundary2 ⟩

  have hx : first_row.x = env.get 0 := by rfl
  have hy : first_row.y = env.get 1 := by rfl
  replace boundary2 : env.get 1 = 1 := calc
    _ = env.get 1 + (1 + -env.get 1) := by rw [boundary2]; ring
    _ = 1 := by ring
  rw [hx, boundary1, hy, boundary2, ZMod.val_zero, ZMod.val_one]
  trivial

def formalFibTable : FormalTable (F p) RowType := {
  constraints := fibTable
  Spec := Spec

  soundness := by
    intro N trace envs _
    simp only [TableConstraintsHold,
      fibTable, Spec, TraceOfLength.ForAllRowsOfTraceWithIndex, Trace.ForAllRowsOfTraceWithIndex]

    induction trace.val using Trace.every_row_two_rows_induction with
    | zero => simp [table_norm]
    | one first_row =>
      simp [table_norm]
      exact boundary_step first_row (envs 0 0)
    | more curr next rest ih1 ih2 =>
      -- first, we prove the inductive part of the Spec
      -- TODO this should be easier, or there should be a custom induction for it
      unfold Trace.ForAllRowsOfTraceWithIndex.inner
      intros ConstraintsHold

      simp only [table_norm] at ConstraintsHold
      simp at ConstraintsHold
      unfold TableConstraintsHold.foldl at ConstraintsHold
      unfold TableConstraintsHold.foldl at ConstraintsHold
      unfold TableConstraintsHold.foldl at ConstraintsHold
      simp [Trace.len] at ConstraintsHold
      specialize ih2 ConstraintsHold.right
      simp only [ih2, and_true, Trace.len]

      let ⟨curr_fib0, curr_fib1⟩ := ih2.left

      -- simplify constraints
      replace ConstraintsHold := ConstraintsHold.left
      simp [table_norm] at ConstraintsHold

      set env := fibRelation.windowEnv ⟨<+> +> curr +> next, rfl⟩ (envs 1 (rest.len + 1))

      simp only [fibRelation, circuit_norm, table_norm, table_assignment_norm, copyToVar,
          Gadgets.Addition8.circuit] at ConstraintsHold
      simp only [circuit_norm, varFromOffset, Vector.mapRange] at ConstraintsHold

      -- NOTE: In Lean 4.25.0-rc2, Vector/List indexing doesn't reduce definitionally
      -- as it did in v4.24.0. We use explicit simp lemmas to reduce the expressions.
      -- See: https://github.com/leanprover/lean4/issues/10736 for related issues.
      have env_simp : env.get 0 = curr.x ∧ env.get 1 = curr.y ∧
                      env.get 2 = next.x ∧ env.get (2 + 1) = next.y := by
        simp only [env, windowEnv, fibRelation, table_assignment_norm, table_norm, circuit_norm,
          copyToVar, Gadgets.Addition8.circuit, varFromOffset, Pure.pure]
        refine ⟨?_, ?_, ?_, ?_⟩
        all_goals simp only [Vector.toList_mk, List.getElem_set, ite_true,
          Vector.toList_append, Vector.mapFinRange_zero, Vector.mapFinRange_succ,
          Vector.mapRange_zero, Vector.mapRange_succ, Vector.toList_push,
          List.nil_append, List.append_assoc]
        · simp only [dif_pos (by omega : 0 < 5)]; rfl
        · simp only [dif_pos (by omega : 1 < 5)]; rfl
        · simp only [dif_pos (by omega : 2 < 5)]; rfl
        · simp only [dif_pos (by omega : 2 + 1 < 5)]; rfl
      rw [env_simp.1, env_simp.2.1, env_simp.2.2.1, env_simp.2.2.2] at ConstraintsHold
      clear env_simp

      have ⟨eq_holds, add_holds⟩ := ConstraintsHold
      rw [add_neg_eq_zero] at eq_holds

      -- and finally now we prove the actual relations

      have lookup_first_col : curr.x.val < 256 := by
        -- This is true also by induction, because we proved that
        -- curr.x is exactly fib8 index, and fib8 is always less than 256
        rw [ih2.left.left]
        apply fib8_less_than_256

      have lookup_second_col : curr.y.val < 256 := by
        rw [ih2.left.right]
        apply fib8_less_than_256

      specialize add_holds ⟨ lookup_first_col, lookup_second_col ⟩

      have spec1 : next.x.val = fib8 (rest.len + 1) := by
        rw [←curr_fib1]
        congr
        exact eq_holds.symm

      have spec2 : (next.y).val = fib8 (rest.len + 2) := by
        simp only [fib8]
        rw [←curr_fib0, ←curr_fib1]
        assumption

      exact ⟨spec1, spec2⟩
}

end Tables.Fibonacci8Table
