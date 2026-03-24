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
def fibRelation (curr : Var RowType (F p)) :
    TableConstraint 2 RowType (F p) (Var RowType (F p)) := do
  let next_x ← copyToVar curr.y
  let next_y ← Gadgets.Addition8.circuit { x := curr.x, y := curr.y }
  assignVar (.next 0) next_x
  assign (.next 1) next_y
  getNextRow

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

def Spec {N : ℕ} (trace : TraceOfLength (F p) RowType N) (_ : ProverData (F p)) : Prop :=
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
  Spec

  soundness := by
    intro N trace envs _
    simp only [TableConstraintsHold,
      fibTable, Spec, TraceOfLength.ForAllRowsOfTraceWithIndex, Trace.ForAllRowsOfTraceWithIndex]

    induction trace.val using Trace.every_row_two_rows_induction with
    | zero => simp [table_norm]
    | one first_row =>
      simp [table_norm]
      exact boundary_step first_row (envs.toEnvironment 0 0)
    | more curr next rest ih1 ih2 =>
      -- TODO: adapt env_simp proof for the chained constraint pattern (getCurrRow wrapper causes simp timeout)
      sorry
}

end Tables.Fibonacci8Table
