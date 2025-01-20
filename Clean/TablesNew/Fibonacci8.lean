import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Basic
import Clean.GadgetsNew.Add8.Addition8
import Clean.GadgetsNew.Equality


/-
  8-bit Fibonacci inductive table definition. The i-th row of the table
  contains the values of the Fibonacci sequence at i and i+1, modulo 256.

  0        | 1
  ...
  fib(i)   | fib(i+1)
  fib(i+1) | fib(i+2)
  ...

-/
namespace Fibonacci8Table
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

/--
  inductive contraints that are applied every two rows of the trace.
-/
def fib_relation : TwoRowsConstraint (F p) 2 := do
  let x <- TableConstraint.get_cell (CellOffset.curr 0)
  let y <- TableConstraint.get_cell (CellOffset.curr 1)
  let z : Expression (F p) <- TableConstraint.subcircuit Add8.circuit {x, y}

  if let var z := z then
    TableConstraint.assign z (CellOffset.next 1)

  let x_next <- TableConstraint.get_cell (CellOffset.next 0)
  TableConstraint.assertion Equality.circuit ⟨y, x_next⟩

/--
  boundary constraints that are applied at the beginning of the trace.
  This is our "base case" for the Fibonacci sequence.
-/
def boundary_fib : SingleRowConstraint (F p) 2 := do
  let x <- TableConstraint.get_cell (CellOffset.curr 0)
  let y <- TableConstraint.get_cell (CellOffset.curr 1)
  TableConstraint.assertion Equality.circuit ⟨x, 0⟩
  TableConstraint.assertion Equality.circuit ⟨y, 1⟩

def fib_table : List (TableOperation (F p) 2) := [
  TableOperation.Boundary 0 boundary_fib,
  TableOperation.EveryRowExceptLast fib_relation,
]

def assumptions_fib {N : ℕ} (trace : TraceOfLength (F p) 2 N) : Prop :=
  N > 2 ∧
  trace.forAllRowsOfTrace (fun row => (row 1).val < 256)

def fib8 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib8 n + fib8 (n + 1)) % 256

def spec_fib {N : ℕ} (trace : TraceOfLength (F p) 2 N) : Prop :=
  trace.forAllRowsOfTraceWithIndex (λ row index =>
    ((row 0).val = fib8 index) ∧ ((row 1).val = fib8 (index + 1)))


lemma fib8_less_than_256 (n : ℕ) : fib8 n < 256 := by
  induction' n using Nat.twoStepInduction
  repeat {simp [fib8]}; apply Nat.mod_lt; simp

-- heavy lifting to transform constraints into specs
-- this proof is quite heavy computationally to check for Lean, because of al the `simp` tactics,
-- but once this is checked and cached, the complete soundness proof is faster to check
lemma constraints_hold_lift (curr : Row 2 (F p)) (next : Row 2 (F p)) :
    TableConstraint.constraints_hold_on_window fib_relation ⟨<+> +> curr +> next, by simp⟩ →
    (ZMod.val (curr 0) < 256 → ZMod.val (curr 1) < 256 → ZMod.val (next 1) = (ZMod.val (curr 0) + ZMod.val (curr 1)) % 256) ∧ curr 1 = next 0
    := by
  intro h
  simp [Circuit.formal_assertion_to_subcircuit] at h
  simp [fib_table, ProvableType.from_values] at h

  -- TODO: we should have a better way to do this
  have var1 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
    := by rfl
  have var2 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
    := by rfl
  have var3 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 2).column = 1
    := by rfl
  have var4 : ((fib_relation (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 4).column = 0
    := by rfl
  have var5 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
    := by rfl
  have var6 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
    := by rfl

  rw [var1, var2, var3] at h

  simp [Add8.circuit, Add8.assumptions, Add8.spec] at h
  simp [PreOperation.to_flat_operations, PreOperation.witness_length] at h
  rw [var4] at h
  simp [Equality.circuit, Equality.spec] at h
  assumption

def formal_fib_table : FormalTable (F:=(F p)) := {
  M := 2,
  constraints := fib_table,
  assumptions := assumptions_fib,
  spec := spec_fib,
  soundness := by
    intro N trace
    simp [assumptions_fib]
    simp [fib_table, spec_fib]

    intro _N_assumption

    induction' trace.val using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    · simp
    · intro _
      simp [fib_table]
      intros boundary1 boundary2
      simp [Circuit.formal_assertion_to_subcircuit, Equality.circuit, Equality.spec] at boundary1 boundary2

      have var1 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 0).column = 0
        := by rfl
      have var2 : ((boundary_fib (p:=p) { subContext := { offset := 0 }, assignment := fun x ↦ { rowOffset := 0, column := 0 } }).1.1.2 1).column = 1
        := by rfl

      rw [var1] at boundary1
      rw [var2] at boundary2
      simp [fib8]
      simp [boundary1, boundary2]
      apply ZMod.val_one
    · intro lookup_h
      simp at lookup_h

      -- first of all, we prove the inductive part of the spec
      unfold TraceOfLength.forAllRowsOfTraceWithIndex.inner
      intros constraints_hold
      specialize ih2 lookup_h.right

      unfold table_constraints_hold.foldl at constraints_hold
      simp only [Trace.len, Nat.succ_ne_zero, ite_false] at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      simp only at constraints_hold
      specialize ih2 constraints_hold.right
      simp only [ih2]

      simp at ih2
      let ⟨curr_fib0, curr_fib1⟩ := ih2.left

      -- lift the constraints to specs
      let constraints_hold := constraints_hold_lift curr next constraints_hold.left
      have ⟨add_holds, eq_holds⟩ := constraints_hold

      -- and finally now we prove the actual relations, this is fortunately very easy
      -- now that we have the specs

      have lookup_first_col : (curr 0).val < 256 := by
        -- This is true also by induction, because we proved that
        -- curr 0 is exactly fib8 index, and fib8 is always less than 256
        rw [ih2.left.left]
        apply fib8_less_than_256

      specialize add_holds lookup_first_col lookup_h.right.left

      have spec1 : (next 0).val = fib8 (rest.len + 1) := by
        apply_fun ZMod.val at eq_holds
        rw [curr_fib1] at eq_holds
        exact eq_holds.symm

      have spec2 : (next 1).val = fib8 (rest.len + 2) := by
        simp [fib8]
        rw [curr_fib0, curr_fib1] at add_holds
        assumption

      simp [spec1, spec2]
}

end Fibonacci8Table
