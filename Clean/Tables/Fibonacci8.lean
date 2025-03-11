import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Theorems
import Clean.Gadgets.Addition8.Addition8
import Clean.Gadgets.Equality.Field


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

instance : NonEmptyProvableType RowType where
  size := 2
  to_elements x := vec [x.x, x.y]
  from_elements v :=
    let ⟨ [x, y], _ ⟩ := v
    ⟨ x, y ⟩

@[reducible]
def curr_row_off {W : ℕ+} : RowType (CellOffset W RowType) :=
  {
    x := CellOffset.curr 0,
    y := CellOffset.curr 1
  }

@[reducible]
def next_row_off {W : ℕ+} : RowType (CellOffset W RowType) :=
  {
    x := CellOffset.next 0,
    y := CellOffset.next 1
  }

/--
  inductive contraints that are applied every two rows of the trace.
-/
def fib_relation : TwoRowsConstraint RowType (F p) := do
  let curr ← TableConstraint.get_curr_row
  let next ← TableConstraint.get_next_row

  let z : Expression (F p) ← TableConstraint.subcircuit Gadgets.Addition8.circuit {
    x := curr.x,
    y := curr.y
  }

  if let var z := z then
    TableConstraint.assign z (CellOffset.next 1)

  TableConstraint.assertion Gadgets.Equality.Field.circuit ⟨curr.y, next.x⟩

/--
  boundary constraints that are applied at the beginning of the trace.
  This is our "base case" for the Fibonacci sequence.
-/
def boundary_fib : SingleRowConstraint RowType (F p) := do
  let curr ← TableConstraint.get_curr_row
  TableConstraint.assertion Gadgets.Equality.Field.circuit ⟨curr.x, 0⟩
  TableConstraint.assertion Gadgets.Equality.Field.circuit ⟨curr.y, 1⟩

def fib_table : List (TableOperation RowType (F p)) := [
  TableOperation.Boundary 0 boundary_fib,
  TableOperation.EveryRowExceptLast fib_relation,
]

def assumptions {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  N > 2 ∧
  trace.forAllRowsOfTrace (fun row => (row.y).val < 256)

def fib8 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib8 n + fib8 (n + 1)) % 256

def spec {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTraceWithIndex (λ row index =>
    ((row.x).val = fib8 index) ∧
    ((row.y).val = fib8 (index + 1))
  )


lemma fib8_less_than_256 (n : ℕ) : fib8 n < 256 := by
  induction' n using Nat.twoStepInduction
  repeat {simp [fib8]}; apply Nat.mod_lt; simp

lemma vars :
    ((fib_relation (p:=p) .empty).1.1.2 0) = CellOffset.curr 0 ∧
    ((fib_relation (p:=p) .empty).1.1.2 1) = CellOffset.curr 1 ∧
    ((fib_relation (p:=p) .empty).1.1.2 2) = CellOffset.next 0 ∧
    ((fib_relation (p:=p) .empty).1.1.2 4) = CellOffset.next 1
  := by
  rw [show CellOffset.next 0 = CellOffset.next 2 by simp [CellOffset.next]]
  simp [fib_relation, bind, table_norm ]
  repeat constructor


def formal_fib_table : FormalTable (F p) RowType := {
  constraints := fib_table,
  assumptions := assumptions,
  spec := spec,
  soundness := by
    intro N trace
    simp only [assumptions, gt_iff_lt, TraceOfLength.forAllRowsOfTrace, table_constraints_hold,
      fib_table, spec, TraceOfLength.forAllRowsOfTraceWithIndex, and_imp]

    intro _N_assumption

    induction' trace.val using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    · simp [table_norm]
    · intro _
      simp [table_norm, fib_table]
      intros boundary1 boundary2
      simp [Circuit.formal_assertion_to_subcircuit, Gadgets.Equality.Field.circuit, Gadgets.Equality.Field.spec,
        circuit_norm
      ] at boundary1 boundary2

      have var1 : ((boundary_fib (p:=p) .empty).1.1.2 0).column = 0
        := by simp [boundary_fib, bind, table_norm]; rfl
      have var2 : ((boundary_fib (p:=p) .empty).1.1.2 1).column = 1
        := by simp [boundary_fib, bind, table_norm]; rfl

      simp only [Fin.isValue, var1, Fin.val_zero, List.getElem_cons_zero, var2, Fin.val_one,
        List.getElem_cons_succ] at boundary1 boundary2
      rw [boundary1, boundary2]
      simp only [fib8, ZMod.val_zero, ZMod.val_one, and_self]

    · intro lookup_h
      simp only [TraceOfLength.forAllRowsOfTrace.inner, Fin.isValue] at lookup_h

      -- first of all, we prove the inductive part of the spec
      unfold TraceOfLength.forAllRowsOfTraceWithIndex.inner
      intros constraints_hold
      specialize ih2 lookup_h.right

      unfold table_constraints_hold.foldl at constraints_hold
      simp only [Trace.len, Nat.succ_eq_add_one, AddLeftCancelMonoid.add_eq_zero, one_ne_zero,
        and_false, reduceIte] at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      simp only at constraints_hold
      specialize ih2 constraints_hold.right
      simp only [ih2, and_self]

      simp only [Fin.isValue] at ih2
      let ⟨curr_fib0, curr_fib1⟩ := ih2.left

      -- lift the constraints to specs
      have constraints_hold := by
        have h := constraints_hold.left
        dsimp [fib_table, circuit_norm, table_norm, Circuit.formal_assertion_to_subcircuit] at h
        simp [vars, CellOffset.column, table_norm] at h
        simp [Gadgets.Addition8.circuit, Gadgets.Addition8.assumptions, Gadgets.Addition8.spec] at h
        simp [Gadgets.Equality.Field.circuit, Gadgets.Equality.Field.spec, Fin.val] at h
        exact h
      have ⟨add_holds, eq_holds⟩ := constraints_hold

      -- and finally now we prove the actual relations, this is fortunately very easy
      -- now that we have lifted the constraints to specs

      have lookup_first_col : (curr.x).val < 256 := by
        -- This is true also by induction, because we proved that
        -- curr.x is exactly fib8 index, and fib8 is always less than 256
        rw [ih2.left.left]
        apply fib8_less_than_256

      specialize add_holds lookup_first_col (by simp only [lookup_h])

      have spec1 : (next.x).val = fib8 (rest.len + 1) := by
        apply_fun ZMod.val at eq_holds
        rw [curr_fib1] at eq_holds
        exact eq_holds.symm

      have spec2 : (next.y).val = fib8 (rest.len + 2) := by
        simp only [Fin.isValue, fib8]
        rw [curr_fib0, curr_fib1] at add_holds
        assumption

      simp only [Fin.isValue, spec1, Trace.len, Nat.succ_eq_add_one, spec2, and_self]
}

end Tables.Fibonacci8Table
