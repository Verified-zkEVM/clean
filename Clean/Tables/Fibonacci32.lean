import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Basic
import Clean.Gadgets.Addition32Full
import Clean.Gadgets.Equality.U32
import Clean.Types.U32


namespace Tables.Fibonacci32
variable {p : ℕ}
variable [p_large_enough: Fact (p > 2*2^32)]

lemma p_large_enough' : Fact (p > 512) := by
  apply Fact.mk; linarith [p_large_enough.elim]

variable [Fact p.Prime]

structure RowType (F : Type) where
  x: U32 F
  y: U32 F

instance (F : Type) : StructuredElements RowType F where
  size := 8
  to_elements s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3]
  from_elements v :=
    -- TODO is it possible to define in terms of StructuredElements.from_elements of the U32?
    let ⟨ [x0, x1, x2, x3, y0, y1, y2, y3], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩ ⟩

/--
  inductive contraints that are applied every two rows of the trace.
-/
def recursive_relation : TwoRowsConstraint RowType (F p) := do
  let curr : RowType _ := StructuredElements.from_elements (<-TableConstraint.get_curr_row)
  let next : RowType _ := StructuredElements.from_elements (<-TableConstraint.get_next_row)

  let z <- TableConstraint.subcircuit Gadgets.Addition32Full.circuit {
    x := curr.x,
    y := curr.y,
    carry_in:=0
  }

  if let ⟨⟨var z0, var z1, var z2, var z3⟩, _⟩ := z then
    TableConstraint.assign z0 (CellOffset.next 4)
    TableConstraint.assign z1 (CellOffset.next 5)
    TableConstraint.assign z2 (CellOffset.next 6)
    TableConstraint.assign z3 (CellOffset.next 7)

  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨curr.y, next.x⟩

/--
  boundary constraints that are applied at the beginning of the trace.
  This is our "base case" for the Fibonacci sequence.
-/
def boundary : SingleRowConstraint RowType (F p) := do
  let row : RowType _ := StructuredElements.from_elements (<-TableConstraint.get_curr_row)

  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨row.x, ⟨0, 0, 0, 0⟩⟩
  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨row.y, ⟨1, 0, 0, 0⟩⟩

def fib32_table : List (TableOperation RowType (F p)) := [
  TableOperation.Boundary 0 boundary,
  TableOperation.EveryRowExceptLast recursive_relation,
]

def assumptions {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  N > 2 ∧
  trace.forAllRowsOfTrace (fun row => (row.y).is_normalized)

def fib32 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib32 n + fib32 (n + 1)) % 2^32

def spec {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTraceWithIndex (λ row index =>
    (row.x.value = fib32 index) ∧ (row.y.value = fib32 (index + 1))
    )


lemma fib32_less_than_2_32 (n : ℕ) : fib32 n < 2^32 := by
  induction' n using Nat.twoStepInduction
  repeat {simp [fib32]}; apply Nat.mod_lt; simp


def boundary_var1 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 0) = CellOffset.curr 0
  := by simp [boundary, bind, table_norm]; rfl
def boundary_var2 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 1) = CellOffset.curr 1
  := by simp [boundary, bind, table_norm]; rfl
def boundary_var3 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 2) = CellOffset.curr 2
  := by simp [boundary, bind, table_norm]; rfl
def boundary_var4 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 3) = CellOffset.curr 3
  := by simp [boundary, bind, table_norm]; rfl
def boundary_var5 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 4) = CellOffset.curr 4
  := by simp [boundary, bind, table_norm]; rfl
def boundary_var6 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 5) = CellOffset.curr 5
  := by simp [boundary, bind, table_norm]; rfl
def boundary_var7 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 6) = CellOffset.curr 6
  := by simp [boundary, bind, table_norm]; rfl
def boundary_var8 : ((boundary (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 7) = CellOffset.curr 7
  := by simp [boundary, bind, table_norm]; rfl

def rec_var0 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 0) = CellOffset.curr 0
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var1 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 1) = CellOffset.curr 1
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var2 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 2) = CellOffset.curr 2
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var3 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 3) = CellOffset.curr 3
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var4 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 4) = CellOffset.curr 4
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var5 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 5) = CellOffset.curr 5
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var6 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 6) = CellOffset.curr 6
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var7 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 7) = CellOffset.curr 7
  := by simp [recursive_relation, bind, table_norm]; rfl

def rec_var8 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 8) = CellOffset.next 8
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var9 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 9) = CellOffset.next 1
  := by simp [recursive_relation, bind, table_norm, StructuredElements.size]; rfl
def rec_var10 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 10) = CellOffset.next 2
  := by simp [recursive_relation, bind, table_norm, StructuredElements.size]; rfl
def rec_var11 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 11) = CellOffset.next 3
  := by simp [recursive_relation, bind, table_norm, StructuredElements.size]; rfl

def rec_var16 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 16) = CellOffset.next 4
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var18 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 18) = CellOffset.next 5
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var20 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 20) = CellOffset.next 6
  := by simp [recursive_relation, bind, table_norm]; rfl
def rec_var22 : ((recursive_relation (p:=p) { offset := 0, assignment := fun _ ↦ { rowOffset := 0, column := 0 } }).1.1.2 22) = CellOffset.next 7
  := by simp [recursive_relation, bind, table_norm]; rfl

lemma lift_rec_add (curr : Row (F p) RowType) (next : Row (F p) RowType)
  : TableConstraint.constraints_hold_on_window recursive_relation ⟨<+> +> curr +> next, by simp [Trace.len]⟩ ->
  (curr.x.is_normalized -> curr.y.is_normalized -> next.y.value = (curr.x.value + curr.y.value) % 2^32) := by

  simp [table_norm, StructuredElements.size, StructuredElements.from_elements]
  intros h_add h_eq

  -- TODO: ok this is very annoying
  -- why can't simp figure out those relations?
  rw [
    show ((3 : Fin 4).val % 6 % 7 % 8) = 3 by rfl,
    show ((4 : Fin 5).val % 7 % 8) = 4 by rfl,
    show (((5 : Fin 6).val % 8)) = 5 by rfl,
    show ((6 : Fin 7).val) = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
  ] at h_add

  simp [Circuit.subcircuit_soundness] at h_add
  simp only [rec_var0, rec_var1, rec_var2, rec_var3, rec_var4, rec_var5, rec_var6, rec_var7] at h_add
  simp [CellOffset.curr, Gadgets.Addition32Full.circuit, Gadgets.Addition32Full.spec,
    table_norm, StructuredElements.to_elements, from_values] at h_add
  simp [to_vars, circuit_norm, table_norm] at h_add

  simp [rec_var16, rec_var18, rec_var20, rec_var22] at h_add
  simp [CellOffset.next] at h_add
  simp [
    show (3 : Fin 8).val = 3 by rfl,
    show (4 : Fin 8).val = 4 by rfl,
    show (5 : Fin 8).val = 5 by rfl,
    show (6 : Fin 8).val = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
  ] at h_add
  simp [Gadgets.Addition32Full.assumptions] at h_add

  intro h_norm_x h_norm_y
  specialize h_add h_norm_x h_norm_y
  simp only [h_add]


lemma lift_rec_eq (curr : Row (F p) RowType) (next : Row (F p) RowType)
  : TableConstraint.constraints_hold_on_window recursive_relation ⟨<+> +> curr +> next, by simp [Trace.len]⟩ ->
  curr.y = next.x := by

  simp [table_norm, StructuredElements.size, StructuredElements.from_elements]
  intros _ h_eq

  rw [
    show ((3 : Fin 4).val % 6 % 7 % 8) = 3 by rfl,
    show ((4 : Fin 5).val % 7 % 8) = 4 by rfl,
    show (((5 : Fin 6).val % 8)) = 5 by rfl,
    show ((6 : Fin 7).val) = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
  ] at h_eq

  simp [Circuit.formal_assertion_to_subcircuit, Circuit.subassertion_soundness, from_values, Gadgets.Equality.U32.circuit, to_vars] at h_eq
  simp only [rec_var4, rec_var5, rec_var6, rec_var7, rec_var8, rec_var9, rec_var10, rec_var11] at h_eq
  simp [CellOffset.curr, Gadgets.Addition32Full.circuit, Gadgets.Addition32Full.spec,
    table_norm, StructuredElements.to_elements, from_values, Gadgets.Equality.U32.spec] at h_eq

  simp [
    show (3 : Fin 8).val = 3 by rfl,
    show (4 : Fin 8).val = 4 by rfl,
    show (5 : Fin 8).val = 5 by rfl,
    show (6 : Fin 8).val = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
    show (8 : Fin 8).val = 0 by rfl,
  ] at h_eq

  have ⟨h0, h1, h2, h3⟩ := h_eq
  ext
  repeat simp only [h0, h1, h2, h3]


def formal_fib32_table : FormalTable (F p) RowType := {
  constraints := fib32_table,
  assumptions := assumptions,
  spec := spec,
  soundness := by
    intro N trace
    simp only [assumptions, gt_iff_lt, Fin.isValue, and_imp, Fin.isValue, fib32_table, spec]
    rw [TraceOfLength.forAllRowsOfTraceWithIndex, TraceOfLength.forAllRowsOfTrace, table_constraints_hold]


    intro _N_assumption

    induction' trace.val using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    · simp [table_norm]
    · intro _
      simp only [table_norm]
      simp [table_norm, Circuit.formal_assertion_to_subcircuit, Circuit.subassertion_soundness, circuit_norm]

      rw [
        show ((3 : Fin 4).val % 6 % 7 % 8) = 3 by rfl,
        show ((4 : Fin 5).val % 7 % 8) = 4 by rfl,
        show (((5 : Fin 6).val % 8)) = 5 by rfl,
        show ((6 : Fin 7).val) = 6 by rfl,
        show (7 : Fin 8).val = 7 by rfl,
      ]

      simp only [boundary_var1, boundary_var2, boundary_var3, boundary_var4, boundary_var5, boundary_var6, boundary_var7, boundary_var8]
      simp [CellOffset.curr, Gadgets.Equality.U32.circuit, Gadgets.Equality.U32.spec]

      simp [
        show (3 : Fin 8).val = 3 by rfl,
        show (4 : Fin 8).val = 4 by rfl,
        show (5 : Fin 8).val = 5 by rfl,
        show (6 : Fin 8).val = 6 by rfl,
        show (7 : Fin 8).val = 7 by rfl,
      ]
      intros b0 b1 b2 b3 b4 b5 b6 b7

      simp only [U32.value, fib32]
      rw [b0, b1, b2, b3, b4, b5, b6, b7]
      simp [ZMod.val_one]

    · intro lookup_h
      simp only [TraceOfLength.forAllRowsOfTrace.inner, Fin.isValue] at lookup_h

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
      simp only [ih2, and_self]

      simp only [Fin.isValue, and_true] at ih2
      let ⟨curr_fib0, curr_fib1⟩ := ih2.left

      simp only [and_true]

      -- lift the constraints to spec
      have add_spec := lift_rec_add curr next constraints_hold.left
      have eq_spec := lift_rec_eq curr next constraints_hold.left

      -- and now we can reason at high level with U32s
      have h_lookup_first : curr.x.is_normalized := by
        -- TODO: should be easy
        sorry

      specialize add_spec h_lookup_first lookup_h.right.left
      simp [fib32]
      rw [←curr_fib0, ←curr_fib1, ←eq_spec]
      simp [add_spec, curr_fib1, Trace.len]
}

end Tables.Fibonacci32
