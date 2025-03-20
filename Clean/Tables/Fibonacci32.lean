import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Theorems
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Gadgets.Equality.U32
import Clean.Types.U32

namespace Tables.Fibonacci32
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

def fib32 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib32 n + fib32 (n + 1)) % 2^32

/--
  The row type for fib32 are two U32 values
-/
structure RowType (F : Type) where
  x: U32 F
  y: U32 F

instance : NonEmptyProvableType RowType where
  size := 8
  to_elements s := #v[s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3]
  from_elements v :=
    -- TODO is it possible to define in terms of ProvableType.from_elements of the U32?
    let ⟨ [x0, x1, x2, x3, y0, y1, y2, y3], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩ ⟩

@[reducible]
def next_row_off : RowType (CellOffset 2 RowType) := {
  x := ⟨CellOffset.next 0, CellOffset.next 1, CellOffset.next 2, CellOffset.next 3⟩,
  y := ⟨CellOffset.next 4, CellOffset.next 5, CellOffset.next 6, CellOffset.next 7⟩
}

@[reducible]
def assign_U32 (x : U32 (Variable (F p))) (offs : U32 (CellOffset 2 RowType)) : TwoRowsConstraint RowType (F p) :=
  do
  TableConstraint.assign x.x0 offs.x0
  TableConstraint.assign x.x1 offs.x1
  TableConstraint.assign x.x2 offs.x2
  TableConstraint.assign x.x3 offs.x3

/--
  inductive contraints that are applied every two rows of the trace.
-/
def recursive_relation : TwoRowsConstraint RowType (F p) := do
  let curr ← TableConstraint.get_curr_row
  let next ← TableConstraint.get_next_row

  let { z, ..} ← TableConstraint.subcircuit Gadgets.Addition32Full.circuit {
    x := curr.x,
    y := curr.y,
    carry_in := 0
  }

  if let ⟨var z0, var z1, var z2, var z3⟩ := z then
    assign_U32 ⟨z0, z1, z2, z3⟩ next_row_off.y

  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨curr.y, next.x⟩

/--
  Boundary constraints that are applied at the beginning of the trace.
-/
def boundary : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.get_curr_row
  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨row.x, ⟨0, 0, 0, 0⟩⟩
  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨row.y, ⟨1, 0, 0, 0⟩⟩

/--
  The fib32 table is composed of the boundary and recursive relation constraints.
-/
def fib32_table : List (TableOperation RowType (F p)) := [
  TableOperation.Boundary 0 boundary,
  TableOperation.EveryRowExceptLast recursive_relation,
]

/--
  We assume that the trace length is at least 2 and that,
  using lookups, the second U32 value is normalized.
-/
def assumptions {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  N ≥ 2 ∧
  trace.forAllRowsOfTrace (fun row => (row.y).is_normalized)

/--
  Specification for fibonacci32: for each row with index i
  - the first U32 value is the i-th fibonacci number
  - the second U32 value is the (i+1)-th fibonacci number
  - the first U32 value is normalized
-/
def spec {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTraceWithIndex (λ row index =>
    (row.x.value = fib32 index) ∧
    (row.y.value = fib32 (index + 1)) ∧
    row.x.is_normalized
  )


/-
  First of all, we prove some lemmas about the mapping variables -> cell offsets
  for both boundary and recursive relation
  Those are too expensive to prove in-line, so we prove them here and use them later
-/
omit p_large_enough in
lemma boundary_vars :
    ((boundary (p:=p) .empty).snd.assignment 0) = CellOffset.curr 0 ∧
    ((boundary (p:=p) .empty).snd.assignment 1) = CellOffset.curr 1 ∧
    ((boundary (p:=p) .empty).snd.assignment 2) = CellOffset.curr 2 ∧
    ((boundary (p:=p) .empty).snd.assignment 3) = CellOffset.curr 3 ∧
    ((boundary (p:=p) .empty).snd.assignment 4) = CellOffset.curr 4 ∧
    ((boundary (p:=p) .empty).snd.assignment 5) = CellOffset.curr 5 ∧
    ((boundary (p:=p) .empty).snd.assignment 6) = CellOffset.curr 6 ∧
    ((boundary (p:=p) .empty).snd.assignment 7) = CellOffset.curr 7
  := by
  simp only [boundary, bind, TableConstraint.get_curr_row,
    TableConstraintOperation.update_context, zero_add, ge_iff_le, zero_le, decide_True,
    Bool.true_and, decide_eq_true_eq, Fin.isValue, Nat.cast_zero, sub_zero, Vector.map,
    Vector.init, Vector.push, Nat.reduceAdd, Vector.nil, Fin.coe_fin_one, Fin.val_zero, add_zero,
    List.nil_append, Nat.cast_one, Fin.val_one, List.singleton_append, Nat.cast_ofNat,
    Fin.val_two, List.cons_append, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.val_natCast,
    List.map_cons, List.map_nil, CellOffset.curr]
  repeat constructor

lemma rec_vars_curr :
    ((recursive_relation (p:=p) .empty).snd.assignment 0) = CellOffset.curr 0 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 1) = CellOffset.curr 1 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 2) = CellOffset.curr 2 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 3) = CellOffset.curr 3 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 4) = CellOffset.curr 4 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 5) = CellOffset.curr 5 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 6) = CellOffset.curr 6 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 7) = CellOffset.curr 7
  := by
  dsimp only [table_norm, recursive_relation]
  simp only [Vector.map, Vector.init, Vector.push, Nat.reduceAdd, Vector.nil, Nat.cast_zero,
    Fin.isValue, Fin.coe_fin_one, Fin.val_zero, add_zero, List.nil_append, Nat.cast_one,
    Fin.val_one, List.singleton_append, Nat.cast_ofNat, Fin.val_two, List.cons_append,
    Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.val_natCast, List.map_cons, List.map_nil, ge_iff_le,
    Bool.and_eq_true, decide_eq_true_eq, bind_assoc, pure_bind]
  repeat constructor

lemma rec_vars_next :
    ((recursive_relation (p:=p) .empty).snd.assignment 8) = CellOffset.next 0 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 9) = CellOffset.next 1 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 10) = CellOffset.next 2 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 11) = CellOffset.next 3 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 16) = CellOffset.next 4 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 18) = CellOffset.next 5 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 20) = CellOffset.next 6 ∧
    ((recursive_relation (p:=p) .empty).snd.assignment 22) = CellOffset.next 7
  := by
  dsimp only [table_norm, recursive_relation]
  simp only [Vector.map, Vector.init, Vector.push, Nat.reduceAdd, Vector.nil, Nat.cast_zero,
    Fin.isValue, Fin.coe_fin_one, Fin.val_zero, add_zero, List.nil_append, Nat.cast_one,
    Fin.val_one, List.cons_append, Nat.cast_ofNat, Fin.val_two, Fin.coe_eq_castSucc,
    Fin.coe_castSucc, Fin.val_natCast, List.map_cons, List.map_nil, ge_iff_le, Bool.and_eq_true,
    decide_eq_true_eq, bind_assoc, pure_bind]
  rw [
    show ((3 : Fin 4).val % 6 % 7 % 8) = 3 by rfl,
    show ((4 : Fin 5).val % 7 % 8) = 4 by rfl,
    show (((5 : Fin 6).val % 8)) = 5 by rfl,
    show ((6 : Fin 7).val) = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
  ]
  repeat constructor

/--
  Main lemma that shows that if the constraints hold over the two-row window, then the spec of add32
  is satisfied, namely that if curr.x.is_normalized and curr.y.is_normalized, then
  - next.y.value = (curr.x.value + curr.y.value) % 2^32
  - next.y.is_normalized
-/
lemma lift_rec_add (curr : Row (F p) RowType) (next : Row (F p) RowType)
  : TableConstraint.constraints_hold_on_window recursive_relation ⟨<+> +> curr +> next, by simp [Trace.len]⟩ ->
  (curr.x.is_normalized -> curr.y.is_normalized -> next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ next.y.is_normalized) := by
  dsimp only [table_norm]
  simp only [Vector.map, Vector.init, Vector.push, Nat.reduceAdd, Vector.nil, Nat.cast_zero,
    Fin.isValue, Fin.coe_fin_one, Fin.val_zero, add_zero, List.nil_append, Nat.cast_one,
    Fin.val_one, zero_add, List.singleton_append, Nat.cast_ofNat, Fin.val_two, List.cons_append,
    Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.val_natCast, List.map_cons, List.map_nil,
    PNat.val_ofNat, Nat.add_one_sub_one, Nat.reduceMod, Nat.add_zero, List.length_cons,
    List.length_singleton, and_true, Nat.reducePow, and_imp]
  intros h_add h_eq
  clear h_eq

  -- TODO: why can't simp figure out those relations?
  rw [
    show ((3 : Fin 4).val % 6 % 7 % 8) = 3 by rfl,
    show ((4 : Fin 5).val % 7 % 8) = 4 by rfl,
    show (((5 : Fin 6).val % 8)) = 5 by rfl,
    show ((6 : Fin 7).val) = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
  ] at h_add

  dsimp only [Circuit.subcircuit_soundness] at h_add
  change _ ∧ _ ∧ _ → (Gadgets.Addition32Full.circuit.spec _ _) at h_add
  rw [and_imp, and_imp] at h_add
  intro h_norm_x h_norm_y
  -- TODO this unification is slow
  specialize h_add h_norm_x h_norm_y

  -- TODO this simp is slow
  simp only [Expression.eval, zero_ne_one, or_false, eval, Vector.map, size, Nat.reduceAdd, to_vars,
    to_elements, List.map_cons, Trace.getLeFromBottom, Row.get, Vector.get, List.length_cons,
    List.length_singleton, rec_vars_curr, CellOffset.curr, Fin.isValue, Fin.cast_eq_self,
    List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_one, List.getElem_cons_succ,
    Fin.val_two, List.map_nil, Vector.instAppend, Vector.append, List.cons_append, List.nil_append,
    rec_vars_next, CellOffset.next, SubCircuit.witness_length, FlatOperation.witness_length,
    add_zero, true_implies, from_elements] at h_add
  simp only [
    show (3 : Fin 8).val = 3 by rfl,
    show (4 : Fin 8).val = 4 by rfl,
    show (5 : Fin 8).val = 5 by rfl,
    show (6 : Fin 8).val = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
  ] at h_add
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_add
  dsimp only [Gadgets.Addition32Full.circuit, Gadgets.Addition32Full.spec] at h_add
  simp only [ZMod.val_zero, add_zero] at h_add
  change (next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ _ ∧ next.y.is_normalized ∧ _) at h_add
  exact ⟨h_add.left, h_add.right.right.left⟩

/--
  Main lemma that shows that if the constraints hold over the two-row window, then the spec of
  the equality assertion is satisfied, namely that curr.y = next.x
-/
lemma lift_rec_eq (curr : Row (F p) RowType) (next : Row (F p) RowType)
  : TableConstraint.constraints_hold_on_window recursive_relation ⟨<+> +> curr +> next, by simp [Trace.len]⟩ ->
  curr.y = next.x := by

  simp only [table_norm, TableConstraint.constraints_hold_on_window,
    TableConstraint.constraints_hold_on_window.foldl,
    Gadgets.Addition32Full.instProvableTypeInputs.eq_1, List.length_cons, List.length_singleton,
    Nat.reduceAdd, ProvableType.from_elements, Vector.map, ProvableType.size,
    PNat.val_ofNat, Vector.init, Vector.push, Vector.nil, Nat.cast_zero, Fin.isValue,
    Fin.coe_fin_one, Fin.val_zero, add_zero, List.nil_append, Nat.cast_one, Fin.val_one, zero_add,
    List.singleton_append, Nat.cast_ofNat, Fin.val_two, List.cons_append, Fin.coe_eq_castSucc,
    Fin.coe_castSucc, Fin.val_natCast, List.map_cons, List.map_nil,
    TableConstraintOperation.update_context, ge_iff_le, zero_le, decide_True, Bool.true_and,
    decide_eq_true_eq, sub_zero, Bool.and_eq_true, TraceOfLength.get, Trace.len,
    Nat.succ_eq_add_one, Nat.add_one_sub_one, Fin.cast_val_eq_self, Nat.reduceMod, Nat.add_zero,
    Expression.eval, Fin.zero_eta, Vector.get, Fin.cast_zero,
    List.get_eq_getElem, CellOffset.next, and_true, and_imp]
  intros _ h_eq

  rw [
    show ((3 : Fin 4).val % 6 % 7 % 8) = 3 by rfl,
    show ((4 : Fin 5).val % 7 % 8) = 4 by rfl,
    show (((5 : Fin 6).val % 8)) = 5 by rfl,
    show ((6 : Fin 7).val) = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl,
  ] at h_eq

  simp only [List.length_nil, Nat.reduceAdd, Gadgets.Addition32Full.circuit,
    Gadgets.Addition32Full.instProvableTypeInputs.eq_1, List.length_cons, List.length_singleton,
    Fin.isValue, Nat.reduceMod, Circuit.formal_assertion_to_subcircuit,
    Gadgets.Equality.U32.circuit, Circuit.subassertion_soundness, Gadgets.Equality.U32.spec, eval,
    from_elements, Vector.map, to_vars, List.map_cons, Expression.eval, Trace.getLeFromBottom,
    Row.get, Vector.get, ProvableType.to_elements, rec_vars_curr, rec_vars_next, CellOffset.curr,
    Fin.cast_eq_self, List.get_eq_getElem, CellOffset.next, Fin.val_one, List.getElem_cons_succ,
    List.getElem_cons_zero, Fin.val_two, List.map_nil, U32.mk.injEq, true_implies] at h_eq

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

/--
  Definition of the formal table for fibonacci32
-/
def formal_fib32_table : FormalTable (F p) RowType := {
  constraints := fib32_table,
  assumptions := assumptions,
  spec := spec,
  soundness := by
    intro N trace
    simp only [assumptions, gt_iff_lt, Fin.isValue, and_imp, Fin.isValue, fib32_table, spec]
    rw [TraceOfLength.forAllRowsOfTraceWithIndex, TraceOfLength.forAllRowsOfTrace, table_constraints_hold]
    intro _N_assumption

    /-
      We prove the soundness of the table by induction on the trace.
    -/
    induction' trace.val using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    -- base case 1
    · simp [table_norm]

    -- base case 2
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

      simp only [boundary_vars]
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
      simp only [U32.is_normalized, b0, b1, b2, b3]
      simp only [ZMod.val_zero, Nat.ofNat_pos, and_self]

    -- inductive step
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
      let ⟨curr_fib0, curr_fib1, curr_normalized_x⟩ := ih2.left

      simp only [and_true]

      -- lift the constraints to spec
      have add_spec := lift_rec_add curr next constraints_hold.left
      have eq_spec := lift_rec_eq curr next constraints_hold.left

      -- and now we can reason at high level with U32s
      specialize add_spec curr_normalized_x lookup_h.right.left
      simp only [fib32, Nat.reducePow]
      rw [←curr_fib0, ←curr_fib1, ←eq_spec]
      simp only [curr_fib1, Trace.len, Nat.succ_eq_add_one, add_spec,
        Nat.reducePow, lookup_h, and_self]
}

end Tables.Fibonacci32
