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

instance : ProvableType RowType where
  size := 8
  to_elements s := #v[s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3]
  from_elements v :=
    -- TODO is it possible to define in terms of ProvableType.from_elements of the U32?
    let ⟨ .mk [x0, x1, x2, x3, y0, y1, y2, y3], _ ⟩ := v
    ⟨ ⟨ x0, x1, x2, x3 ⟩, ⟨ y0, y1, y2, y3 ⟩ ⟩

@[reducible]
def next_row_off : RowType (CellOffset 2 RowType) := {
  x := ⟨.next 0, .next 1, .next 2, .next 3⟩,
  y := ⟨.next 4, .next 5, .next 6, .next 7⟩
}

@[reducible]
def assign_U32 (offs : U32 (CellOffset 2 RowType)) (x : Var U32 (F p)) : TwoRowsConstraint RowType (F p) := do
  assign offs.x0 x.x0
  assign offs.x1 x.x1
  assign offs.x2 x.x2
  assign offs.x3 x.x3

/--
  inductive contraints that are applied every two rows of the trace.
-/
def recursive_relation : TwoRowsConstraint RowType (F p) := do
  let curr ← TableConstraint.get_curr_row
  let next ← TableConstraint.get_next_row

  let { z, ..} ← subcircuit Gadgets.Addition32Full.circuit {
    x := curr.x,
    y := curr.y,
    carry_in := 0
  }

  assign_U32 next_row_off.y z
  assertion Gadgets.Equality.U32.circuit ⟨curr.y, next.x⟩

/--
  Boundary constraints that are applied at the beginning of the trace.
-/
def boundary : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.get_curr_row
  assertion Gadgets.Equality.U32.circuit ⟨row.x, ⟨0, 0, 0, 0⟩⟩
  assertion Gadgets.Equality.U32.circuit ⟨row.y, ⟨1, 0, 0, 0⟩⟩

/--
  The fib32 table is composed of the boundary and recursive relation constraints.
-/
def fib32_table : List (TableOperation RowType (F p)) := [
  .Boundary 0 boundary,
  .EveryRowExceptLast recursive_relation,
]

/--
  Specification for fibonacci32: for each row with index i
  - the first U32 value is the i-th fibonacci number
  - the second U32 value is the (i+1)-th fibonacci number
  - both U32 values are normalized
-/
def spec {N : ℕ} (trace : TraceOfLength (F p) RowType N) : Prop :=
  trace.forAllRowsOfTraceWithIndex (fun row index =>
    (row.x.value = fib32 index) ∧
    (row.y.value = fib32 (index + 1)) ∧
    row.x.is_normalized ∧ row.y.is_normalized
  )

/-
  First of all, we prove some lemmas about the mapping variables -> cell offsets
  for both boundary and recursive relation
  Those are too expensive to prove in-line, so we prove them here and use them later
-/
omit p_large_enough in
lemma boundary_vars (first_row: Row (F p) RowType) (aux_env : Environment (F p)) :
    let env := boundary.window_env ⟨<+> +> first_row, rfl⟩ aux_env;
    env.get 0 = first_row.x.x0 ∧
    env.get 1 = first_row.x.x1 ∧
    env.get 2 = first_row.x.x2 ∧
    env.get 3 = first_row.x.x3 ∧
    env.get 4 = first_row.y.x0 ∧
    env.get 5 = first_row.y.x1 ∧
    env.get 6 = first_row.y.x2 ∧
    env.get 7 = first_row.y.x3
  := by
  repeat constructor

variable {α : Type}

lemma fib_vars_curr (curr next : Row (F p) RowType) (aux_env : Environment (F p)) :
    let env := recursive_relation.window_env ⟨<+> +> curr +> next, rfl⟩ aux_env;
    env.get 0 = curr.x.x0 ∧
    env.get 1 = curr.x.x1 ∧
    env.get 2 = curr.x.x2 ∧
    env.get 3 = curr.x.x3 ∧
    env.get 4 = curr.y.x0 ∧
    env.get 5 = curr.y.x1 ∧
    env.get 6 = curr.y.x2 ∧
    env.get 7 = curr.y.x3
  := by
  intro env
  dsimp only [env, window_env]
  have h_offset : (recursive_relation (p:=p)).final_assignment.offset = 24 := rfl
  simp only [h_offset, reduceDIte, Nat.reduceLT]
  dsimp only [recursive_relation, table_assignment_norm, circuit_norm,
    Gadgets.Addition32Full.circuit, assign_U32, Gadgets.Equality.U32.circuit]
  simp only [circuit_norm, table_norm]
  simp [Trace.getLeFromBottom]
  and_intros <;> rfl

/-- TODO this is much faster than `fib_vars_curr`, but need to figure out how to prove
  statements about individual indices with it -/
lemma fib_vars_curr' :
   (recursive_relation (p:=p)).final_assignment.vars.toArray.extract 0 8 =
   #[.input ⟨0, 0⟩, .input ⟨0, 1⟩, .input ⟨0, 2⟩, .input ⟨0, 3⟩,
     .input ⟨0, 4⟩, .input ⟨0, 5⟩, .input ⟨0, 6⟩, .input ⟨0, 7⟩] := by
    dsimp only [recursive_relation, table_assignment_norm, circuit_norm,
      Gadgets.Addition32Full.circuit, assign_U32, Gadgets.Equality.U32.circuit]
    simp only [circuit_norm, table_norm]
    simp only [circuit_norm, table_norm, List.extract_eq_drop_take, List.take_succ_cons, List.take_zero, List.drop_zero, seval]
    rfl

lemma fib_vars_next (curr next : Row (F p) RowType) (aux_env : Environment (F p)) :
    let env := recursive_relation.window_env ⟨<+> +> curr +> next, rfl⟩ aux_env;
    env.get 8 = next.x.x0 ∧
    env.get 9 = next.x.x1 ∧
    env.get 10 = next.x.x2 ∧
    env.get 11 = next.x.x3 ∧
    env.get 16 = next.y.x0 ∧
    env.get 18 = next.y.x1 ∧
    env.get 20 = next.y.x2 ∧
    env.get 22 = next.y.x3
  := by
  intro env
  dsimp only [env, window_env]
  have h_offset : (recursive_relation (p:=p)).final_assignment.offset = 24 := rfl
  simp only [h_offset, reduceDIte, Nat.reduceLT]
  dsimp only [recursive_relation, table_assignment_norm, circuit_norm,
    Gadgets.Addition32Full.circuit, assign_U32, Gadgets.Equality.U32.circuit]
  simp only [circuit_norm, table_norm]
  simp [Trace.getLeFromBottom]
  and_intros <;> rfl

/--
  Main lemma that shows that if the constraints hold over the two-row window,
  then the spec of add32 and equality are satisfied
-/
lemma lift_constraints (curr next : Row (F p) RowType) (aux_env : Environment (F p))
  : recursive_relation.constraints_hold_on_window ⟨<+> +> curr +> next, rfl⟩ aux_env →
  curr.y = next.x ∧
  (curr.x.is_normalized → curr.y.is_normalized → next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ next.y.is_normalized)
   := by
  simp only [table_norm]
  obtain ⟨ hcurr_x0, hcurr_x1, hcurr_x2, hcurr_x3, hcurr_y0, hcurr_y1, hcurr_y2, hcurr_y3 ⟩ := fib_vars_curr curr next aux_env
  obtain ⟨ hnext_x0, hnext_x1, hnext_x2, hnext_x3, hnext_y0, hnext_y1, hnext_y2, hnext_y3 ⟩ := fib_vars_next curr next aux_env
  set env := recursive_relation.window_env  ⟨<+> +> curr +> next, rfl⟩ aux_env
  dsimp only [table_norm, circuit_norm, recursive_relation, assign_U32,
    Gadgets.Equality.U32.circuit, Gadgets.Addition32Full.circuit
  ]
  rintro ⟨ ⟨_, h_add⟩, h_eq ⟩
  simp only [table_norm, circuit_norm, subcircuit_norm] at h_add h_eq
  simp [
    show (3 : Fin 8).val = 3 by rfl,
    show (4 : Fin 8).val = 4 by rfl,
    show (5 : Fin 8).val = 5 by rfl,
    show (6 : Fin 8).val = 6 by rfl,
    show (7 : Fin 8).val = 7 by rfl
  ] at h_add
  conv at h_eq =>
    congr
    · skip
    · simp [
        show (3 : Fin 8).val = 3 by rfl,
        show (4 : Fin 8).val = 4 by rfl,
        show (5 : Fin 8).val = 5 by rfl,
        show (6 : Fin 8).val = 6 by rfl,
        show (7 : Fin 8).val = 7 by rfl
      ]
  rw [hcurr_x0, hcurr_x1, hcurr_x2, hcurr_x3, hcurr_y0, hcurr_y1, hcurr_y2, hcurr_y3, hnext_y0, hnext_y1, hnext_y2, hnext_y3] at h_add
  rw [hcurr_y0, hcurr_y1, hcurr_y2, hcurr_y3, hnext_x0, hnext_x1, hnext_x2, hnext_x3] at h_eq
  constructor
  · rw [Gadgets.Equality.U32.spec, true_implies] at h_eq
    exact h_eq
  rw [Gadgets.Addition32Full.assumptions, Gadgets.Addition32Full.spec] at h_add
  intro h_norm_x h_norm_y
  specialize h_add ⟨ h_norm_x, h_norm_y, by simp ⟩
  rw [ZMod.val_zero, add_zero] at h_add
  change (next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ _ ∧ next.y.is_normalized ∧ _) at h_add
  obtain ⟨ h_add_mod, _, h_norm_nexty, _ ⟩ := h_add
  exact ⟨h_add_mod, h_norm_nexty⟩

/--
  Definition of the formal table for fibonacci32
-/
def formal_fib32_table : FormalTable (F p) RowType := {
  constraints := fib32_table,
  spec := spec,
  soundness := by
    intro N trace envs _
    simp only [fib32_table, spec]
    rw [TraceOfLength.forAllRowsOfTraceWithIndex, table_constraints_hold]

    /-
      We prove the soundness of the table by induction on the trace.
    -/
    induction' trace.val using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    -- base case 1
    · simp [table_norm]

    -- base case 2
    · simp [table_norm]
      have h_vars := boundary_vars first_row (envs 0 0)
      set env := boundary.window_env ⟨<+> +> first_row, rfl⟩ (envs 0 0)
      simp only [table_norm, boundary, circuit_norm, Gadgets.Equality.U32.circuit]
      simp only [subcircuit_norm, Gadgets.Equality.U32.spec]
      -- TODO it's annoying how we end up reasoning about the individual parts of the U32
      -- even though the gadget we used was about equality of entire U32s
      simp [circuit_norm]
      -- TODO find simp set that handles these identities?
      simp only [
        show (3 : Fin 8).val = 3 by rfl,
        show (4 : Fin 8).val = 4 by rfl,
        show (5 : Fin 8).val = 5 by rfl,
        show (6 : Fin 8).val = 6 by rfl,
        show (7 : Fin 8).val = 7 by rfl,
      ]
      obtain ⟨ hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3 ⟩ := h_vars
      rw [hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
      clear hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3

      intros b0 b1 b2 b3 b4 b5 b6 b7
      simp only [U32.value, fib32]
      simp [b0, b1, b2, b3, b4, b5, b6, b7]

      simp [ZMod.val_one]
      simp only [U32.is_normalized, b0, b1, b2, b3, b4, b5, b6, b7]
      simp only [ZMod.val_zero, ZMod.val_one, Nat.ofNat_pos, and_self]
      trivial

    -- inductive step
    · -- first of all, we prove the inductive part of the spec
      unfold TraceOfLength.forAllRowsOfTraceWithIndex.inner
      intros constraints_hold

      unfold table_constraints_hold.foldl at constraints_hold
      simp only [Trace.len, Nat.succ_ne_zero, ite_false] at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      unfold table_constraints_hold.foldl at constraints_hold
      simp only at constraints_hold
      specialize ih2 constraints_hold.right
      simp only [ih2, and_self]

      let ⟨curr_fib0, curr_fib1, curr_normalized_x, curr_normalized_y⟩ := ih2.left
      simp only [and_true]
      replace constraints_hold := constraints_hold.left

      -- simplfy constraints
      simp at constraints_hold
      have ⟨ eq_spec, add_spec ⟩ := lift_constraints curr next (envs 1 (rest.len + 1)) constraints_hold

      -- and now we can reason at high level with U32s
      specialize add_spec curr_normalized_x curr_normalized_y
      simp only [fib32, Trace.len]
      rw [←curr_fib0, ←curr_fib1, ←eq_spec]
      simp only [curr_fib1, Trace.len, Nat.succ_eq_add_one, add_spec,
        Nat.reducePow, and_self, curr_normalized_y]
}

end Tables.Fibonacci32
