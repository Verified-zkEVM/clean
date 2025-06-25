import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Theorems
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Equality
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

instance : ProvableStruct RowType where
  components := [U32, U32]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }
  combined_size := 8 -- explicit size to enable casting indices to `Fin size`

@[reducible]
def next_row_off : RowType (CellOffset 2 RowType) := {
  x := ⟨.next 0, .next 1, .next 2, .next 3⟩,
  y := ⟨.next 4, .next 5, .next 6, .next 7⟩
}

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

  let z ← subcircuit Gadgets.Addition32.circuit { x := curr.x, y := curr.y }

  assign_U32 next_row_off.y z
  curr.y === next.x

/--
  Boundary constraints that are applied at the beginning of the trace.
-/
def boundary : SingleRowConstraint RowType (F p) := do
  let row ← TableConstraint.get_curr_row
  row.x === (const (U32.from_byte 0))
  row.y === (const (U32.from_byte 1))

/--
  The fib32 table is composed of the boundary and recursive relation constraints.
-/
def fib32_table : List (TableOperation RowType (F p)) := [
  Boundary (.fromStart 0) boundary,
  EveryRowExceptLast recursive_relation,
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

variable {α : Type}

-- assignment copied from eval:
-- #eval! (recursive_relation (p:=p_babybear)).final_assignment.vars
lemma fib_assignment : (recursive_relation (p:=p)).final_assignment.vars =
   #v[.input ⟨0, 0⟩, .input ⟨0, 1⟩, .input ⟨0, 2⟩, .input ⟨0, 3⟩, .input ⟨0, 4⟩, .input ⟨0, 5⟩, .input ⟨0, 6⟩,
      .input ⟨0, 7⟩, .input ⟨1, 0⟩, .input ⟨1, 1⟩, .input ⟨1, 2⟩, .input ⟨1, 3⟩, .input ⟨1, 4⟩, .input ⟨1, 5⟩,
      .input ⟨1, 6⟩, .input ⟨1, 7⟩, .input ⟨1, 4⟩, .aux 1, .input ⟨1, 5⟩, .aux 3, .input ⟨1, 6⟩, .aux 5,
      .input ⟨1, 7⟩, .aux 7] := by
  dsimp only [table_assignment_norm, circuit_norm, recursive_relation, Gadgets.Addition32.circuit, assign_U32]
  simp only [table_assignment_norm, circuit_norm, Vector.mapFinRange_succ, Vector.mapFinRange_zero, Vector.mapRange_zero, Vector.mapRange_succ]

lemma fib_vars (curr next : Row (F p) RowType) (aux_env : Environment (F p)) :
    let env := recursive_relation.window_env ⟨<+> +> curr +> next, rfl⟩ aux_env;
    eval env (varFromOffset U32 0) = curr.x ∧
    eval env (varFromOffset U32 4) = curr.y ∧
    eval env (varFromOffset U32 8) = next.x ∧
    eval env (U32.mk (var ⟨16⟩) (var ⟨18⟩) (var ⟨20⟩) (var ⟨22⟩)) = next.y
  := by
  intro env
  dsimp only [env, window_env]
  have h_offset : (recursive_relation (p:=p)).final_assignment.offset = 24 := rfl
  simp only [h_offset]
  rw [fib_assignment]
  simp only [circuit_norm, explicit_provable_type, reduceDIte, Nat.reduceLT, Nat.reduceAdd]
  -- TODO it's annoying that we explicitly need the GetElem instance here
  simp only [PNat.mk_ofNat, Vector.instGetElemNatLt, Vector.get, Fin.cast_mk, PNat.val_ofNat,
    Fin.ofNat'_eq_cast, Nat.cast_zero, Fin.isValue, Nat.cast_one, Nat.cast_ofNat,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  and_intros <;> rfl

/--
  Main lemma that shows that if the constraints hold over the two-row window,
  then the spec of add32 and equality are satisfied
-/
lemma fib_constraints (curr next : Row (F p) RowType) (aux_env : Environment (F p))
  : recursive_relation.constraints_hold_on_window ⟨<+> +> curr +> next, rfl⟩ aux_env →
  curr.y = next.x ∧
  (curr.x.is_normalized → curr.y.is_normalized → next.y.value = (curr.x.value + curr.y.value) % 2^32 ∧ next.y.is_normalized)
   := by
  simp only [table_norm]
  obtain ⟨ hcurr_x, hcurr_y, hnext_x, hnext_y ⟩ := fib_vars curr next aux_env
  set env := recursive_relation.window_env  ⟨<+> +> curr +> next, rfl⟩ aux_env
  simp only [table_norm, circuit_norm, recursive_relation,
    assign_U32, Gadgets.Addition32.circuit]
  rintro ⟨ h_add, h_eq ⟩
  simp only [table_norm, circuit_norm, subcircuit_norm, true_implies, Nat.reduceAdd, zero_add] at h_add
  rw [hcurr_x, hcurr_y, hnext_y] at h_add
  rw [hcurr_y, hnext_x] at h_eq
  clear hcurr_x hcurr_y hnext_x hnext_y
  constructor
  · exact h_eq
  rw [Gadgets.Addition32.assumptions, Gadgets.Addition32.spec] at h_add
  intro h_norm_x h_norm_y
  specialize h_add ⟨ h_norm_x, h_norm_y ⟩
  obtain ⟨ h_add_mod, h_norm_next_y ⟩ := h_add
  exact ⟨h_add_mod, h_norm_next_y⟩

lemma boundary_constraints (first_row : Row (F p) RowType) (aux_env : Environment (F p)) :
  Circuit.constraints_hold.soundness (window_env boundary ⟨<+> +> first_row, rfl⟩ aux_env) boundary.operations →
  first_row.x.value = fib32 0 ∧ first_row.y.value = fib32 1 ∧ first_row.x.is_normalized ∧ first_row.y.is_normalized
  := by
  set env := boundary.window_env ⟨<+> +> first_row, rfl⟩ aux_env
  simp only [table_norm, boundary, circuit_norm]
  simp only [and_imp]
  have hx : eval env (varFromOffset U32 0) = first_row.x := by rfl
  have hy : eval env (varFromOffset U32 4) = first_row.y := by rfl
  rw [hx, hy]
  clear hx hy
  intro x_zero y_one
  rw [x_zero, y_one]
  simp only [U32.from_byte_is_normalized, U32.from_byte_value, fib32]
  trivial

/--
  Definition of the formal table for fibonacci32
-/
def formal_fib32_table : FormalTable (F p) RowType := {
  constraints := fib32_table,
  spec := spec,

  soundness := by
    intro N trace envs _
    simp only [fib32_table, spec]
    rw [TraceOfLength.forAllRowsOfTraceWithIndex, Trace.forAllRowsOfTraceWithIndex, table_constraints_hold]

    /-
      We prove the soundness of the table by induction on the trace.
    -/
    induction' trace.val using Trace.everyRowTwoRowsInduction with first_row curr next rest _ ih2
    -- base case 1
    · simp [table_norm]

    -- base case 2
    · simp [table_norm]
      apply boundary_constraints first_row (envs 0 0)

    -- inductive step
    · simp [table_norm] at ih2 ⊢
      intro constraints_hold boundary rest
      -- first of all, we prove the inductive part of the spec

      specialize ih2 boundary rest
      simp only [ih2, and_self, and_true]

      let ⟨curr_fib0, curr_fib1, curr_normalized_x, curr_normalized_y⟩ := ih2.left

      -- simplfy constraints
      have ⟨ eq_spec, add_spec ⟩ := fib_constraints curr next (envs 1 _) constraints_hold

      -- finish induction
      specialize add_spec curr_normalized_x curr_normalized_y
      simp only [fib32, Trace.len]
      rw [←curr_fib0, ←curr_fib1, ←eq_spec]
      simp only [curr_fib1, Trace.len, Nat.succ_eq_add_one, add_spec,
        Nat.reducePow, and_self, curr_normalized_y]
}

end Tables.Fibonacci32
