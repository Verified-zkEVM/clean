import Clean.Table.Basic

namespace Trace
variable {F : Type} {S : Type → Type} [ProvableType S]

/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  account the previous two rows.
-/
def everyRowTwoRowsInduction {P : Trace F S → Sort*}
    (zero : P (<+>))
    (one : ∀ row : Row F S, P (empty +> row))
    (more : ∀ curr next : Row F S,
      ∀ rest : Trace F S, P (rest) → P (rest +> curr) → P (rest +> curr +> next))
    : ∀ trace, P trace
  | <+> => zero
  | <+> +> first => one first
  | rest +> curr +> _ => more _ _ _
    (everyRowTwoRowsInduction zero one more (rest))
    (everyRowTwoRowsInduction zero one more (rest +> curr))

lemma len_le_succ (trace : Trace F S) (row : Row F S) :
    trace.len ≤ (trace +> row).len :=
  match trace with
  | <+> => by simp only [len, Nat.succ_eq_add_one, zero_add, zero_le]
  | (rest +> _) =>
    by simp only [len, Nat.succ_eq_add_one, le_add_iff_nonneg_right, zero_le]

lemma len_ge_succ_of_ge {N : ℕ} (trace : Trace F S) (row : Row F S) (_h : trace.len ≥ N) :
    (trace +> row).len ≥ N :=
  match trace with
  | <+> => by
      simp only [len, ge_iff_le, nonpos_iff_eq_zero, Nat.succ_eq_add_one, zero_add] at *
      simp only [_h, zero_le]
  | (rest +> row) => by simp only [len, Nat.succ_eq_add_one, ge_iff_le] at *; linarith

/--
  This induction principle states that if a trace length is at leas two, then to prove a property
  about the whole trace, we can provide just a proof for the first two rows, and then a proof
  for the inductive step.
-/
def everyRowTwoRowsInduction' {P : (t : Trace F S) → t.len ≥ 2 → Sort*}
    (base : ∀ first second (h : (<+> +> first +> second).len ≥ 2), P (<+> +> first +> second) h)
    (more : ∀ curr next : Row F S,
      ∀ (rest : Trace F S) (h : rest.len ≥ 2),
        P rest h →
        P (rest +> curr) (len_ge_succ_of_ge _ _ h) →
        P (rest +> curr +> next) (len_ge_succ_of_ge _ _ (len_ge_succ_of_ge _ _ h)))
    : ∀ (trace : Trace F S) (h : trace.len ≥ 2), P trace h
  -- the cases where the trace is empty or has only one row are trivial,
  -- since the length is greater than 2
  | <+> => by intro h; contradiction
  | <+> +> first => by intro h; contradiction
  | <+> +> first +> second => fun h => base first second h
  | rest +> curr +> next =>
      let ih' := (everyRowTwoRowsInduction' base more (rest))
      let ih'' := (everyRowTwoRowsInduction' base more (rest +> curr))
      (Nat.lt_or_ge 2 rest.len).by_cases
        -- TODO: this definition should be similar to Nat.letRec
        (by sorry)
        (by sorry)

end Trace

namespace TraceOfLength
variable {F : Type} {S : Type → Type} [ProvableType S] (N : ℕ)
/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  account the previous two rows.
-/
def everyRowTwoRowsInduction {P : (N : ℕ) → TraceOfLength F S N → Sort*}
    (zero : P 0 ⟨<+>, rfl⟩)
    (one : ∀ row : Row F S, P 1 ⟨<+> +> row, rfl⟩)
    (more : ∀ (N : ℕ) (curr next : Row F S),
      ∀ rest : TraceOfLength F S N, P N (rest) →
        P (N + 1) ⟨rest.val +> curr, by rw [Trace.len, rest.property]⟩ →
        P (N + 2) ⟨rest.val +> curr +> next, by simp only [Trace.len, rest.property]⟩)
    : ∀ N trace, P N trace
  | 0, ⟨<+>, _⟩ => zero
  | 1, ⟨<+> +> first, _⟩ => one first
  | N + 2, ⟨rest +> curr +> next, (h : rest.len + 2 = N + 2)⟩ => by
    have eq : rest.len = N := by rw [Nat.add_left_inj] at h; exact h
    exact more N curr next ⟨rest, eq⟩
      (everyRowTwoRowsInduction zero one more N ⟨rest, eq⟩)
      (everyRowTwoRowsInduction zero one more (N + 1) ⟨rest +> curr, by rw [Trace.len, eq]⟩)

def everyRowTwoRowsInduction' {P : (N : ℕ+) → TraceOfLength F S N → Prop}
    (one : ∀ row : Row F S, P 1 ⟨<+> +> row, rfl⟩)
    (more : ∀ (N : ℕ) (curr next : Row F S) (rest : TraceOfLength F S N),
      P ⟨N + 1, Nat.succ_pos N⟩ ⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩ →
      P ⟨N + 2, Nat.succ_pos (N + 1)⟩ ⟨rest.val +> curr +> next, by simp [Trace.len, rest.property]⟩)
    : ∀ N trace, P N trace := by
  intro N trace
  let P' (N : ℕ) (trace : TraceOfLength F S N) : Prop :=
    if h : N = 0 then True else P ⟨N, Nat.pos_iff_ne_zero.mpr h⟩ trace
  have goal' := everyRowTwoRowsInduction (P:=P') trivial one (by
    intro N curr next rest h_rest h_curr
    exact more N curr next rest h_curr) N trace
  simpa [P', N.pos] using goal'

def twoRowInduction {prop : Row F S → ℕ → Prop}
    (zero : ∀ first_row : Row F S, prop first_row 0)
    (succ : ∀ (N : ℕ) (curr next : Row F S), prop curr N → prop next (N + 1))
    : ∀ N (trace : TraceOfLength F S N), forAllRowsOfTraceWithIndex trace prop := by
  intro N trace
  simp only [forAllRowsOfTraceWithIndex]
  induction trace.val using Trace.everyRowTwoRowsInduction with
  | zero => trivial
  | one first_row =>
    simp only [forAllRowsOfTraceWithIndex.inner]
    exact ⟨ zero first_row, trivial ⟩
  | more curr next rest _ ih2 =>
    simp only [forAllRowsOfTraceWithIndex.inner] at *
    have h3 : prop next (rest +> curr).len := succ _ _ _ ih2.left
    exact ⟨ h3, ih2.left, ih2.right ⟩

end TraceOfLength

variable {F : Type} [Field F] {S : Type → Type} [ProvableType S] {W : ℕ+}

namespace CellAssignment

def push_var_input_offset (assignment: CellAssignment W S) (off: CellOffset W S) :
  (assignment.push_var_input off).offset = assignment.offset + 1 := by
  simp [push_var_input, Vector.push]

lemma push_row_offset (assignment: CellAssignment W S) (row: Fin W) :
  (assignment.push_row row).offset = assignment.offset + size S := by rfl

theorem assignment_from_circuit_offset (as: CellAssignment W S) (ops: Operations F) :
    (assignment_from_circuit as ops).offset = as.offset + ops.local_length := by
  induction ops using Operations.induct generalizing as with
  | empty => rfl
  | witness | assert | lookup | subcircuit =>
    simp_all +arith [assignment_from_circuit, CellAssignment.push_vars_aux, Operations.local_length]

theorem assignment_from_circuit_vars (as: CellAssignment W S) (ops: Operations F) :
    (assignment_from_circuit as ops).vars = (as.vars ++ (.mapRange ops.local_length fun i => .aux (as.aux_length + i) : Vector (Cell W S) _)
      ).cast (assignment_from_circuit_offset ..).symm := by
  induction ops using Operations.induct generalizing as with
  | empty => rfl
  | witness | assert | lookup | subcircuit =>
    simp_all +arith [assignment_from_circuit, push_vars_aux, Operations.local_length,
      Vector.mapRange_add_eq_append, Vector.cast, Array.append_assoc]

end CellAssignment
