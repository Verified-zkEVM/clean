import Clean.Table.Basic

namespace Trace
variable {F : Type} {S : Type → Type} [ProvableType S]

/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  account the previous two rows.
-/
def every_row_two_rows_induction {P : Trace F S → Sort*}
    (zero : P (<+>))
    (one : ∀ row : Row F S, P (empty +> row))
    (more : ∀ curr next : Row F S,
      ∀ rest : Trace F S, P (rest) → P (rest +> curr) → P (rest +> curr +> next))
    : ∀ trace, P trace
  | <+> => zero
  | <+> +> first => one first
  | rest +> curr +> _ => more _ _ _
    (every_row_two_rows_induction zero one more (rest))
    (every_row_two_rows_induction zero one more (rest +> curr))

/--
  This induction principle states that if a trace length is at least two, then to prove a property
  about the whole trace, we can provide just a proof for the first two rows, and then a proof
  for the inductive step.
-/
def everyRowTwoRowsInduction' {P : (t : Trace F S) → t.len ≥ 2 → Sort*}
    (base : ∀ first second, P (<+> +> first +> second) (show 2 ≤ 2 by norm_num))
    (more : ∀ (row : Row F S) (rest : Trace F S) (h : rest.len ≥ 2),
      P rest h → P (rest +> row) (Nat.le_succ_of_le h))
    : ∀ (trace : Trace F S) (h : trace.len ≥ 2), P trace h
  -- the cases where the trace is empty or has only one row are trivial,
  -- since the length is greater than 2
  | <+> => by intro; contradiction
  | <+> +> first => by intro; contradiction
  | <+> +> first +> second => fun _ => base first second
  | rest +> prev +> curr +> next => fun h =>
    have h_len : 2 ≤ rest.len + 2 := by simp
    let ih := everyRowTwoRowsInduction' base more (rest +> prev +> curr) h_len
    more next (rest +> prev +> curr) h_len ih

end Trace

namespace TraceOfLength
variable {F : Type} {S : Type → Type} [ProvableType S] (N : ℕ)
/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  account the previous two rows.
-/
def every_row_two_rows_induction {P : (N : ℕ) → TraceOfLength F S N → Sort*}
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
      (every_row_two_rows_induction zero one more N ⟨rest, eq⟩)
      (every_row_two_rows_induction zero one more (N + 1) ⟨rest +> curr, by rw [Trace.len, eq]⟩)

def everyRowTwoRowsInduction' {P : (N : ℕ+) → TraceOfLength F S N → Prop}
    (one : ∀ row : Row F S, P 1 ⟨<+> +> row, rfl⟩)
    (more : ∀ (N : ℕ) (curr next : Row F S) (rest : TraceOfLength F S N),
      P ⟨N + 1, Nat.succ_pos N⟩ ⟨rest.val +> curr, by simp [Trace.len, rest.property]⟩ →
      P ⟨N + 2, Nat.succ_pos (N + 1)⟩ ⟨rest.val +> curr +> next, by simp [Trace.len, rest.property]⟩)
    : ∀ N trace, P N trace := by
  intro N trace
  let P' (N : ℕ) (trace : TraceOfLength F S N) : Prop :=
    if h : N = 0 then True else P ⟨N, Nat.pos_iff_ne_zero.mpr h⟩ trace
  have goal' := every_row_two_rows_induction (P:=P') trivial one (by
    intro N curr next rest h_rest h_curr
    exact more N curr next rest h_curr) N trace
  simpa [P', N.pos] using goal'

def two_row_induction {prop : Row F S → ℕ → Prop}
    (zero : ∀ first_row : Row F S, prop first_row 0)
    (succ : ∀ (N : ℕ) (curr next : Row F S), prop curr N → prop next (N + 1))
    : ∀ N (trace : TraceOfLength F S N), ForAllRowsOfTraceWithIndex trace prop := by
  intro N trace
  simp only [ForAllRowsOfTraceWithIndex, Trace.ForAllRowsOfTraceWithIndex]
  induction trace.val using Trace.every_row_two_rows_induction with
  | zero => trivial
  | one first_row =>
    simp only [Trace.ForAllRowsOfTraceWithIndex.inner]
    exact ⟨ zero first_row, trivial ⟩
  | more curr next rest _ ih2 =>
    simp only [Trace.ForAllRowsOfTraceWithIndex.inner] at *
    have h3 : prop next (rest +> curr).len := succ _ _ _ ih2.left
    exact ⟨ h3, ih2.left, ih2.right ⟩

theorem lastRow_of_forAllWithIndex {N : ℕ+} {prop : Row F S → ℕ → Prop}
  (trace : TraceOfLength F S N) (h : ForAllRowsOfTraceWithIndex trace prop) :
    prop trace.lastRow (N - 1) := by
  induction N, trace using everyRowTwoRowsInduction' with
  | one row =>
    simp only [table_norm, and_true] at h
    exact h
  | more N curr next rest ih =>
    simp only [table_norm] at h ⊢
    rw [rest.property] at h
    exact h.left

theorem lastRow_of_forAllWithPrevious {N : ℕ+} {prop : Row F S → (i : ℕ) → TraceOfLength F S i → Prop}
  (trace : TraceOfLength F S N) (h : ForAllRowsWithPrevious trace prop) :
    prop trace.lastRow (N - 1) trace.tail := by
  induction N, trace using everyRowTwoRowsInduction' with
  | one row =>
    simp only [ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, and_true] at h
    exact h
  | more N curr next rest ih =>
    rcases rest with ⟨ rest, hN ⟩
    subst hN
    simp only [ForAllRowsWithPrevious, Trace.ForAllRowsWithPrevious, table_norm] at h ⊢
    simp only [PNat.mk_coe, Nat.add_one_sub_one, tail, Trace.tail]
    exact h.left

end TraceOfLength

variable {F : Type} [Field F] {S : Type → Type} [ProvableType S] {W : ℕ+}

namespace CellAssignment

def pushVarInput_offset (assignment : CellAssignment W S) (off : CellOffset W S) :
  (assignment.pushVarInput off).offset = assignment.offset + 1 := by
  simp [pushVarInput, Vector.push]

lemma pushRow_offset (assignment : CellAssignment W S) (row : Fin W) :
  (assignment.pushRow row).offset = assignment.offset + size S := rfl

theorem assignmentFromCircuit_offset (as : CellAssignment W S) (ops : Operations F) :
    (assignmentFromCircuit as ops).offset = as.offset + ops.localLength := by
  induction ops using Operations.induct generalizing as with
  | empty => rfl
  | witness | assert | lookup | subcircuit =>
    simp_all +arith [assignmentFromCircuit, CellAssignment.pushVarsAux, Operations.localLength]

theorem assignmentFromCircuit_vars (as : CellAssignment W S) (ops : Operations F) :
    (assignmentFromCircuit as ops).vars = (as.vars ++ (.mapRange ops.localLength fun i => .aux (as.aux_length + i) : Vector (Cell W S) _)
      ).cast (assignmentFromCircuit_offset ..).symm := by
  induction ops using Operations.induct generalizing as with
  | empty => rfl
  | witness | assert | lookup | subcircuit =>
    simp_all +arith [assignmentFromCircuit, pushVarsAux, Operations.localLength,
      Vector.mapRange_add_eq_append, Vector.cast, Array.append_assoc]

theorem setVarInput_offset (assignment : CellAssignment W S) (off : CellOffset W S) (var : ℕ) :
    (assignment.setVarInput off var).offset = assignment.offset := by
  simp [setVarInput]

theorem setVarInput_vars_getElem_eq (assignment : CellAssignment W S) (off : CellOffset W S) (var : ℕ)
    (h : var < assignment.offset) :
    (assignment.setVarInput off var).vars[var]'(by rw [setVarInput_offset]; exact h) = .input off := by
  simp only [setVarInput, Vector.set?]
  simp

theorem setVarInput_vars_getElem_ne (assignment : CellAssignment W S) (off : CellOffset W S) (var : ℕ)
    (i : ℕ) (hi : i < assignment.offset) (hne : i ≠ var) :
    (assignment.setVarInput off var).vars[i]'(by rw [setVarInput_offset]; exact hi) = assignment.vars[i] := by
  simp only [setVarInput, Vector.set?]
  simp [hne.symm]

/-- The offset is preserved by a foldl of setVarInput calls. -/
theorem setVarInput_foldl_offset
    (pairs : List (CellOffset W S × ℕ))
    (assignment : CellAssignment W S) :
    (pairs.foldl (fun a p => a.setVarInput p.1 p.2) assignment).offset = assignment.offset := by
  induction pairs generalizing assignment with
  | nil => rfl
  | cons p ps ih =>
    unfold List.foldl
    rw [ih, setVarInput_offset]

/-- Composing multiple `setVarInput` calls preserves entries whose index
    is not among the targets. -/
theorem setVarInput_foldl_preserves
    (pairs : List (CellOffset W S × ℕ))
    (assignment : CellAssignment W S)
    (j : ℕ) (hj : j < assignment.offset)
    (h_ne : ∀ pair ∈ pairs, pair.2 ≠ j) :
    (pairs.foldl (fun a p => a.setVarInput p.1 p.2) assignment).vars[j]'(by
      rw [setVarInput_foldl_offset]; exact hj) = assignment.vars[j] := by
  induction pairs generalizing assignment with
  | nil => rfl
  | cons p ps ih =>
    show (ps.foldl (fun a p => a.setVarInput p.1 p.2)
      (assignment.setVarInput p.1 p.2)).vars[j]'_ = assignment.vars[j]
    exact (ih (assignment.setVarInput p.1 p.2) (by rw [setVarInput_offset]; exact hj)
      (fun pair hp => h_ne pair (List.mem_cons_of_mem _ hp))).trans
      (setVarInput_vars_getElem_ne assignment p.1 p.2 j hj
        (h_ne p (List.mem_cons.mpr (Or.inl rfl))).symm)

/-- Composing multiple `setVarInput` calls: the last call for a given index wins,
    provided no later call targets the same index. -/
theorem setVarInput_foldl_last
    (before : List (CellOffset W S × ℕ))
    (off : CellOffset W S) (idx : ℕ)
    (after : List (CellOffset W S × ℕ))
    (assignment : CellAssignment W S)
    (hidx : idx < assignment.offset)
    (h_ne_after : ∀ pair ∈ after, pair.2 ≠ idx) :
    ((before ++ [(off, idx)] ++ after).foldl (fun a p => a.setVarInput p.1 p.2) assignment).vars[idx]'(by
      rw [setVarInput_foldl_offset]; exact hidx) = .input off := by
  induction before generalizing assignment with
  | nil =>
    show (after.foldl (fun a p => a.setVarInput p.1 p.2) (assignment.setVarInput off idx)).vars[idx]'_ = .input off
    rw [setVarInput_foldl_preserves after _ idx (by rw [setVarInput_offset]; exact hidx) h_ne_after]
    exact setVarInput_vars_getElem_eq assignment off idx hidx
  | cons p ps ih =>
    show ((ps ++ [(off, idx)] ++ after).foldl (fun a p => a.setVarInput p.1 p.2)
      (assignment.setVarInput p.1 p.2)).vars[idx]'_ = .input off
    exact ih (assignment.setVarInput p.1 p.2) (by rw [setVarInput_offset]; exact hidx)

/-- If all second components of `pairs` are pairwise distinct and all indices are within
    `assignment.offset`, then the foldl of `setVarInput` maps `idx` to `.input off`,
    where `pairs[k] = (off, idx)`.

    This lemma avoids list decomposition (unlike `setVarInput_foldl_last`),
    working by induction on the list instead, which sidesteps dependent-type issues
    when rewriting inside `Vector.getElem`. -/
theorem setVarInput_foldl_at
    (pairs : List (CellOffset W S × ℕ))
    (assignment : CellAssignment W S)
    (off : CellOffset W S) (idx : ℕ)
    (k : ℕ) (hk : k < pairs.length)
    (h_at : pairs[k]'hk = (off, idx))
    (h_nodup : ∀ (i j : ℕ) (hi : i < pairs.length) (hj : j < pairs.length),
      i ≠ j → (pairs[i]'hi).2 ≠ (pairs[j]'hj).2)
    (h_bound : idx < assignment.offset) :
    (pairs.foldl (fun a p => a.setVarInput p.1 p.2) assignment).vars[idx]'(by
      rw [setVarInput_foldl_offset]; exact h_bound) = .input off := by
  induction pairs generalizing k assignment with
  | nil => simp at hk
  | cons p ps ih =>
    simp only [List.foldl_cons]
    cases k with
    | zero =>
      have hp_eq : p = (off, idx) := by simpa using h_at
      subst hp_eq
      rw [setVarInput_foldl_preserves ps _ idx
        (by rw [setVarInput_offset]; exact h_bound)
        (fun pair hp_mem => by
          rw [List.mem_iff_getElem] at hp_mem
          obtain ⟨j, hj_lt, hj_eq⟩ := hp_mem
          have h_ne := h_nodup 0 (j + 1) (by simp) (by simp; omega) (by omega)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h_ne
          rw [← hj_eq]; exact h_ne.symm)]
      exact setVarInput_vars_getElem_eq assignment off idx h_bound
    | succ k' =>
      exact ih (assignment.setVarInput p.1 p.2) k' (by simp [List.length] at hk; omega)
        (by simpa using h_at)
        (fun i j hi hj hij => h_nodup (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega))
        (by rw [setVarInput_offset]; exact h_bound)

end CellAssignment
