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

end CellAssignment

/-! ### Offset consistency preservation

We define a predicate `PreservesOffsetConsistency` on `TableConstraint`s and prove it for
all primitive operations and their compositions (bind, forM). This lets us prove
`OffsetConsistent` for complex table constraints that involve loops over abstract types.
-/

section OffsetConsistency

variable {α β : Type}

/-- A `TableConstraint` preserves the offset consistency invariant if, for any context where
    `circuit.localLength = assignment.offset`, the output context also satisfies this. -/
def TableConstraint.PreservesOffsetConsistency (tc : TableConstraint W S F α) : Prop :=
  ∀ ctx : TableContext W S F,
    ctx.circuit.localLength = ctx.assignment.offset →
    (tc ctx).2.circuit.localLength = (tc ctx).2.assignment.offset

/-- If a table constraint preserves offset consistency, it is offset-consistent
    (since the empty context satisfies the invariant trivially). -/
theorem TableConstraint.OffsetConsistent_of_preserves {tc : TableConstraint W S F α}
    (h : tc.PreservesOffsetConsistency) : tc.OffsetConsistent := by
  exact h .empty rfl

/-- `pure` preserves offset consistency. -/
theorem TableConstraint.pure_preservesOffsetConsistency (a : α) :
    (pure a : TableConstraint W S F α).PreservesOffsetConsistency := by
  intro ctx h; exact h

/-- `getRow` preserves offset consistency. -/
theorem TableConstraint.getRow_preservesOffsetConsistency (row : Fin W) :
    (TableConstraint.getRow (S := S) (F := F) row).PreservesOffsetConsistency := by
  intro ctx h
  show (ctx.circuit ++ [Operation.witness (size S) _]).localLength = (ctx.assignment.pushRow row).offset
  rw [Operations.append_localLength, CellAssignment.pushRow_offset]
  simp only [Operations.localLength]
  omega

/-- Lifting a `Circuit` to `TableConstraint` preserves offset consistency. -/
theorem TableConstraint.monadLift_preservesOffsetConsistency (circuit : Circuit F β) :
    (monadLift circuit : TableConstraint W S F β).PreservesOffsetConsistency := by
  intro ctx h
  simp only [monadLift, MonadLift.monadLift]
  simp only [Operations.append_localLength, CellAssignment.assignmentFromCircuit_offset]
  omega

/-- `assignVar` preserves offset consistency. -/
theorem TableConstraint.assignVar_preservesOffsetConsistency (off : CellOffset W S) (v : Variable F) :
    (assignVar off v : TableConstraint W S F Unit).PreservesOffsetConsistency := by
  intro ctx h
  show ctx.circuit.localLength = (ctx.assignment.setVarInput off v.index).offset
  rw [CellAssignment.setVarInput_offset]
  exact h

/-- `bind` preserves offset consistency if both parts do. -/
theorem TableConstraint.bind_preservesOffsetConsistency
    {f : TableConstraint W S F α} {g : α → TableConstraint W S F β}
    (hf : f.PreservesOffsetConsistency)
    (hg : ∀ a, (g a).PreservesOffsetConsistency) :
    (f >>= g).PreservesOffsetConsistency := by
  intro ctx h
  simp only [bind_def]
  exact hg _ _ (hf ctx h)

/-- `List.forM` preserves offset consistency if the body does for all elements. -/
theorem TableConstraint.forM_list_preservesOffsetConsistency
    {γ : Type} {l : List γ} {body : γ → TableConstraint W S F Unit}
    (hbody : ∀ x ∈ l, (body x).PreservesOffsetConsistency) :
    (l.forM body : TableConstraint W S F Unit).PreservesOffsetConsistency := by
  induction l with
  | nil =>
    exact pure_preservesOffsetConsistency ()
  | cons x xs ih =>
    have hx := hbody x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, (body y).PreservesOffsetConsistency :=
      fun y hy => hbody y (List.mem_cons_of_mem _ hy)
    show (body x >>= fun _ => xs.forM body).PreservesOffsetConsistency
    exact bind_preservesOffsetConsistency hx (fun _ => ih hxs)

end OffsetConsistency

/-! ### Var assignment preservation below a bound

We define `PreservesVarsBelow`, analogous to `PreservesOffsetConsistency`, to reason about
the `forM` loop in `inductiveWitness`. The key property is that operations which only modify
variables at or above a bound `b` preserve the assignment mapping for indices below `b`.
-/

section VarsBelow

variable {α β γ : Type}

/-- A table constraint preserves var assignments at indices below `b`,
    assuming the context starts with `assignment.offset ≥ b` and is offset-consistent.
    It also guarantees that the output offset is still ≥ b and offset-consistent. -/
def TableConstraint.PreservesVarsBelow (tc : TableConstraint W S F α) (b : ℕ) : Prop :=
  ∀ ctx : TableContext W S F,
    b ≤ ctx.assignment.offset →
    ctx.circuit.localLength = ctx.assignment.offset →
    (b ≤ (tc ctx).2.assignment.offset) ∧
    ((tc ctx).2.circuit.localLength = (tc ctx).2.assignment.offset) ∧
    (∀ (i : ℕ) (hi_b : i < b) (hi_out : i < (tc ctx).2.assignment.offset)
      (hi_in : i < ctx.assignment.offset),
      (tc ctx).2.assignment.vars[i] = ctx.assignment.vars[i])

/-- `pure` preserves vars below any bound. -/
theorem TableConstraint.pure_preservesVarsBelow (a : α) (b : ℕ) :
    (pure a : TableConstraint W S F α).PreservesVarsBelow b := by
  intro ctx hb hoc
  exact ⟨hb, hoc, fun _ _ _ _ => rfl⟩

/-- `bind` preserves vars below a bound if both parts do. -/
theorem TableConstraint.bind_preservesVarsBelow
    {f : TableConstraint W S F α} {g : α → TableConstraint W S F β} {b : ℕ}
    (hf : f.PreservesVarsBelow b)
    (hg : ∀ a, (g a).PreservesVarsBelow b) :
    (f >>= g).PreservesVarsBelow b := by
  intro ctx hb hoc
  obtain ⟨hb_f, hoc_f, hvars_f⟩ := hf ctx hb hoc
  obtain ⟨hb_g, hoc_g, hvars_g⟩ := hg (f ctx).1 (f ctx).2 hb_f hoc_f
  refine ⟨?_, ?_, ?_⟩
  · -- b ≤ output offset: (f >>= g) ctx = let (a, ctx') := f ctx; g a ctx'
    change b ≤ (g (f ctx).1 (f ctx).2).2.assignment.offset
    exact hb_g
  · -- offset consistency
    change (g (f ctx).1 (f ctx).2).2.circuit.localLength = (g (f ctx).1 (f ctx).2).2.assignment.offset
    exact hoc_g
  · intro i hi_b hi_out hi_in
    change (g (f ctx).1 (f ctx).2).2.assignment.vars[i] = ctx.assignment.vars[i]
    have hi_f : i < (f ctx).2.assignment.offset := Nat.lt_of_lt_of_le hi_b hb_f
    rw [hvars_g i hi_b hi_out hi_f]
    exact hvars_f i hi_b hi_f hi_in

/-- Lifting a `Circuit` to `TableConstraint` preserves vars below any bound ≤ current offset. -/
theorem TableConstraint.monadLift_preservesVarsBelow (circuit : Circuit F β) (b : ℕ) :
    (monadLift circuit : TableConstraint W S F β).PreservesVarsBelow b := by
  intro ctx hb hoc
  set ops := (circuit ctx.circuit.localLength).2
  -- After monadLift, the result context has:
  -- assignment = assignmentFromCircuit ctx.assignment ops
  -- circuit field = ctx.circuit ++ ops
  -- We prove it satisfies PreservesVarsBelow b
  -- The assignment grows by ops.localLength, preserving existing vars
  have h_afc := CellAssignment.assignmentFromCircuit_offset ctx.assignment ops
  have h_afc_vars := CellAssignment.assignmentFromCircuit_vars ctx.assignment ops
  constructor
  · -- b ≤ output offset
    change b ≤ (assignmentFromCircuit ctx.assignment ops).offset
    omega
  constructor
  · -- offset consistency
    show (ctx.circuit ++ ops).localLength = (assignmentFromCircuit ctx.assignment ops).offset
    rw [Operations.append_localLength, h_afc]; omega
  · intro i hi_b hi_out hi_in
    -- The vars at index i < ctx.assignment.offset are preserved
    show (assignmentFromCircuit ctx.assignment ops).vars[i] = ctx.assignment.vars[i]
    rw [h_afc_vars]
    simp only [Vector.getElem_cast, Vector.getElem_append, hi_in, ↓reduceDIte]

/-- `assignVar` preserves vars below `b` when the target variable index is ≥ `b`. -/
theorem TableConstraint.assignVar_preservesVarsBelow (off : CellOffset W S) (v : Variable F) (b : ℕ)
    (hv : b ≤ v.index) :
    (assignVar off v : TableConstraint W S F Unit).PreservesVarsBelow b := by
  intro ctx hb hoc
  -- assignVar off v ctx = ((), { ctx with assignment := ctx.assignment.setVarInput off v.index })
  -- so (assignVar off v ctx).2.assignment = ctx.assignment.setVarInput off v.index
  -- and (assignVar off v ctx).2.circuit = ctx.circuit
  constructor
  · -- b ≤ output offset
    change b ≤ (ctx.assignment.setVarInput off v.index).offset
    rw [CellAssignment.setVarInput_offset]; exact hb
  constructor
  · -- offset consistency
    change ctx.circuit.localLength = (ctx.assignment.setVarInput off v.index).offset
    rw [CellAssignment.setVarInput_offset]; exact hoc
  · intro i hi_b hi_out hi_in
    change (ctx.assignment.setVarInput off v.index).vars[i] = ctx.assignment.vars[i]
    exact CellAssignment.setVarInput_vars_getElem_ne _ _ _ _ hi_in (by omega)

/-- A `bind` where the first part is a `monadLift` preserves vars below `b`,
    and the continuation preserves vars below `b` for any value (including the produced variable).
    This handles the pattern `let v ← witnessVar ...; ... ; assignVar off v`. -/
theorem TableConstraint.bind_monadLift_preservesVarsBelow
    {circuit : Circuit F γ} {g : γ → TableConstraint W S F β} {b : ℕ}
    (hg : ∀ (a : γ) (ctx : TableContext W S F),
      b ≤ ctx.assignment.offset →
      ctx.circuit.localLength = ctx.assignment.offset →
      (g a).PreservesVarsBelow b) :
    ((monadLift circuit >>= g : TableConstraint W S F β)).PreservesVarsBelow b := by
  apply bind_preservesVarsBelow (monadLift_preservesVarsBelow circuit b) (fun a => ?_)
  intro ctx hb hoc
  exact hg a ctx hb hoc ctx hb hoc

/-- `List.forM` preserves vars below a bound if the body does for all elements. -/
theorem TableConstraint.forM_list_preservesVarsBelow
    {γ : Type} {l : List γ} {body : γ → TableConstraint W S F Unit} {b : ℕ}
    (hbody : ∀ x ∈ l, (body x).PreservesVarsBelow b) :
    (l.forM body : TableConstraint W S F Unit).PreservesVarsBelow b := by
  induction l with
  | nil => exact pure_preservesVarsBelow () b
  | cons x xs ih =>
    have hx := hbody x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, (body y).PreservesVarsBelow b :=
      fun y hy => hbody y (List.mem_cons_of_mem _ hy)
    show (body x >>= fun _ => xs.forM body).PreservesVarsBelow b
    exact bind_preservesVarsBelow hx (fun _ => ih hxs)

/-- The pattern `let v ← witnessVar compute; assertZero expr; assignVar off v` preserves
    vars below `b`, because `witnessVar` creates a variable at the current offset (which is ≥ b),
    so `assignVar` targets an index ≥ b. -/
theorem TableConstraint.witnessAssertAssign_preservesVarsBelow (b : ℕ)
    (compute : Environment F → F) (expr : Variable F → Expression F) (off : CellOffset W S) :
    ((do
      let new_var ← (witnessVar (F := F) compute : Circuit F _)
      (assertZero (F := F) (expr new_var) : Circuit F _)
      assignVar off new_var) : TableConstraint W S F Unit).PreservesVarsBelow b := by
  intro ctx hb hoc
  -- Step 1: monadLift (witnessVar compute)
  set step1 := (monadLift (witnessVar (F := F) compute) : TableConstraint W S F _) ctx
  have h1 := monadLift_preservesVarsBelow (β := Variable F) (witnessVar (F := F) compute) b ctx hb hoc
  -- new_var index = ctx.circuit.localLength ≥ b
  have h_var_idx : step1.1.index = ctx.circuit.localLength := by
    simp [step1, monadLift, MonadLift.monadLift, witnessVar]
  have h_var_ge : b ≤ step1.1.index := by omega
  -- Step 2: monadLift (assertZero (expr step1.1))
  have h2 := monadLift_preservesVarsBelow (β := Unit) (assertZero (F := F) (expr step1.1)) b step1.2 h1.1 h1.2.1
  set step2 := (monadLift (assertZero (F := F) (expr step1.1)) : TableConstraint W S F _) step1.2
  -- Step 3: assignVar off step1.1
  have h3 := assignVar_preservesVarsBelow off step1.1 b h_var_ge step2.2 h2.1 h2.2.1
  -- Combine
  refine ⟨?_, ?_, ?_⟩
  · change b ≤ (assignVar off step1.1 step2.2).2.assignment.offset; exact h3.1
  · change (assignVar off step1.1 step2.2).2.circuit.localLength =
      (assignVar off step1.1 step2.2).2.assignment.offset; exact h3.2.1
  · intro i hi_b hi_out hi_in
    change (assignVar off step1.1 step2.2).2.assignment.vars[i] = ctx.assignment.vars[i]
    rw [h3.2.2 i hi_b hi_out (Nat.lt_of_lt_of_le hi_b h2.1),
        h2.2.2 i hi_b (Nat.lt_of_lt_of_le hi_b h2.1) (Nat.lt_of_lt_of_le hi_b h1.1),
        h1.2.2 i hi_b (Nat.lt_of_lt_of_le hi_b h1.1) hi_in]

end VarsBelow
