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
