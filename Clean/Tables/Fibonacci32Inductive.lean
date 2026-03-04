/- Simple Fibonacci example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Gadgets.Addition32.Addition32

set_option maxHeartbeats 400000

namespace Tables.Fibonacci32Inductive
open Gadgets
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

def fib32 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (fib32 n + fib32 (n + 1)) % 2^32

structure Row (F : Type) where
  x: U32 F
  y: U32 F
deriving ProvableStruct

def table : InductiveTable (F p) Row unit where
  step row _ := do
    let z ← Addition32.circuit { x := row.x, y := row.y }
    let fresh_y <== row.y
    return { x := fresh_y, y := z }

  Spec _ _ i _ row _ : Prop :=
    row.x.value = fib32 i ∧
    row.y.value = fib32 (i + 1) ∧
    row.x.Normalized ∧ row.y.Normalized

  soundness := by
    simp_all [InductiveTable.Soundness, fib32, circuit_norm,
      Addition32.circuit, Addition32.Assumptions, Addition32.Spec, HasAssignEq.assignEq]

  completeness := by
    intro _ _ env acc_var _ acc _ _ _ h_eval h_witnesses ⟨_, h_spec, _⟩
    simp only [circuit_norm, Addition32.circuit, Addition32.Assumptions, Addition32.Spec,
      HasAssignEq.assignEq] at h_witnesses ⊢
    obtain ⟨h_add_witnesses, h_fresh_witnesses⟩ := h_witnesses
    have h_norm : (eval env acc_var.x).Normalized ∧ (eval env acc_var.y).Normalized := by
      have h1 : eval env acc_var.x = acc.x := by
        have := congr_arg Row.x h_eval.1; simp [circuit_norm] at this; exact this
      have h2 : eval env acc_var.y = acc.y := by
        have := congr_arg Row.y h_eval.1; simp [circuit_norm] at this; exact this
      exact ⟨h1 ▸ h_spec.2.2.1, h2 ▸ h_spec.2.2.2⟩
    exact ⟨h_norm, by
      rw [ProvableType.ext_iff]; intro i hi
      rw [ProvableType.eval_varFromOffset, ProvableType.toElements_fromElements, Vector.getElem_mapRange]
      exact h_fresh_witnesses ⟨i, hi⟩⟩

  outputFreshVars := by
    have hsum : ([4, 4] : List ℕ).sum = 8 := rfl
    simp only [circuit_norm, Addition32.circuit, explicit_provable_type, hsum]
    refine InductiveTable.outputFreshVars_of_indices _ _ _ (fun i => match i.val with
      | 0 => 16 | 1 => 17 | 2 => 18 | 3 => 19 | 4 => 8 | 5 => 10 | 6 => 12 | _ => 14)
      ?_ ?_ ?_ ?_
    · intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro ⟨i, hi⟩
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> grind
    · intro ⟨i, hi⟩
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> grind
    · intro ⟨a, ha⟩ ⟨b, hb⟩ h
      have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
      have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
      rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> first | rfl | grind

-- the input is hard-coded to (0, 1)
def formalTable (output : Row (F p)) := table.toFormal { x := U32.fromByte 0, y := U32.fromByte 1 } output

-- The table's statement implies that the output row contains the nth Fibonacci number
theorem tableStatement (output : Row (F p)) : ∀ n > 0, ∀ trace env,
    (formalTable output).statement n trace env → output.y.value = fib32 n := by
  intro n hn trace env Spec
  simp only [FormalTable.statement, formalTable, InductiveTable.toFormal, table] at Spec
  replace Spec := Spec ⟨hn, (by simp [fib32, U32.fromByte_value, U32.fromByte_normalized])⟩
  simp_all +arith

end Tables.Fibonacci32Inductive
