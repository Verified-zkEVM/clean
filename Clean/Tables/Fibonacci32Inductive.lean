/- Simple Fibonacci example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Gadgets.Addition32.Addition32

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

instance : ProvableStruct Row where
  components := [U32, U32]
  toComponents := fun { x, y } => .cons x (.cons y .nil)
  fromComponents := fun (.cons x (.cons y .nil)) => { x, y }

def table : InductiveTable (F p) Row unit where
  step row _ := do
    let z ← Addition32.circuit { x := row.x, y := row.y }
    return { x := row.y, y := z }

  Spec i row _ _ : Prop :=
    row.x.value = fib32 i ∧
    row.y.value = fib32 (i + 1) ∧
    row.x.Normalized ∧ row.y.Normalized

  soundness := by simp_all [InductiveTable.Soundness, fib32, circuit_norm,
      Addition32.circuit, Addition32.Assumptions, Addition32.Spec]

  completeness := by simp_all [InductiveTable.Completeness, fib32, circuit_norm,
    Addition32.circuit, Addition32.Assumptions, Addition32.Spec]

-- the input is hard-coded to (0, 1)
def formalTable (output : Row (F p)) := table.toFormal { x := U32.fromByte 0, y := U32.fromByte 1 } output

-- The table's statement implies that the output row contains the nth Fibonacci number
theorem tableStatement (output : Row (F p)) : ∀ n > 0, ∀ trace,
    (formalTable output).statement n trace → output.y.value = fib32 n := by
  intro n hn trace Spec
  simp only [FormalTable.statement, formalTable, InductiveTable.toFormal, table] at Spec
  replace Spec := Spec ⟨hn, (by simp [table, fib32, U32.fromByte_value, U32.fromByte_normalized])⟩
  simp_all +arith

end Tables.Fibonacci32Inductive
