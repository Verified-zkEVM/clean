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

def table : InductiveTable (F p) Addition32.Inputs unit where
  step row _ := do
    let z ← subcircuit Gadgets.Addition32.circuit row
    return { x := row.y, y := z }

  spec i row _ _ : Prop :=
    row.x.value = fib32 i ∧
    row.y.value = fib32 (i + 1) ∧
    row.x.is_normalized ∧ row.y.is_normalized

  soundness := by simp_all [fib32, circuit_norm, subcircuit_norm,
    Addition32.circuit, Addition32.assumptions, Addition32.spec]

  completeness := by simp_all [fib32, circuit_norm, subcircuit_norm,
    Addition32.circuit, Addition32.assumptions, Addition32.spec]

-- the input is hard-coded to (0, 1)
def formalTable (output : Addition32.Inputs (F p)) := table.toFormal { x := U32.from_byte 0, y := U32.from_byte 1 } output

-- The table's statement implies that the output row contains the nth Fibonacci number
theorem tableStatement (output : Addition32.Inputs (F p)) : ∀ n > 0, ∀ trace,
    (formalTable output).statement n trace → output.y.value = fib32 n := by
  intro n hn trace spec
  simp only [FormalTable.statement, formalTable, InductiveTable.toFormal, table] at spec
  replace spec := spec ⟨hn, (by simp [table, fib32, U32.from_byte_value, U32.from_byte_is_normalized])⟩
  simp_all +arith

end Tables.Fibonacci32Inductive
