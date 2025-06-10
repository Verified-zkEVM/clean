/- Simple Fibonacci example using `InductiveTable` -/
import Clean.Table.Inductive
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Gadgets.Equality

namespace Tables.Fibonacci32Inductive
open Gadgets
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

def fib32 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (fib32 n + fib32 (n + 1)) % 2^32

structure Row (F : Type) where
  x: U32 F
  y: U32 F

instance : ProvableStruct Row where
  components := [U32, U32]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }

def table : InductiveTable (F p) Row where
  step row := do
    let { z, .. } ← subcircuit Gadgets.Addition32Full.circuit {
      x := row.x, y := row.y, carry_in := 0
    }
    return { x := row.y, y := z }

  spec i row : Prop :=
    row.x.value = fib32 i ∧
    row.y.value = fib32 (i + 1) ∧
    row.x.is_normalized ∧ row.y.is_normalized

  soundness := by simp_all [fib32, circuit_norm, subcircuit_norm,
    Addition32Full.circuit, Addition32Full.assumptions, Addition32Full.spec]

  completeness := by simp_all [fib32, circuit_norm, subcircuit_norm,
    Addition32Full.circuit, Addition32Full.assumptions, Addition32Full.spec]

-- the input is hard-coded to (0, 1)
def formalTable (output : Row (F p)) := table.toFormal { x:= U32.from_byte 0, y:= U32.from_byte 1 } output

-- The table's statement implies that the output row contains the nth Fibonacci number
theorem tableStatement (output : Row (F p)) : ∀ n > 0, ∀ trace,
    (formalTable output).statement n trace → output.y.value = fib32 n := by
  intro n hn trace spec
  simp only [FormalTable.statement, formalTable, InductiveTable.toFormal, table] at spec
  replace spec := spec ⟨hn, (by simp [table, fib32, U32.from_byte_value, U32.from_byte_is_normalized])⟩
  simp_all +arith

end Tables.Fibonacci32Inductive
