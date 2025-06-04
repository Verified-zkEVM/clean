import Clean.Table.Inductive
import Clean.Gadgets.Addition32.Addition32Full
import Clean.Gadgets.Equality

namespace Tables.Fibonacci32
open Gadgets
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

def fib32 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib32 n + fib32 (n + 1)) % 2^32

structure Row (F : Type) where
  x: U32 F
  y: U32 F
instance : ProvableStruct Row where
  components := [U32, U32]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }

def table : InductiveTable (F p) Row where
  main _ (curr : Var Row (F p)) : Circuit (F p) (Var Row (F p)) := do
    let { z, .. } ← subcircuit Gadgets.Addition32Full.circuit {
      x := curr.x, y := curr.y, carry_in := 0
    }
    return { x := curr.y, y := z }

  spec (i : ℕ) (row : Row (F p)) : Prop :=
    row.x.value = fib32 i ∧
    row.y.value = fib32 (i + 1) ∧
    row.x.is_normalized ∧ row.y.is_normalized

  soundness := by simp_all [fib32, circuit_norm, subcircuit_norm,
    Addition32Full.circuit, Addition32Full.assumptions, Addition32Full.spec]

  completeness := by simp_all [fib32, circuit_norm, subcircuit_norm,
    Addition32Full.circuit, Addition32Full.assumptions, Addition32Full.spec]
