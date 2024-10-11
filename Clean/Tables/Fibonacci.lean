import Clean.Utils.Field
import Clean.Expression
import Clean.GenericConstraint
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasLehmer
import Clean.Gadgets.Addition8
import Clean.Gadgets.Equality
import Clean.Table

section FibonacciTable
open Expression
variable (T : ℕ+) (p : ℕ) [Fact p.Prime] [Fact (p > 512)]

/-
Table layout:

0        | 1        | carry
1        | 1        | carry
...
fib(i)   | fib(i+1) | carry
fib(i+1) | fib(i+2) | carry
-/


def constraints : List (TableConstraint 3 T p) := [
  TableConstraint.boundary 0 (λ row => Equality.circuit 3 T (var row 0) (const 0)),
  TableConstraint.boundary 0 (λ row => Equality.circuit 3 T (var row 1) (const 1)),
  TableConstraint.everyRowExceptLast (λ row => Addition8.circuit 3 T (var row 0) (var row 1) (var row 2) (var (row+1) 1)),
  TableConstraint.everyRowExceptLast (λ row => Equality.circuit 3 T (var row 1) (var (row+1) 0))
]

def fib8 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n+2) => (fib8 n + fib8 (n+1)) % 256

def spec : Inputs 3 T (F p) -> Prop :=
  fun trace => (∀ row : ZMod T, (trace row 0).val = (fib8 row.val) % 256)


def fibonacciTable : Table 3 T p := {
  constraints := constraints T p,
  spec := spec T p,
  equiv := (by
    intros trace
    simp [ByteLookup.lookup, eval, spec]

    intro lookups
    constructor
    · sorry
    · sorry
  )
}




end FibonacciTable
