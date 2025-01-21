import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Table.Basic
import Clean.Gadgets.Addition32Full
import Clean.Gadgets.Equality.U32
import Clean.Types.U32


/-
  8-bit Fibonacci inductive table definition. The i-th row of the table
  contains the values of the Fibonacci sequence at i and i+1, modulo 256.

  0        | 1
  ...
  fib(i)   | fib(i+1)
  fib(i+1) | fib(i+2)
  ...

-/
namespace Tables.Fibonacci32
variable {p : ℕ}
variable [p_large_enough: Fact (p > 2*2^32)]

lemma p_large_enough' : Fact (p > 512) := by
  apply Fact.mk; linarith [p_large_enough.elim]

variable [Fact (p ≠ 0)] [Fact p.Prime]

/--
  inductive contraints that are applied every two rows of the trace.
-/
def recursive_relation : TwoRowsConstraint (F p) 8 := do
  let x0 <- TableConstraint.get_cell (CellOffset.curr 0)
  let x1 <- TableConstraint.get_cell (CellOffset.curr 1)
  let x2 <- TableConstraint.get_cell (CellOffset.curr 2)
  let x3 <- TableConstraint.get_cell (CellOffset.curr 3)

  let y0 <- TableConstraint.get_cell (CellOffset.curr 4)
  let y1 <- TableConstraint.get_cell (CellOffset.curr 5)
  let y2 <- TableConstraint.get_cell (CellOffset.curr 6)
  let y3 <- TableConstraint.get_cell (CellOffset.curr 7)

  let x : U32 (Expression (F p)) := ⟨x0, x1, x2, x3⟩
  let y : U32 (Expression (F p)) := ⟨y0, y1, y2, y3⟩


  let z <- TableConstraint.subcircuit Gadgets.Addition32Full.circuit {x, y, carry_in:=0}

  if let ⟨⟨var z0, var z1, var z2, var z3⟩, _⟩ := z then
    TableConstraint.assign z0 (CellOffset.next 4)
    TableConstraint.assign z1 (CellOffset.next 5)
    TableConstraint.assign z2 (CellOffset.next 6)
    TableConstraint.assign z3 (CellOffset.next 7)

  let x0_next <- TableConstraint.get_cell (CellOffset.next 0)
  let x1_next <- TableConstraint.get_cell (CellOffset.next 1)
  let x2_next <- TableConstraint.get_cell (CellOffset.next 2)
  let x3_next <- TableConstraint.get_cell (CellOffset.next 3)

  let x_next : U32 (Expression (F p)) := ⟨x0_next, x1_next, x2_next, x3_next⟩
  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨y, x_next⟩

/--
  boundary constraints that are applied at the beginning of the trace.
  This is our "base case" for the Fibonacci sequence.
-/
def boundary : SingleRowConstraint (F p) 8 := do
  let x0 <- TableConstraint.get_cell (CellOffset.curr 0)
  let x1 <- TableConstraint.get_cell (CellOffset.curr 1)
  let x2 <- TableConstraint.get_cell (CellOffset.curr 2)
  let x3 <- TableConstraint.get_cell (CellOffset.curr 3)
  let y0 <- TableConstraint.get_cell (CellOffset.curr 4)
  let y1 <- TableConstraint.get_cell (CellOffset.curr 5)
  let y2 <- TableConstraint.get_cell (CellOffset.curr 6)
  let y3 <- TableConstraint.get_cell (CellOffset.curr 7)

  let x : U32 (Expression (F p)) := ⟨x0, x1, x2, x3⟩
  let y : U32 (Expression (F p)) := ⟨y0, y1, y2, y3⟩

  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨x, U32.decompose_nat_expr 0⟩
  TableConstraint.assertion Gadgets.Equality.U32.circuit ⟨y, U32.decompose_nat_expr 1⟩

def fib32_table : List (TableOperation (F p) 8) := [
  TableOperation.Boundary 0 boundary,
  TableOperation.EveryRowExceptLast recursive_relation,
]

def assumptions {N : ℕ} (trace : TraceOfLength (F p) 8 N) : Prop :=
  N > 2 ∧
  trace.forAllRowsOfTrace (fun row => (row 1).val < 256)

def fib32 : ℕ -> ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (fib32 n + fib32 (n + 1)) % 2^32

def spec {N : ℕ} (trace : TraceOfLength (F p) 8 N) : Prop :=
  trace.forAllRowsOfTraceWithIndex (λ row index =>
    let x := (U32.mk (row 0) (row 1) (row 2) (row 3)).value
    let y := (U32.mk (row 4) (row 5) (row 6) (row 7)).value
    (x = fib32 index) ∧ (y = fib32 (index + 1))
    )


lemma fib32_less_than_2_32 (n : ℕ) : fib32 n < 2^32 := by
  induction' n using Nat.twoStepInduction
  repeat {simp [fib32]}; apply Nat.mod_lt; simp


def formal_fib32_table : FormalTable (F:=(F p)) := {
  M := 8,
  constraints := fib32_table,
  assumptions := assumptions,
  spec := spec,
  soundness := by
    sorry
}

end Tables.Fibonacci32
