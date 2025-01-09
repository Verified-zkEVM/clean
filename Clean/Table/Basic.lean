import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Basic
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Utils.Field


def Row (M : ℕ+) (F : Type) := Fin M -> F

/--
  A trace is an inductive list of rows. It can be viewed as a structured
  environment that maps cells to field elements.
-/
inductive Trace (M : ℕ+) (F : Type) :=
  /-- An empty trace -/
  | empty : Trace M F
  /-- Add a row to the end of the trace -/
  | cons (rest: Trace M F) (row: Row M F) : Trace M F

@[inherit_doc] notation:67 "<+>" => Trace.empty
@[inherit_doc] infixl:67 " +> " => Trace.cons

namespace Trace
/--
  The length of a trace is the number of rows it contains.
-/
def len {M : ℕ+} {F : Type} : Trace M F -> ℕ
  | <+> => 0
  | rest +> _ => Nat.succ rest.len

/--
  Induction principle that applies for every row in the trace, where the inductive step takes into
  acount the previous two rows.
-/
def everyRowTwoRowsInduction {M : ℕ+} {F : Type} {P : Trace M F → Sort*}
    (zero : P (<+>))
    (one : ∀ row : Row M F, P (empty +> row))
    (more : ∀ curr next : Row M F,
      ∀ rest : Trace M F, P (rest) -> P (rest +> curr) → P (rest +> curr +> next))
    : ∀ trace, P trace
  | <+> => zero
  | <+> +> first => one first
  | rest +> curr +> _ => more _ _ _
    (everyRowTwoRowsInduction zero one more (rest))
    (everyRowTwoRowsInduction zero one more (rest +> curr))

def getLe {M :ℕ+} {F : Type}:
    (trace : Trace M F) -> (row : Fin trace.len) -> (col : Fin M) -> F
  | _ +> currRow, ⟨0, _⟩, j => currRow j
  | rest +> _, ⟨i + 1, h⟩, j => getLe rest ⟨i, Nat.le_of_succ_le_succ h⟩ j

end Trace

/--
  A trace of length M is a trace with exactly M rows.
-/
def TraceOfLength (M : ℕ+) (N : ℕ) (F : Type) : Type := { env : Trace M F // env.len = N }

namespace TraceOfLength

def get {N: ℕ+} {M : ℕ} {F : Type} : (env : TraceOfLength N M F) -> (i : Fin M) -> (j : Fin N) -> F
  | ⟨env, h⟩, i, j => env.getLe (by rw [←h] at i; exact i) j

end TraceOfLength


section Table
variable (N : ℕ+) (M : ℕ) (p : ℕ) [Fact p.Prime]

/--
  Apply a proposition to every row in the trace
-/
def forAllRowsOfTrace (trace : TraceOfLength N M (F p)) (prop : Row N (F p) -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N (F p) -> (Row N (F p) -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => prop row ∧ inner rest prop

def forAllRowsOfTraceExceptLast (trace : TraceOfLength N M (F p)) (prop : Row N (F p) -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N (F p) -> (Row N (F p) -> Prop) -> Prop
    | <+>, _ => true
    | <+> +> _, _ => true
    | rest +> curr +> _, prop => prop curr ∧ inner (rest +> curr) prop


/--
  Apply a proposition, which could be dependent on the row index, to every row of the trace
-/
def forAllRowsOfTraceWithIndex (trace : TraceOfLength N M (F p)) (prop : Row N (F p) -> ℕ -> Prop) : Prop :=
  inner trace.val prop
  where
  inner : Trace N (F p) -> (Row N (F p) -> ℕ -> Prop) -> Prop
    | <+>, _ => true
    | rest +> row, prop => (prop row rest.len) ∧ inner rest prop
