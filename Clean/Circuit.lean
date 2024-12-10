import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace Circuit
variable {F: Type} [CommRing F]

structure Variable (F : Type) where
  index: ℕ
  witness: Unit → F

instance : Repr (Variable F) where
  reprPrec v _ := "x" ++ repr v.index

inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F

namespace Expression
def eval : Expression F → F
  | var v => v.witness ()
  | const c => c
  | add x y => eval x + eval y
  | mul x y => eval x * eval y

def toString [Repr F] : Expression F → String
  | var v => reprStr v
  | const c => reprStr c
  | add x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | mul x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"

instance [Repr F] : Repr (Expression F) where
  reprPrec e _ := toString e
end Expression

namespace Expression

-- combine expressions elegantly
instance : Zero (Expression F) where
  zero := const 0

instance : One (Expression F) where
  one := const 1

instance : Add (Expression F) where
  add := add

instance : Neg (Expression F) where
  neg e := mul (const (-1)) e

instance : Sub (Expression F) where
  sub e₁ e₂ := add e₁ (-e₂)

instance : Mul (Expression F) where
  mul := mul

instance : Coe F (Expression F) where
  coe f := const f

instance : Coe (Variable F) (Expression F) where
  coe x := var x

instance : Coe (Expression F) F where
  coe x := x.eval

instance : HMul F (Expression F) (Expression F) where
  hMul := fun f e => mul f e
end Expression

structure Vector (F : Type) (n: ℕ) where
  entries: Fin n → F
deriving Repr

structure Table (F : Type) where
  arity: ℕ
  length: ℕ
  row: Fin length → Vector F arity

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity
  witness: Unit → Fin table.length -- index of the entry

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ repr l.entry ++ ")"

inductive Row
  | Current
  | Next
deriving Repr

structure Cell (F : Type) where
  column: ℕ -- index of the column
  row: Row
deriving Repr

structure Context (F : Type) where
  offset: ℕ
  locals: Array (Variable F)
  constraints: Array (Expression F)
  lookups: Array (Lookup F)
  assignments: Array (Cell F × Variable F)
deriving Repr

namespace Context
def empty (offset: ℕ) : Context F := ⟨ offset, #[] , #[] , #[] , #[] ⟩
end Context

variable {α : Type}

inductive Operation (F : Type) where
  | Witness : (compute : Unit → F) → Operation F
  | Assert : Expression F → Operation F
  | Lookup : Lookup F → Operation F
  | Assign : Cell F × Variable F → Operation F
  | Circuit : (circuit: Context F → (Context F × List (Operation F)) × Unit) → Operation F

namespace Operation

def run (ctx: Context F) : Operation F → Context F
  | Witness compute =>
    let var := ⟨ ctx.offset, compute ⟩
    let offset := ctx.offset + 1
    { ctx with offset, locals := ctx.locals.push var }

  | Assert e => { ctx with constraints := ctx.constraints.push e }

  | Lookup l => { ctx with lookups := ctx.lookups.push l }

  | Assign (c, v) => { ctx with assignments := ctx.assignments.push (c, v) }

  | Circuit c =>
    let subctx := Context.empty ctx.offset
    let ((subctx, _), _) := c subctx
    { ctx with offset := subctx.offset }

instance [Repr F] : ToString (Operation F) where
  toString op := match op with
    | Witness _v => "Witness"
    | Assert e => "Assert(" ++ reprStr e ++ ")"
    | Lookup l => "Lookup(" ++ reprStr l ++ ")"
    | Assign (c, v) => "Assign(" ++ reprStr c ++ ", " ++ reprStr v ++ ")"
    | Circuit _ => "Circuit"
end Operation

def Stateful (F : Type) (α : Type) := Context F → (Context F × List (Operation F)) × α

def Stateful.run (circuit: Stateful F α) (offset: ℕ := 0) : Context F × List (Operation F) :=
  let ctx := Context.empty offset
  let ((ctx, ops), _ ) := circuit ctx
  (ctx, ops)

instance : Monad (Stateful F) where
  pure a ctx := ((ctx, []), a)
  bind f g ctx :=
    let ((ctx', ops), a) := f ctx
    let ((ctx'', ops'), a) := g a ctx'
    ((ctx'', ops ++ ops'), a)

def as_stateful (f: Context F → Operation F × α) : Stateful F α := fun ctx  =>
  let (op, a) := f ctx
  let ctx' := Operation.run ctx op
  (⟨ ctx', [op] ⟩, a)

-- operations we can do in a circuit

-- create a new variable
def witness (compute : Unit → F) := as_stateful (fun ctx =>
  let var := ⟨ ctx.offset, compute ⟩
  (Operation.Witness compute, Expression.var var)
)

-- add a constraint
def assert (e: Expression F) := as_stateful (
  fun _ => (Operation.Assert e, ())
)

-- add a lookup
def lookup (l: Lookup F) := as_stateful (
  fun _ => (Operation.Lookup l, ())
)

-- assign a variable to a cell
def assign_cell (c: Cell F) (v: Variable F) := as_stateful (
  fun _ => (Operation.Assign (c, v), ())
)

-- run a sub-circuit
def subcircuit (c: Stateful F Unit) := as_stateful (
  fun _ => (Operation.Circuit c, ())
)

end Circuit

section -- examples
open Circuit

variable (offset: ℕ) {p: ℕ} [p_prime: Fact p.Prime]

def F p := ZMod p

variable [p_large_enough: Fact (p > 512)]

def create (x: ℕ) (lt: x < p) : F p :=
  match p, p_prime with
  | 0, _ => False.elim (Nat.not_lt_zero x lt)
  | (_n + 1), _ => ⟨ x, lt ⟩

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  create (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def mod256 (x: F p) : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

instance : CommRing (F p) := ZMod.commRing p

def E := Expression (F p)
open Expression (const)

def Boolean (x: Expression (F p)) : Stateful (F p) Unit :=
  do assert (x * (x - 1))

def Add8 (x y: Expression (F p)) : Stateful (F p) (Expression (F p)) :=
  do
    let z ← witness (fun () => mod256 (x + y))
    -- lookup (_) -- TODO

    let carry ← witness (fun () => x + y - z)
    subcircuit (Boolean carry) ;

    assert (x + y - z - carry * (const 256)) ;
    return z

#eval!
  let p := 1009
  let p_prime := Fact.mk (by sorry : Nat.Prime p)
  let p_large_enough := Fact.mk (by norm_num : p > 512)
  let x: Variable (F p) := ⟨ 0, fun () => 20 ⟩
  let y: Variable (F p) := ⟨ 1, fun () => 30 ⟩
  let (ctx, ops) := (Add8 (p:=p) x y).run 2
  ops
end
