import Mathlib.Algebra.Field.Basic

variable {F: Type} {s : ℕ}

/--
A `Variable F n` is a variable in an environment of size `s` with elements of type `F`.
It is represented by an index into the environment.
-/
structure Variable (F : Type) (s : ℕ) where
  index: Fin s

instance : Repr (Variable F s) where
  reprPrec v _ := "x" ++ repr v.index

inductive Expression (F : Type) (s : ℕ) where
  | var : Variable F s -> Expression F s
  | const : F -> Expression F s
  | add : Expression F s -> Expression F s -> Expression F s
  | mul : Expression F s -> Expression F s -> Expression F s

export Expression (var const)

/--
  Lift a single variable from a smaller environment to a larger environment.
-/
@[simp]
def Variable.lift {s s' : ℕ} (h : s ≤ s') : Variable F s → Variable F s'
  | ⟨v⟩ => ⟨⟨v, by exact Nat.lt_of_lt_of_le v.is_lt h⟩⟩

/--
  Lift a single variable from a smaller environment to a larger environment at a given offset
  This takes a variable defined over `Fin s` and returns a variable defined over `Fin (s + off)` where
  the index is increased by `off`.
-/
@[simp]
def Variable.lift_offset {s : ℕ} (off : ℕ) : Variable F s → Variable F (s + off)
  | ⟨v⟩ => ⟨⟨v + off, by simp⟩⟩

namespace Expression
variable [Field F]

/--
Evaluate expression given an external `environment` that determines the assignment
of all variables.
-/
@[simp]
def eval_env (env: Fin s → F) : Expression F s → F
  | var v => env v.index
  | const c => c
  | add x y => eval_env env x + eval_env env y
  | mul x y => eval_env env x * eval_env env y

def toString [Repr F] : Expression F s → String
  | var v => "x" ++ reprStr v.index
  | const c => reprStr c
  | add x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | mul x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"

/--
  Lift an expression from a smaller environment to a larger environment.
-/
def lift_vars {s s' : ℕ} (h : s ≤ s') : Expression F s → Expression F s'
  | var v => var (v.lift h)
  | const c => const c
  | add x y => add (lift_vars h x) (lift_vars h y)
  | mul x y => mul (lift_vars h x) (lift_vars h y)

/--
  Lift an expression from a smaller environment to a larger environment at a given offset.
-/
def lift_vars_offset (off : ℕ) : Expression F s → Expression F (s + off)
  | var v => var (v.lift_offset off)
  | const c => const c
  | add x y => add (lift_vars_offset off x) (lift_vars_offset off y)
  | mul x y => mul (lift_vars_offset off x) (lift_vars_offset off y)

instance [Repr F] : Repr (Expression F s) where
  reprPrec e _ := toString e

-- combine expressions elegantly
instance : Zero (Expression F s) where
  zero := const 0

instance : One (Expression F s) where
  one := const 1

instance : Add (Expression F s) where
  add := add

instance : Neg (Expression F s) where
  neg e := mul (const (-1)) e

instance : Sub (Expression F s) where
  sub e₁ e₂ := add e₁ (-e₂)

instance : Mul (Expression F s) where
  mul := mul

instance : Coe F (Expression F s) where
  coe f := const f

instance : Coe (Variable F s) (Expression F s) where
  coe x := var x

instance : HMul F (Expression F s) (Expression F s) where
  hMul := fun f e => mul f e
end Expression
