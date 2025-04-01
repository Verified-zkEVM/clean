import Mathlib.Algebra.Field.Basic
import Clean.Circuit.SimpGadget

variable {F: Type}

structure Variable (F : Type) where
  index: ℕ

instance : Repr (Variable F) where
  reprPrec v _ := "var ⟨" ++ repr v.index ++ "⟩"

inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F

export Expression (var const)

structure Environment (F: Type) where
  get: ℕ → F

namespace Expression
variable [Field F]

/--
Evaluate expression given an external `environment` that determines the assignment
of all variables.

This is needed when we want to make statements about a circuit in the adversarial
situation where the prover can assign anything to variables.
-/
@[circuit_norm]
def eval (env: Environment F) : Expression F → F
  | var v => env.get v.index
  | const c => c
  | add x y => eval env x + eval env y
  | mul x y => eval env x * eval env y

def toString [Repr F] : Expression F → String
  | var v => reprStr v
  | const c => reprStr c
  | add x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | mul x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"

instance [Repr F] : Repr (Expression F) where
  reprPrec e _ := toString e

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

instance : HMul F (Expression F) (Expression F) where
  hMul := fun f e => mul f e

-- TODO probably should just make Variable F := ℕ
instance {n: ℕ} : OfNat (Variable F) n where
  ofNat := { index := n }
end Expression

instance [Field F] : CoeFun (Environment F) (fun _ => (Expression F) → F) where
  coe env x := x.eval env
