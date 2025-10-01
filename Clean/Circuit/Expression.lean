import Mathlib.Algebra.Field.Basic
import Clean.Circuit.SimpGadget

variable {F : Type}

structure Variable (F : Type) where
  index : ℕ

instance : Repr (Variable F) where
  reprPrec v _ := "var ⟨" ++ repr v.index ++ "⟩"

inductive Expression (F : Type) where
  | var : Variable F -> Expression F
  | const : F -> Expression F
  | add : Expression F -> Expression F -> Expression F
  | mul : Expression F -> Expression F -> Expression F

export Expression (var)

structure NamedList (F : Type) where
  name : String
  value : List F
deriving DecidableEq

instance [Repr F] : Repr (NamedList F) where
  reprPrec nl _ := "⟨" ++ repr nl.name ++ ", " ++ repr nl.value ++ "⟩"

structure Tape (F : Type) where
  get : ℕ → F

structure Environment (F : Type) where
  tape : Tape F
  yielded : Set (NamedList F)

namespace Expression
variable [Field F]

/--
Evaluate expression given an external `tape` that determines the assignment
of all variables.

This is needed when we want to make statements about a circuit in the adversarial
situation where the prover can assign anything to variables.
-/
@[circuit_norm]
def eval (tape : Tape F) : Expression F → F
  | var v => tape.get v.index
  | const c => c
  | add x y => eval tape x + eval tape y
  | mul x y => eval tape x * eval tape y

end Expression

namespace NamedList
variable [Field F]

def eval (nl : NamedList (Expression F)) (tape : Tape F) : NamedList F :=
  { name := nl.name, value := nl.value.map (Expression.eval tape) }

end NamedList

namespace Expression
variable [Field F]

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

instance {n : ℕ} [OfNat F n] : OfNat (Expression F) n where
  ofNat := const (OfNat.ofNat n)

instance : HMul F (Expression F) (Expression F) where
  hMul f e := mul f e

instance : HDiv (Expression F) F (Expression F) where
  hDiv e f := mul (f⁻¹ : F) e

instance : HDiv (Expression F) ℕ (Expression F) where
  hDiv e f := mul (f⁻¹ : F) e

-- TODO probably should just make Variable F := ℕ
instance {n : ℕ} : OfNat (Variable F) n where
  ofNat := { index := n }
end Expression

instance [Field F] : CoeFun (Tape F) (fun _ => (Expression F) → F) where
  coe tape x := x.eval tape

instance [Field F] : CoeFun (Environment F) (fun _ => (Expression F) → F) where
  coe env x := x.eval env.tape

instance [Field F] : Inhabited F where
  default := 0

instance [Field F] : Inhabited (Expression F) where
  default := .const 0

/-! ## Lemmas about Expression evaluation -/

section EvalLemmas
variable [Field F]

/-- Expression.eval distributes over multiplication -/
@[circuit_norm]
lemma eval_mul (env : Environment F) (a b : Expression F) :
    Expression.eval env.tape (Expression.mul a b) = (Expression.eval env.tape a) * (Expression.eval env.tape b) := by
  simp only [Expression.eval]

/-- Expression.eval distributes over Fin.foldl with addition -/
lemma eval_foldl (env : Environment F) (n : ℕ)
    (f : Expression F → Fin n → Expression F) (init : Expression F)
    (hf : ∀ (e : Expression F) (i : Fin n),
      Expression.eval env.tape (f e i) = Expression.eval env.tape (f (Expression.const (Expression.eval env.tape e)) i)) :
    Expression.eval env.tape (Fin.foldl n f init) =
    Fin.foldl n (fun (acc : F) (i : Fin n) => Expression.eval env.tape (f (Expression.const acc) i)) (Expression.eval env.tape init) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n' ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    -- Apply the inductive hypothesis with the appropriate function and assumption
    have hf' : ∀ (e : Expression F) (i : Fin n'),
      Expression.eval env.tape (f e i.castSucc) = Expression.eval env.tape (f (Expression.const (Expression.eval env.tape e)) i.castSucc) := by
      intros e i
      exact hf e i.castSucc

    have h1 : Expression.eval env.tape (Fin.foldl n' (fun x1 x2 => f x1 x2.castSucc) init) =
              Fin.foldl n' (fun acc i => Expression.eval env.tape (f (Expression.const acc) i.castSucc)) (Expression.eval env.tape init) :=
      ih (fun x i => f x i.castSucc) hf'

    -- Now apply the assumption to relate the two sides
    rw [hf (Fin.foldl n' (fun x1 x2 => f x1 x2.castSucc) init) (Fin.last n')]
    -- Rewrite using h1
    rw [h1]

end EvalLemmas
