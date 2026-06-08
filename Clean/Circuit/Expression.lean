import Mathlib.Algebra.Field.Basic
import Clean.Circuit.SimpGadget

variable {F L : Type}

structure VariableWithLocation (F : Type) (L : Type) where
  index : L

def Variable (F : Type) := VariableWithLocation F ℕ

instance [Repr L] : Repr (VariableWithLocation F L) where
  reprPrec v _ := "var ⟨" ++ repr v.index ++ "⟩"

instance : Repr (Variable F) where
  reprPrec v _ := "var ⟨" ++ repr v.index ++ "⟩"

inductive ExpressionWithLocation (F : Type) (L : Type) where
  | var : VariableWithLocation F L -> ExpressionWithLocation F L
  | const : F -> ExpressionWithLocation F L
  | add : ExpressionWithLocation F L -> ExpressionWithLocation F L -> ExpressionWithLocation F L
  | mul : ExpressionWithLocation F L -> ExpressionWithLocation F L -> ExpressionWithLocation F L

def Expression (F : Type) := ExpressionWithLocation F ℕ

/-- Arbitrary data a prover can witness and refer to in a circuit spec -/
def ProverData (F : Type) :=
  String → (n : ℕ) → Array (Vector F n)

/-- Runtime-only hashmap of prover hints. Same shape as `ProverData`, but
distinct to emphasize that hints are *not* committed: they feed only the
witness-generation step and never appear in the proof. -/
def ProverHint (F : Type) :=
  String → (n : ℕ) → Array (Vector F n)

/-- Placeholder `ProverHint` that returns an empty array for every key. -/
def ProverHint.empty (F : Type) : ProverHint F := fun _ _ => #[]

/--
  `Environment` represents the data that is provided at runtime to concretely
  specify the witness assignment of a circuit (`get`) and any additional witness data
  external to the current circuit (`data`).

  In the abstract plaintext-witness version of the protocol, the full
  `Environment` is passed from the prover to the verifier.
  All constraints can be checked against the `Environment`.
  Soundness theorems have the form `∀ env : Environment F, ...`.
 -/
structure EnvironmentWithLocation (F : Type) (L : Type) where
  /-- Assignment of a circuit's variables to field elements -/
  get : L → F
  /-- Additional witness data not part of the current circuit's witness, such as the content
   of lookup tables, made available for potential re-witnessing and for statements concerning
   the verifier, such as a circuit's spec. -/
  data : ProverData F

def Environment (F : Type) := EnvironmentWithLocation F ℕ

/--
  `ProverEnvironment` is `Environment` plus the prover's runtime `ProverHint`.
  In some circuits, the additional `hint` is necessary to give an honest prover
  sufficient information to generate a witness.
  Completeness theorems are formulated against the `ProverEnvironment`.
-/
structure ProverEnvironment (F : Type) extends Environment F where
  /-- Runtime-only hashmap of prover hints, never committed into the proof. -/
  hint : ProverHint F

/-- Project a `ProverEnvironment` to its `Environment`. -/
@[circuit_norm]
abbrev ProverEnvironment.toEnvironment (env : ProverEnvironment F) : Environment F :=
  env.toEnvironmentWithLocation

instance : Coe (ProverEnvironment F) (Environment F) := ⟨ProverEnvironment.toEnvironment⟩
instance : CoeOut (ProverEnvironment F) (Environment F) := ⟨ProverEnvironment.toEnvironment⟩

instance {α} : Coe (Environment F → α) (ProverEnvironment F → α) := ⟨fun f env => f env⟩
instance {α} : CoeOut (Environment F → α) (ProverEnvironment F → α) := ⟨fun f env => f env⟩

@[circuit_norm] abbrev Environment.fromArray [Field F] (row : Array F) (data : ProverData F) : Environment F where
  get j := row[j]?.getD 0
  data

namespace Expression
variable [Field F]

@[circuit_norm]
abbrev var (v : Variable F) : Expression F :=
  ExpressionWithLocation.var v

@[circuit_norm]
abbrev const (c : F) : Expression F :=
  ExpressionWithLocation.const c

@[circuit_norm]
abbrev add (x y : Expression F) : Expression F :=
  ExpressionWithLocation.add x y

@[circuit_norm]
abbrev mul (x y : Expression F) : Expression F :=
  ExpressionWithLocation.mul x y

/--
Evaluate expression given an external `environment` that determines the assignment
of all variables.

This is needed when we want to make statements about a circuit in the adversarial
situation where the prover can assign anything to variables.
-/
@[circuit_norm]
def eval (env : Environment F) : Expression F → F
  | .var v => env.get v.index
  | .const c => c
  | .add x y => eval env x + eval env y
  | .mul x y => eval env x * eval env y

def toString [Repr F] : Expression F → String
  | .var v => reprStr v
  | .const c => reprStr c
  | .add x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | .mul x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"

instance [Repr F] : Repr (Expression F) where
  reprPrec e _ := toString e

-- combine expressions elegantly
instance : Zero (Expression F) where zero := (ExpressionWithLocation.const 0 : Expression F)
instance : One (Expression F) where one := (ExpressionWithLocation.const 1 : Expression F)
instance : Add (Expression F) where add x y := (ExpressionWithLocation.add x y : Expression F)
instance : Neg (Expression F) where
  neg e := (ExpressionWithLocation.mul (ExpressionWithLocation.const (-1) : Expression F) e : Expression F)
instance : Sub (Expression F) where sub e₁ e₂ := (ExpressionWithLocation.add e₁ (-e₂) : Expression F)
instance : Mul (Expression F) where mul x y := (ExpressionWithLocation.mul x y : Expression F)

instance : Coe F (Expression F) where coe f := (ExpressionWithLocation.const f : Expression F)
instance {n : ℕ} [OfNat F n] : OfNat (Expression F) n where
  ofNat := (ExpressionWithLocation.const (OfNat.ofNat n) : Expression F)

instance : HMul F (Expression F) (Expression F) where
  hMul f e := (ExpressionWithLocation.mul (ExpressionWithLocation.const f : Expression F) e : Expression F)
instance : HMul (Expression F) F (Expression F) where
  hMul e f := (ExpressionWithLocation.mul e (ExpressionWithLocation.const f : Expression F) : Expression F)

instance : HDiv (Expression F) F (Expression F) where
  hDiv e f := (ExpressionWithLocation.mul (ExpressionWithLocation.const (f⁻¹ : F) : Expression F) e : Expression F)
instance : HDiv (Expression F) ℕ (Expression F) where
  hDiv e f := (ExpressionWithLocation.mul (ExpressionWithLocation.const (f⁻¹ : F) : Expression F) e : Expression F)

instance : HAdd (Expression F) (ExpressionWithLocation F ℕ) (Expression F) where
  hAdd x y := ExpressionWithLocation.add x (y : Expression F)
instance : HAdd (ExpressionWithLocation F ℕ) (Expression F) (Expression F) where
  hAdd x y := ExpressionWithLocation.add (x : Expression F) y
instance : HSub (Expression F) (ExpressionWithLocation F ℕ) (Expression F) where
  hSub x y :=
    let y' : Expression F := y
    ExpressionWithLocation.add x (-y')
instance : HSub (ExpressionWithLocation F ℕ) (Expression F) (Expression F) where
  hSub x y := ExpressionWithLocation.add (x : Expression F) (-y)
instance : HMul (Expression F) (ExpressionWithLocation F ℕ) (Expression F) where
  hMul x y := ExpressionWithLocation.mul x (y : Expression F)
instance : HMul (ExpressionWithLocation F ℕ) (Expression F) (Expression F) where
  hMul x y := ExpressionWithLocation.mul (x : Expression F) y

@[circuit_norm]
lemma eval_const (env : Environment F) (c : F) :
    Expression.eval env (Expression.const c) = c := by
  simp only [Expression.eval]

@[circuit_norm]
lemma eval_ofNat (env : Environment F) (n : ℕ) [OfNat F n] :
    Expression.eval env (OfNat.ofNat n : Expression F) = OfNat.ofNat n := by
  simp only [Expression.eval]

@[circuit_norm]
lemma eval_one (env : Environment F) :
    Expression.eval env (1 : Expression F) = 1 := by
  rw [eval_ofNat env 1]

@[circuit_norm]
lemma eval_neg (env : Environment F) (x : Expression F) :
    Expression.eval env (-x) = -Expression.eval env x := by
  simp only [Expression.eval]
  rw [neg_mul, one_mul]

@[circuit_norm]
lemma eval_neg_one (env : Environment F) :
    Expression.eval env (-1 : Expression F) = -1 := by
  rw [eval_neg, eval_one]

@[circuit_norm]
lemma eval_add_op (env : Environment F) (x y : Expression F) :
    Expression.eval env (x + y) = Expression.eval env x + Expression.eval env y := by
  change Expression.eval env (Expression.add x y) = Expression.eval env x + Expression.eval env y
  simp only [Expression.eval]

@[circuit_norm]
lemma eval_sub_op (env : Environment F) (x y : Expression F) :
    Expression.eval env (x - y) = Expression.eval env x - Expression.eval env y := by
  change Expression.eval env (Expression.add x (-y)) = Expression.eval env x - Expression.eval env y
  simp only [Expression.eval, sub_eq_add_neg]
  rw [neg_mul, one_mul]

@[circuit_norm]
lemma eval_mul_op (env : Environment F) (x y : Expression F) :
    Expression.eval env (x * y) = Expression.eval env x * Expression.eval env y := by
  change Expression.eval env (Expression.mul x y) = Expression.eval env x * Expression.eval env y
  simp only [Expression.eval]

-- TODO probably should just make Variable F := ℕ
instance {n : ℕ} : OfNat (Variable F) n where
  ofNat := { index := n }
end Expression

export Expression (var)

namespace ExpressionWithLocation
variable [Field F]

def toString [Repr F] [Repr L] : ExpressionWithLocation F L → String
  | var v => reprStr v
  | const c => reprStr c
  | add x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | mul x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"

instance [Repr F] [Repr L] : Repr (ExpressionWithLocation F L) where
  reprPrec e _ := toString e

@[circuit_norm]
def eval (x : ExpressionWithLocation F L) (env : EnvironmentWithLocation F L) : F :=
  match x with
  | var v => env.get v.index
  | const c => c
  | add x y => eval x env + eval y env
  | mul x y => eval x env * eval y env

instance : Zero (ExpressionWithLocation F L) where zero := const 0
instance : One (ExpressionWithLocation F L) where one := const 1
instance : Add (ExpressionWithLocation F L) where add := add
instance : Neg (ExpressionWithLocation F L) where neg e := mul (const (-1)) e
instance : Sub (ExpressionWithLocation F L) where sub e₁ e₂ := add e₁ (-e₂)
instance : Mul (ExpressionWithLocation F L) where mul := mul

end ExpressionWithLocation

instance [Field F] : CoeFun (EnvironmentWithLocation F L)
    (fun _ => (ExpressionWithLocation F L) → F) where
  coe env x := ExpressionWithLocation.eval x env

instance [Field F] : CoeFun (Environment F) (fun _ => (Expression F) → F) where
  coe env x := x.eval env

instance [Field F] : CoeFun (ProverEnvironment F) (fun _ => (Expression F) → F) where
  coe env x := x.eval env

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
    Expression.eval env (Expression.mul a b) = (Expression.eval env a) * (Expression.eval env b) := by
  simp only [Expression.eval]

/-- Expression.eval distributes over addition -/
@[circuit_norm]
lemma eval_add (env : Environment F) (a b : Expression F) :
    Expression.eval env (Expression.add a b) = (Expression.eval env a) + (Expression.eval env b) := by
  simp only [Expression.eval]

/-- Expression.eval distributes over Fin.foldl with addition -/
lemma eval_foldl (env : Environment F) (n : ℕ)
    (f : Expression F → Fin n → Expression F) (init : Expression F)
    (hf : ∀ (e : Expression F) (i : Fin n),
      Expression.eval env (f e i) = Expression.eval env (f (Expression.const (Expression.eval env e)) i)) :
    Expression.eval env (Fin.foldl n f init) =
    Fin.foldl n (fun (acc : F) (i : Fin n) => Expression.eval env (f (Expression.const acc) i)) (Expression.eval env init) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n' ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    -- Apply the inductive hypothesis with the appropriate function and assumption
    have hf' : ∀ (e : Expression F) (i : Fin n'),
      Expression.eval env (f e i.castSucc) = Expression.eval env (f (Expression.const (Expression.eval env e)) i.castSucc) := by
      intros e i
      exact hf e i.castSucc

    have h1 : Expression.eval env (Fin.foldl n' (fun x1 x2 => f x1 x2.castSucc) init) =
              Fin.foldl n' (fun acc i => Expression.eval env (f (Expression.const acc) i.castSucc)) (Expression.eval env init) :=
      ih (fun x i => f x i.castSucc) hf'

    -- Now apply the assumption to relate the two sides
    rw [hf (Fin.foldl n' (fun x1 x2 => f x1 x2.castSucc) init) (Fin.last n')]
    -- Rewrite using h1
    rw [h1]

end EvalLemmas
