import Midnight.SHA256.Witness

/-! Serializable Clean witness programs for the source SHA advice computations.
Every helper has an evaluation theorem against `Witness`; there are no `.native`
callbacks, oracle values or witness-independent placeholder assignments here.
These theorems describe honest witness computation. Gate soundness/completeness
is established separately by the semantic gadgets that use these programs.
-/

namespace Midnight.SHA256.WitnessIR
open Halo2

def readNat (cell : AssignedCell F) : NExpr F := .val (.expr cell)
def program (value : NExpr F) : WitgenIR F 1 := .ofFExpr (.ofNat value)

def spread32 (value : NExpr F) : NExpr F :=
  (List.range 32).foldl (fun acc i =>
    .lor acc (.shiftL (.land (.shiftR value (.const i)) (.const 1)) (.const (2 * i))))
    (.const 0)

def compactEven (value : NExpr F) : NExpr F :=
  let x := .land value (.const Witness.evenMask)
  let x := .land (.lor x (.shiftR x (.const 1))) (.const 0x3333333333333333)
  let x := .land (.lor x (.shiftR x (.const 2))) (.const 0x0f0f0f0f0f0f0f0f)
  let x := .land (.lor x (.shiftR x (.const 4))) (.const 0x00ff00ff00ff00ff)
  let x := .land (.lor x (.shiftR x (.const 8))) (.const 0x0000ffff0000ffff)
  .land (.lor x (.shiftR x (.const 16))) (.const 0x00000000ffffffff)

def evenBits (value : NExpr F) : NExpr F := compactEven value
def oddBits (value : NExpr F) : NExpr F := compactEven (.shiftR value (.const 1))
def negateSpread (value : NExpr F) : NExpr F := .lxor value (.const Witness.evenMask)

def limb (value : NExpr F) (slice : Witness.Slice) : NExpr F :=
  .mod (.shiftR value (.const slice.1)) (.const (2 ^ slice.2))

def limbs {n : Nat} (layout : Vector Witness.Slice n) (value : NExpr F) :
    Vector (NExpr F) n := layout.map (limb value)

def weighted {n : Nat} (recipe : Witness.Recipe n) (values : Vector (NExpr F) n) : NExpr F :=
  recipe.foldr (fun (exponent, index) acc =>
    .add (.mul (.const (4 ^ exponent)) values[index]) acc) (.const 0)

def sum (values : List (NExpr F)) : NExpr F := values.foldr .add (.const 0)
def sum32 (values : List (NExpr F)) : NExpr F := .mod (sum values) (.const Witness.wordModulus)
def carry32 (values : List (NExpr F)) : NExpr F := .div (sum values) (.const Witness.wordModulus)

section Evaluation
variable {Env : Type} [Witgen.WitgenEnv F Env (AssignedCell F)]
variable (ctx : Witgen.CtxOver F Env)

theorem eval_readNat (cell : AssignedCell F) :
    (readNat cell).eval ctx = FiniteField.val
      (Witgen.WitgenEnv.readVar ctx.env cell : F) := rfl

private theorem eval_foldl {α : Type} (items : List α)
    (step : NExpr F → α → NExpr F) (valueStep : Nat → α → Nat)
    (hstep : ∀ expression item, (step expression item).eval ctx =
      valueStep (expression.eval ctx) item) (initial : NExpr F) :
    (items.foldl step initial).eval ctx = items.foldl valueStep (initial.eval ctx) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, hstep]

theorem eval_spread32 (value : NExpr F) :
    (spread32 value).eval ctx = Witness.spread32 (value.eval ctx) := by
  exact eval_foldl ctx _ _ _ (fun _ _ => rfl) (.const 0)

theorem eval_evenBits (value : NExpr F) :
    (evenBits value).eval ctx = Witness.evenBits (value.eval ctx) := rfl

theorem eval_oddBits (value : NExpr F) :
    (oddBits value).eval ctx = Witness.oddBits (value.eval ctx) := rfl

theorem eval_negateSpread (value : NExpr F) :
    (negateSpread value).eval ctx = Witness.negateSpread (value.eval ctx) := rfl

theorem eval_limb (value : NExpr F) (slice : Witness.Slice) :
    (limb value slice).eval ctx = Witness.limb (value.eval ctx) slice := rfl

theorem eval_weighted {n : Nat} (recipe : Witness.Recipe n) (values : Vector (NExpr F) n) :
    (weighted recipe values).eval ctx =
      Witness.weighted recipe (values.map fun expression => expression.eval ctx) := by
  induction recipe with
  | nil => rfl
  | cons term rest ih =>
    rcases term with ⟨exponent, index⟩
    simp only [weighted, Witness.weighted, List.foldr_cons, Witgen.NExprOver.eval,
      Fin.getElem_fin, Vector.getElem_map] at *
    rw [ih]

theorem eval_sum (values : List (NExpr F)) :
    (sum values).eval ctx = (values.map fun expression => expression.eval ctx).sum := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [sum, List.foldr_cons, Witgen.NExprOver.eval, List.map_cons, List.sum_cons] at *
    rw [ih]

theorem eval_sum32 (values : List (NExpr F)) :
    (sum32 values).eval ctx =
      Witness.sum32 (values.map fun expression => expression.eval ctx) := by
  simp only [sum32, Witness.sum32, Witgen.NExprOver.eval, eval_sum]

theorem eval_carry32 (values : List (NExpr F)) :
    (carry32 values).eval ctx =
      Witness.carry32 (values.map fun expression => expression.eval ctx) := by
  simp only [carry32, Witness.carry32, Witgen.NExprOver.eval, eval_sum]

end Evaluation

/-- The actual single-advice program returns the field interpretation of the
input-driven integer expression in the real placed prover environment. -/
theorem eval_program (value : NExpr F) (env : Placed ProverEnvironment F) :
    ((program value).eval env)[0] = FiniteField.fromNat (value.eval { env }) := by
  exact Halo2.eval_ofFExpr_zero (.ofNat value) env

/-- Reusing a just-assigned plain cell gives exactly the source spread witness,
provided the natural witness fits the field. This is the completeness rewrite
used by the witness circuit's shared plain/spread assignment. -/
theorem eval_spread_readNat_of_assigned (value : NExpr F) (cell : AssignedCell F)
    (env : Placed ProverEnvironment F)
    (hassigned : cell.eval env.place env.env.toEnvironment =
      FiniteField.fromNat (value.eval { env }))
    (hbound : value.eval { env } < FiniteField.size F) :
    ((program (spread32 (readNat cell))).eval env)[0] =
      FiniteField.fromNat (Witness.spread32 (value.eval { env })) := by
  rw [eval_program, eval_spread32, eval_readNat, Halo2.WitgenEnv.readVar_halo2,
    hassigned, FiniteField.val_fromNat _ hbound]

end Midnight.SHA256.WitnessIR
