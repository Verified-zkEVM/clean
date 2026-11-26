import Midnight.SHA256.Witness

/-! Serializable Clean witness programs for the source SHA advice computations.
Every helper has an evaluation theorem against `Witness`; there are no `.native`
callbacks, oracle values or witness-independent placeholder assignments here.
These theorems describe honest witness computation. Gate soundness/completeness
is established separately by the semantic gadgets that use these programs.
-/

namespace Midnight.SHA256.WitnessIR
open Halo2

def readNat (cell : AssignedCell F) : U64Expr F := .val (.expr cell)
def program (value : U64Expr F) : WitgenIR F 1 := .ofFExpr (.ofU64 value)

def spread32 (value : U64Expr F) : U64Expr F :=
  (List.range 32).foldl (fun acc i =>
    .lor acc (.shiftL (.land (.shiftR value (.const (UInt64.ofNat i))) (.const 1)) (.const (UInt64.ofNat (2 * i)))))
    (.const 0)

def compactEven (value : U64Expr F) : U64Expr F :=
  let x := .land value (.const (UInt64.ofNat Witness.evenMask))
  let x := .land (.lor x (.shiftR x (.const 1))) (.const 0x3333333333333333)
  let x := .land (.lor x (.shiftR x (.const 2))) (.const 0x0f0f0f0f0f0f0f0f)
  let x := .land (.lor x (.shiftR x (.const 4))) (.const 0x00ff00ff00ff00ff)
  let x := .land (.lor x (.shiftR x (.const 8))) (.const 0x0000ffff0000ffff)
  .land (.lor x (.shiftR x (.const 16))) (.const 0x00000000ffffffff)

def evenBits (value : U64Expr F) : U64Expr F := compactEven value
def oddBits (value : U64Expr F) : U64Expr F := compactEven (.shiftR value (.const 1))
def negateSpread (value : U64Expr F) : U64Expr F := .lxor value (.const (UInt64.ofNat Witness.evenMask))

def limb (value : U64Expr F) (slice : Witness.Slice) : U64Expr F :=
  .mod (.shiftR value (.const (UInt64.ofNat slice.1))) (.const (UInt64.ofNat (2 ^ slice.2)))

def limbs {n : Nat} (layout : Vector Witness.Slice n) (value : U64Expr F) :
    Vector (U64Expr F) n := layout.map (limb value)

def weighted {n : Nat} (recipe : Witness.Recipe n) (values : Vector (U64Expr F) n) : U64Expr F :=
  recipe.foldr (fun (exponent, index) acc =>
    .add (.mul (.const (UInt64.ofNat (4 ^ exponent))) values[index]) acc) (.const 0)

def sum (values : List (U64Expr F)) : U64Expr F := values.foldr .add (.const 0)
def sum32 (values : List (U64Expr F)) : U64Expr F := .mod (sum values) (.const (UInt64.ofNat Witness.wordModulus))
def carry32 (values : List (U64Expr F)) : U64Expr F := .div (sum values) (.const (UInt64.ofNat Witness.wordModulus))

section Evaluation
variable {Env : Type} [Witgen.WitgenEnv F Env (AssignedCell F)]
variable (ctx : Witgen.CtxOver F Env)

theorem eval_readNat (cell : AssignedCell F) :
    ((readNat cell).eval ctx).toNat =
      (Witgen.WitgenEnv.readVar ctx.env cell : F).val % 2 ^ 64 := by
  simp [readNat, Witgen.U64ExprOver.eval, Witgen.FExprOver.eval]

private theorem eval_foldl {α : Type} (items : List α)
    (step : U64Expr F → α → U64Expr F) (valueStep : Nat → α → Nat)
    (hstep : ∀ expression, ∀ item ∈ items, ((step expression item).eval ctx).toNat =
      valueStep ((expression.eval ctx).toNat) item) (initial : U64Expr F) :
    ((items.foldl step initial).eval ctx).toNat =
      items.foldl valueStep ((initial.eval ctx).toNat) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (fun e x hx => hstep e x (List.mem_cons_of_mem _ hx)),
      hstep initial item List.mem_cons_self]

theorem eval_spread32 (value : U64Expr F) :
    ((spread32 value).eval ctx).toNat = Witness.spread32 ((value.eval ctx).toNat) := by
  apply eval_foldl ctx _ _ _ _ (.const 0)
  intro expression i hi
  have hi32 : i < 32 := List.mem_range.mp hi
  have hi64 : (UInt64.ofNat i).toNat % 64 = i := by
    rw [UInt64.toNat_ofNat']
    omega
  have h2i64 : (UInt64.ofNat (2 * i)).toNat % 64 = 2 * i := by
    rw [UInt64.toNat_ofNat']
    omega
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hbit : (((value.eval ctx).toNat >>> i) &&& 1) ≤ 1 := Nat.and_le_right
  have hpow : 2 ^ (2 * i) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hshift : (((value.eval ctx).toNat >>> i) &&& 1) <<< (2 * i) < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    exact (Nat.mul_le_mul_right _ hbit).trans_lt (by simpa using hpow)
  simp only [Witgen.U64ExprOver.eval, UInt64.toNat_or, UInt64.toNat_shiftLeft,
    UInt64.toNat_and, UInt64.toNat_shiftRight, hi64, h2i64, h1, Nat.mod_eq_of_lt hshift]

theorem eval_compactEven (value : U64Expr F) :
    ((compactEven value).eval ctx).toNat = Witness.compactEven ((value.eval ctx).toNat) := by
  simp only [compactEven, Witness.compactEven, Witness.evenMask, Witgen.U64ExprOver.eval,
    UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_shiftRight]
  rfl

theorem eval_evenBits (value : U64Expr F) :
    ((evenBits value).eval ctx).toNat = Witness.evenBits ((value.eval ctx).toNat) :=
  eval_compactEven ctx value

theorem eval_oddBits (value : U64Expr F) :
    ((oddBits value).eval ctx).toNat = Witness.oddBits ((value.eval ctx).toNat) := by
  have h1 : (1 : UInt64).toNat % 64 = 1 := rfl
  simpa only [oddBits, Witness.oddBits, Witgen.U64ExprOver.eval, UInt64.toNat_shiftRight, h1] using
    eval_compactEven ctx (.shiftR value (.const 1))

theorem eval_negateSpread (value : U64Expr F) :
    ((negateSpread value).eval ctx).toNat = Witness.negateSpread ((value.eval ctx).toNat) := by
  simp only [negateSpread, Witness.negateSpread, Witness.evenMask, Witgen.U64ExprOver.eval,
    UInt64.toNat_xor]
  rfl

theorem eval_limb (value : U64Expr F) (slice : Witness.Slice)
    (h1 : slice.1 < 64 := by decide) (h2 : slice.2 < 64 := by decide) :
    ((limb value slice).eval ctx).toNat = Witness.limb ((value.eval ctx).toNat) slice := by
  have hs1 : (UInt64.ofNat slice.1).toNat % 64 = slice.1 := by
    rw [UInt64.toNat_ofNat']
    omega
  have hs2 : (UInt64.ofNat (2 ^ slice.2)).toNat = 2 ^ slice.2 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h2)]
  simp only [limb, Witness.limb, Witgen.U64ExprOver.eval, UInt64.toNat_mod,
    UInt64.toNat_shiftRight, hs1, hs2]

theorem eval_weighted {n : Nat} (recipe : Witness.Recipe n) (values : Vector (U64Expr F) n) :
    ((weighted recipe values).eval ctx).toNat =
      (Witness.weighted recipe (values.map fun expression => (expression.eval ctx).toNat)) % 2 ^ 64 := by
  induction recipe with
  | nil => rfl
  | cons term rest ih =>
    rcases term with ⟨exponent, index⟩
    simp only [weighted, Witness.weighted, List.foldr_cons, Witgen.U64ExprOver.eval,
      UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
      Fin.getElem_fin, Vector.getElem_map] at *
    rw [ih]
    simp [Nat.add_mod, Nat.mul_mod]

theorem eval_sum (values : List (U64Expr F)) :
    ((sum values).eval ctx).toNat =
      (values.map fun expression => (expression.eval ctx).toNat).sum % 2 ^ 64 := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [sum, List.foldr_cons, Witgen.U64ExprOver.eval, UInt64.toNat_add,
      List.map_cons, List.sum_cons] at *
    rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem eval_sum32 (values : List (U64Expr F)) :
    ((sum32 values).eval ctx).toNat =
      Witness.sum32 (values.map fun expression => (expression.eval ctx).toNat) := by
  have hmod : (UInt64.ofNat Witness.wordModulus).toNat = Witness.wordModulus := by
    decide
  simp only [sum32, Witness.sum32, Witgen.U64ExprOver.eval, UInt64.toNat_mod, eval_sum, hmod]
  exact Nat.mod_mod_of_dvd _ (by decide : Witness.wordModulus ∣ 2 ^ 64)

theorem eval_carry32 (values : List (U64Expr F))
    (hbound : (values.map fun expression => (expression.eval ctx).toNat).sum < 2 ^ 64) :
    ((carry32 values).eval ctx).toNat =
      Witness.carry32 (values.map fun expression => (expression.eval ctx).toNat) := by
  have hmod : (UInt64.ofNat Witness.wordModulus).toNat = Witness.wordModulus := by
    decide
  simp only [carry32, Witness.carry32, Witgen.U64ExprOver.eval, UInt64.toNat_div, eval_sum, hmod,
    Nat.mod_eq_of_lt hbound]

end Evaluation

/-- The actual single-advice program returns the field interpretation of the
input-driven integer expression in the real placed prover environment. -/
theorem eval_program (value : U64Expr F) (env : Placed ProverEnvironment F) :
    ((program value).eval env)[0] = FiniteField.fromNat ((value.eval { env }).toNat) := by
  exact Halo2.eval_ofFExpr_zero (.ofU64 value) env

/-- Reusing a just-assigned plain cell gives exactly the source spread witness,
provided the natural witness fits the field. This is the completeness rewrite
used by the witness circuit's shared plain/spread assignment. -/
theorem eval_spread_readNat_of_assigned (value : U64Expr F) (cell : AssignedCell F)
    (env : Placed ProverEnvironment F)
    (hassigned : cell.eval env.place env.env.toEnvironment =
      FiniteField.fromNat ((value.eval { env }).toNat))
    (hbound : (value.eval { env }).toNat < FiniteField.size F) :
    ((program (spread32 (readNat cell))).eval env)[0] =
      FiniteField.fromNat (Witness.spread32 ((value.eval { env }).toNat)) := by
  rw [eval_program, eval_spread32, eval_readNat, Halo2.WitgenEnv.readVar_halo2, hassigned]
  change FiniteField.fromNat (Witness.spread32 (ZMod.val ((value.eval { env }).toNat : F) % 2 ^ 64)) = _
  rw [ZMod.val_natCast_of_lt hbound, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]

end Midnight.SHA256.WitnessIR
