module

public import Clean.Circuit.WitnessIR

/-!
# Authoring sugar for the witness IR

Makes witness-IR programs read like normal code:

- typeclass operators on the IR expression types (`+ * - ⁻¹` on `FExpr`;
  `+ * / % &&& ||| ^^^ <<< >>>` on `U64Expr`), numeric literals via `OfNat`,
  and a coercion from circuit `Expression`s,
- dot-notation bridges `x.val : U64Expr` (on `Expression` and `FExpr`) and
  `n.toField : FExpr`,
- condition notation `=?` / `<?`,
- `VExpr.range n fun i => ...` — loop former whose body receives the index as an
  `U64Expr` (applied to `.idx` at construction time, so the lambda is authoring-time
  only and the result is first-order data),
- a builder monad `Witgen.M` with `letF`/`letU` for shared intermediate values.

Example (SHA256 `Add32`-style):
```
witnessVectorProgram 32 do
  let s ← (bitsVal a + bitsVal b) % ((2^32 : ℕ) : U64Expr F)
  return .range 32 fun i => ((s >>> i) % 2).toField
```
-/

@[expose] public section

variable {F : Type} {α β : Type}

namespace Clean

/-! ## Operators and coercions -/

instance : Coe (Expression F) (FExpr F) := ⟨.expr⟩
instance : Coe (Expression F) (field (FExpr F)) where
  coe e := .expr e
instance : Coe F (FExpr F) := ⟨.const⟩
instance : Coe F (field (FExpr F)) := ⟨.const⟩
instance {M : TypeMap} [ProvableType M] : Coe (M (Expression F)) (M (FExpr F)) where
  coe v := fromElements (toElements v |>.map .expr)

end Clean

namespace Witgen

/- Numeric literals are generic over the variable atom `V` (like the arithmetic
instances below), so `3`, `2`, … build the same `.const` regardless of whether variables
are main Clean's `Expression F` or Halo2-Clean's `AssignedCell F`. -/
instance {V : Type} {n : ℕ} [OfNat F n] : OfNat (FExprOver F V) n := ⟨.const (OfNat.ofNat n)⟩
/- The field arithmetic instances are generic over the variable atom `V`, so they cover
both main Clean's `FExpr F = FExprOver F (Expression F)` and Halo2-Clean's
`FExprOver F (AssignedCell F)` — a witness program builds the same arithmetic tree
regardless of how it reads circuit variables. -/
instance {V : Type} : Add (FExprOver F V) := ⟨.add⟩
instance {V : Type} : Mul (FExprOver F V) := ⟨.mul⟩
instance {V : Type} : Inv (FExprOver F V) := ⟨.inv⟩
@[reducible] instance {V : Type} : Inv (field (FExprOver F V)) :=
  (inferInstance : Inv (FExprOver F V))
instance {V : Type} [Field F] : Neg (FExprOver F V) := ⟨.neg⟩
instance {V : Type} [Field F] : Sub (FExprOver F V) := ⟨.sub⟩
instance {V : Type} : Coe (U64ExprOver F V) (FExprOver F V) := ⟨.ofU64⟩

end Witgen

namespace Clean
open Witgen

/- Heterogeneous arithmetic between circuit expressions and witness expressions: the
`Coe (Expression F) (FExpr F)` route stopped covering `binop%` elaboration after the
`FExprOver` generalization (the abbrev obscures the max-type computation), so the mixed
operations get explicit instances. -/
instance : HAdd (Expression F) (FExpr F) (FExpr F) := ⟨fun e x => .add (.expr e) x⟩
instance : HAdd (FExpr F) (Expression F) (FExpr F) := ⟨fun x e => .add x (.expr e)⟩
instance : HMul (Expression F) (FExpr F) (FExpr F) := ⟨fun e x => .mul (.expr e) x⟩
instance : HMul (FExpr F) (Expression F) (FExpr F) := ⟨fun x e => .mul x (.expr e)⟩
instance [Field F] : HSub (Expression F) (FExpr F) (FExpr F) := ⟨fun e x => FExprOver.sub (.expr e) x⟩
instance [Field F] : HSub (FExpr F) (Expression F) (FExpr F) := ⟨fun x e => FExprOver.sub x (.expr e)⟩

end Clean

namespace Witgen

/- The u64-sorted instances are atom-generic like the field-sorted ones above. -/
instance {V : Type} : Coe ℕ (U64ExprOver F V) := ⟨(.const <| UInt64.ofNat ·)⟩
instance {V : Type} : Coe UInt64 (U64ExprOver F V) := ⟨.const⟩
instance {V : Type} {n : ℕ} : OfNat (U64ExprOver F V) n := ⟨.const (OfNat.ofNat n)⟩
instance {V : Type} : Inhabited (U64ExprOver F V) where
  default := .const 0
instance {V : Type} : Add (U64ExprOver F V) := ⟨.add⟩
instance {V : Type} : Mul (U64ExprOver F V) := ⟨.mul⟩
instance {V : Type} : Div (U64ExprOver F V) := ⟨.div⟩
instance {V : Type} : HDiv (U64ExprOver F V) ℕ (U64ExprOver F V) where
  hDiv n m := .div n (.const (UInt64.ofNat m))
instance {V : Type} : Mod (U64ExprOver F V) := ⟨.mod⟩
instance {V : Type} : HMod (U64ExprOver F V) ℕ (U64ExprOver F V) where
  hMod n m := .mod n (.const (UInt64.ofNat m))
instance {V : Type} : AndOp (U64ExprOver F V) := ⟨.land⟩
instance {V : Type} : OrOp (U64ExprOver F V) := ⟨.lor⟩
instance {V : Type} : XorOp (U64ExprOver F V) := ⟨.lxor⟩
instance {V : Type} : ShiftLeft (U64ExprOver F V) := ⟨.shiftL⟩
instance {V : Type} : ShiftRight (U64ExprOver F V) := ⟨.shiftR⟩
instance {V : Type} : HShiftLeft (U64ExprOver F V) ℕ (U64ExprOver F V) where
  hShiftLeft n m := .shiftL n (.const (UInt64.ofNat m))
instance {V : Type} : HShiftRight (U64ExprOver F V) ℕ (U64ExprOver F V) where
  hShiftRight n m := .shiftR n (.const (UInt64.ofNat m))

end Witgen

namespace Clean

/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩

/-! The `FExpr.eval`/`U64Expr.eval` matchers do not unfold the operator instances above,
so evaluation would get stuck on operator-sugared IR. Desugar to constructors in
`circuit_norm` via per-operator rfl-lemmas; the evaluators' own match equations then apply. -/

@[circuit_norm] theorem FExpr.add_def {V : Type} (x y : Witgen.FExprOver F V) : x + y = .add x y := rfl
@[circuit_norm] theorem FExpr.mul_def {V : Type} (x y : Witgen.FExprOver F V) : x * y = .mul x y := rfl
@[circuit_norm] theorem FExpr.inv_def {V : Type} (x : Witgen.FExprOver F V) : x⁻¹ = .inv x := rfl
@[circuit_norm] theorem FExpr.neg_def {V : Type} [Field F] (x : Witgen.FExprOver F V) : -x = Witgen.FExprOver.neg x := rfl
@[circuit_norm] theorem FExpr.sub_def {V : Type} [Field F] (x y : Witgen.FExprOver F V) : x - y = Witgen.FExprOver.sub x y := rfl

@[circuit_norm] theorem U64Expr.add_def {V : Type} (x y : Witgen.U64ExprOver F V) : x + y = .add x y := rfl
@[circuit_norm] theorem U64Expr.mul_def {V : Type} (x y : Witgen.U64ExprOver F V) : x * y = .mul x y := rfl
@[circuit_norm] theorem U64Expr.div_def {V : Type} (x y : Witgen.U64ExprOver F V) : x / y = .div x y := rfl
@[circuit_norm] theorem U64Expr.hDiv_def {V : Type} (x : Witgen.U64ExprOver F V) (m : ℕ) :
  x / m = Witgen.U64ExprOver.div x (.const (UInt64.ofNat m)) := rfl
@[circuit_norm] theorem U64Expr.mod_def {V : Type} (x y : Witgen.U64ExprOver F V) : x % y = .mod x y := rfl
@[circuit_norm] theorem U64Expr.hMod_def {V : Type} (x : Witgen.U64ExprOver F V) (m : ℕ) :
  x % m = Witgen.U64ExprOver.mod x (.const (UInt64.ofNat m)) := rfl
@[circuit_norm] theorem U64Expr.land_def {V : Type} (x y : Witgen.U64ExprOver F V) : x &&& y = .land x y := rfl
@[circuit_norm] theorem U64Expr.lor_def {V : Type} (x y : Witgen.U64ExprOver F V) : x ||| y = .lor x y := rfl
@[circuit_norm] theorem U64Expr.lxor_def {V : Type} (x y : Witgen.U64ExprOver F V) : x ^^^ y = .lxor x y := rfl
@[circuit_norm] theorem U64Expr.shiftL_def {V : Type} (x y : Witgen.U64ExprOver F V) : x <<< y = .shiftL x y := rfl
@[circuit_norm] theorem U64Expr.shiftR_def {V : Type} (x y : Witgen.U64ExprOver F V) : x >>> y = .shiftR x y := rfl
@[circuit_norm] theorem U64Expr.hShiftL_def {V : Type} (x : Witgen.U64ExprOver F V) (m : ℕ) :
  x <<< m = Witgen.U64ExprOver.shiftL x (.const (UInt64.ofNat m)) := rfl
@[circuit_norm] theorem U64Expr.hShiftR_def {V : Type} (x : Witgen.U64ExprOver F V) (m : ℕ) :
  x >>> m = Witgen.U64ExprOver.shiftR x (.const (UInt64.ofNat m)) := rfl

/-- The `u64` value of a circuit expression, as a witness-IR expression: `x.val`. -/
abbrev Expression.val (e : Expression F) : U64Expr F := .val (.expr e)

/-- The `n` low bits of the field value of an IR expression, as a vector output. -/
abbrev VExpr.bits (n : ℕ) (e : FExpr F) : VExpr F n := .bitsOf e

/-- The `n` low bits of a circuit expression, as a vector output: `x.bits n`. -/
abbrev Expression.bits (e : Expression F) (n : ℕ) : VExpr F n := .bitsOf (.expr e)

end Clean

namespace Witgen

/-! ## Bridges as dot notation -/

/-- The `u64` value of an IR field expression (truncated `ZMod.val`): `e.val`. -/
abbrev FExprOver.val {V : Type} (e : FExprOver F V) : U64ExprOver F V := .val e

/-- Cast a u64-sorted IR expression back into the field (via `FiniteField.fromNat`). -/
abbrev U64ExprOver.toField {V : Type} (n : U64ExprOver F V) : FExprOver F V := .ofU64 n

/-- Cast a boolean expression to a field element that is 0 or 1. -/
abbrev BExprOver.toField {V : Type} [Field F] (b : BExprOver F V) : FExprOver F V := .ite b 1 0

/-- Bit `i` of the field value of an IR expression, as the field element `0` or `1`. -/
abbrev FExprOver.bit {V : Type} [Field F] (e : FExprOver F V) (i : ℕ) : FExprOver F V :=
  (BExprOver.bit e i).toField

/-! ## Conditions -/

/-- Overload witness-IR equality tests while keeping a single parser entry for
`=?`. Field-sorted operands become `BExpr.feq`; u64-sorted operands become
`BExpr.neq` (u64 equality).  The operand types are heterogeneous so
`x =? 0` can keep `x` as an `Expression` while interpreting `0` as an IR
constant, preserving the exported witness shape. The output is generic over the
variable atom `V` (an `outParam`, determined by the operands), so conditions build
over any atom — main Clean's `Expression F` or Halo2-Clean's `AssignedCell F`. -/
class EqCond (α β : Type) (F : outParam Type) (V : outParam Type) where
  /-- Build a witness-IR equality condition for these operand sorts. -/
  eqCond : α → β → BExprOver F V

@[inherit_doc EqCond.eqCond] infix:50 " =? " => EqCond.eqCond

instance {V : Type} : EqCond (FExprOver F V) (FExprOver F V) F V := ⟨.feq⟩
instance {V : Type} : EqCond (FExprOver F V) F F V where eqCond x y := .feq x (.const y)
instance {V : Type} : EqCond F (FExprOver F V) F V where eqCond x y := .feq (.const x) y
instance {V : Type} [NatCast F] : EqCond (FExprOver F V) ℕ F V where
  eqCond x n := .feq x (.const (n : F))
instance {V : Type} [NatCast F] : EqCond ℕ (FExprOver F V) F V where
  eqCond n x := .feq (.const (n : F)) x
instance {V : Type} : EqCond (U64ExprOver F V) (U64ExprOver F V) F V := ⟨.neq⟩
instance {V : Type} : EqCond (U64ExprOver F V) ℕ F V where
  eqCond x n := .neq x (.const (UInt64.ofNat n))
instance {V : Type} : EqCond ℕ (U64ExprOver F V) F V where
  eqCond n x := .neq (.const (UInt64.ofNat n)) x

/-- Overload witness-IR less-than tests while keeping a single parser entry for `<?`.
Field-sorted operands become `BExpr.flt` (comparing `FiniteField.val`s, so it stays exact
on fields wider than 64 bits); u64-sorted operands become `BExpr.lt`. Generic over the
variable atom `V` like `EqCond`. -/
class LtCond (α β : Type) (F : outParam Type) (V : outParam Type) where
  /-- Build a witness-IR less-than condition for these operand sorts. -/
  ltCond : α → β → BExprOver F V

@[inherit_doc LtCond.ltCond] infix:50 " <? " => LtCond.ltCond

instance {V : Type} : LtCond (FExprOver F V) (FExprOver F V) F V := ⟨.flt⟩
instance {V : Type} : LtCond (FExprOver F V) F F V where ltCond x y := .flt x (.const y)
instance {V : Type} : LtCond F (FExprOver F V) F V where ltCond x y := .flt (.const x) y
instance {V : Type} [NatCast F] : LtCond (FExprOver F V) ℕ F V where
  ltCond x n := .flt x (.const (n : F))
instance {V : Type} [NatCast F] : LtCond ℕ (FExprOver F V) F V where
  ltCond n x := .flt (.const (n : F)) x
instance {V : Type} : LtCond (U64ExprOver F V) (U64ExprOver F V) F V := ⟨.lt⟩
instance {V : Type} : LtCond (U64ExprOver F V) ℕ F V where
  ltCond x n := .lt x (.const (UInt64.ofNat n))
instance {V : Type} : LtCond ℕ (U64ExprOver F V) F V where
  ltCond n x := .lt (.const (UInt64.ofNat n)) x

instance {V : Type} : Inhabited (BExprOver F V) := ⟨.false⟩
instance {V : Type} : AndOp (BExprOver F V) := ⟨.and⟩

end Witgen

namespace Clean

open Witgen

instance : EqCond (Expression F) (FExpr F) F (Expression F) where eqCond x y := .feq x y
instance : EqCond (FExpr F) (Expression F) F (Expression F) where eqCond x y := .feq x y
instance : EqCond (Expression F) F F (Expression F) where eqCond x y := .feq x y
instance : EqCond F (Expression F) F (Expression F) where eqCond x y := .feq x y
instance [NatCast F] : EqCond (Expression F) ℕ F (Expression F) where eqCond x n := .feq x (n : F)
instance [NatCast F] : EqCond ℕ (Expression F) F (Expression F) where eqCond n x := .feq (n : F) x

instance : LtCond (Expression F) (FExpr F) F (Expression F) where ltCond x y := .flt x y
instance : LtCond (FExpr F) (Expression F) F (Expression F) where ltCond x y := .flt x y
instance : LtCond (Expression F) F F (Expression F) where ltCond x y := .flt x y
instance : LtCond F (Expression F) F (Expression F) where ltCond x y := .flt x y
instance [NatCast F] : LtCond (Expression F) ℕ F (Expression F) where ltCond x n := .flt x (n : F)
instance [NatCast F] : LtCond ℕ (Expression F) F (Expression F) where ltCond n x := .flt (n : F) x

/-! Desugar `=?`/`&&&` conditions to constructors, for the same reason as the operator
lemmas above. One lemma per `EqCond` instance. -/

@[circuit_norm] theorem EqCond.fexpr_fexpr_def (x y : FExpr F) : (x =? y) = BExpr.feq x y := rfl
@[circuit_norm] theorem EqCond.expr_fexpr_def (x : Expression F) (y : FExpr F) :
  (x =? y) = BExpr.feq (.expr x) y := rfl
@[circuit_norm] theorem EqCond.fexpr_expr_def (x : FExpr F) (y : Expression F) :
  (x =? y) = BExpr.feq x (.expr y) := rfl
@[circuit_norm] theorem EqCond.fexpr_const_def (x : FExpr F) (y : F) :
  (x =? y) = BExpr.feq x (.const y) := rfl
@[circuit_norm] theorem EqCond.const_fexpr_def (x : F) (y : FExpr F) :
  (x =? y) = BExpr.feq (.const x) y := rfl
@[circuit_norm] theorem EqCond.expr_const_def (x : Expression F) (y : F) :
  (x =? y) = BExpr.feq (.expr x) (.const y) := rfl
@[circuit_norm] theorem EqCond.const_expr_def (x : F) (y : Expression F) :
  (x =? y) = BExpr.feq (.const x) (.expr y) := rfl
@[circuit_norm] theorem EqCond.expr_nat_def [NatCast F] (x : Expression F) (n : ℕ) :
  (x =? n) = BExpr.feq (.expr x) (.const (n : F)) := rfl
@[circuit_norm] theorem EqCond.nat_expr_def [NatCast F] (n : ℕ) (x : Expression F) :
  (n =? x) = BExpr.feq (.const (n : F)) (.expr x) := rfl
@[circuit_norm] theorem EqCond.fexpr_nat_def [NatCast F] (x : FExpr F) (n : ℕ) :
  (x =? n) = BExpr.feq x (.const (n : F)) := rfl
@[circuit_norm] theorem EqCond.nat_fexpr_def [NatCast F] (n : ℕ) (x : FExpr F) :
  (n =? x) = BExpr.feq (.const (n : F)) x := rfl
@[circuit_norm] theorem EqCond.u64_u64_def (x y : U64Expr F) : (x =? y) = BExpr.neq x y := rfl
@[circuit_norm] theorem EqCond.u64_nat_def (x : U64Expr F) (n : ℕ) :
  (x =? n) = BExpr.neq x (.const (UInt64.ofNat n)) := rfl
@[circuit_norm] theorem EqCond.nat_u64_def (n : ℕ) (x : U64Expr F) :
  (n =? x) = BExpr.neq (.const (UInt64.ofNat n)) x := rfl
@[circuit_norm] theorem BExpr.and_def (x y : BExpr F) : x &&& y = BExpr.and x y := rfl

/-! Same treatment for `<?`. One lemma per `LtCond` instance. -/

@[circuit_norm] theorem LtCond.fexpr_fexpr_def (x y : FExpr F) : (x <? y) = BExpr.flt x y := rfl
@[circuit_norm] theorem LtCond.expr_fexpr_def (x : Expression F) (y : FExpr F) :
  (x <? y) = BExpr.flt (.expr x) y := rfl
@[circuit_norm] theorem LtCond.fexpr_expr_def (x : FExpr F) (y : Expression F) :
  (x <? y) = BExpr.flt x (.expr y) := rfl
@[circuit_norm] theorem LtCond.fexpr_const_def (x : FExpr F) (y : F) :
  (x <? y) = BExpr.flt x (.const y) := rfl
@[circuit_norm] theorem LtCond.const_fexpr_def (x : F) (y : FExpr F) :
  (x <? y) = BExpr.flt (.const x) y := rfl
@[circuit_norm] theorem LtCond.expr_const_def (x : Expression F) (y : F) :
  (x <? y) = BExpr.flt (.expr x) (.const y) := rfl
@[circuit_norm] theorem LtCond.const_expr_def (x : F) (y : Expression F) :
  (x <? y) = BExpr.flt (.const x) (.expr y) := rfl
@[circuit_norm] theorem LtCond.expr_nat_def [NatCast F] (x : Expression F) (n : ℕ) :
  (x <? n) = BExpr.flt (.expr x) (.const (n : F)) := rfl
@[circuit_norm] theorem LtCond.nat_expr_def [NatCast F] (n : ℕ) (x : Expression F) :
  (n <? x) = BExpr.flt (.const (n : F)) (.expr x) := rfl
@[circuit_norm] theorem LtCond.fexpr_nat_def [NatCast F] (x : FExpr F) (n : ℕ) :
  (x <? n) = BExpr.flt x (.const (n : F)) := rfl
@[circuit_norm] theorem LtCond.nat_fexpr_def [NatCast F] (n : ℕ) (x : FExpr F) :
  (n <? x) = BExpr.flt (.const (n : F)) x := rfl
@[circuit_norm] theorem LtCond.u64_u64_def (x y : U64Expr F) : (x <? y) = BExpr.lt x y := rfl
@[circuit_norm] theorem LtCond.u64_nat_def (x : U64Expr F) (n : ℕ) :
  (x <? n) = BExpr.lt x (.const (UInt64.ofNat n)) := rfl
@[circuit_norm] theorem LtCond.nat_u64_def (n : ℕ) (x : U64Expr F) :
  (n <? x) = BExpr.lt (.const (UInt64.ofNat n)) x := rfl

/-- Bit `i` of the field value of a circuit expression: `x.bit i`. -/
abbrev Expression.bit [Field F] (e : Expression F) (i : ℕ) : FExpr F :=
  (BExpr.bit (.expr e) i).toField

/-- The row index as a field element: `.idx`. -/
abbrev FExpr.idx : FExpr F := .ofU64 .idx

/-- A bit-valued condition cast into the field is the corresponding `0`/`1` element —
the same normal form `VExpr.bitsOf` evaluates to, so bit-decomposition proofs see one
shape whether the bit index is static or the loop index. Keyed as a pre-rewrite so it
fires before `FExpr.eval` unfolds the underlying `ite`. -/
@[circuit_norm ↓]
theorem FExpr.eval_bit [FiniteField F] (ctx : Ctx F) (e : FExpr F) (i : ℕ) :
    FExprOver.eval ctx (e.bit i) = FiniteField.fromNat (FiniteField.val (e.eval ctx) >>> i % 2) := by
  simp only [FExprOver.eval, BExprOver.eval, ← Nat.decide_shiftRight_mod_two_eq_one,
    decide_eq_true_eq]
  rcases Nat.mod_two_eq_zero_or_one (FiniteField.val (e.eval ctx) >>> i) with h | h <;>
    simp [h]

/-! ## Index access notation for .listGet -/

instance {F : Type} {n : ℕ} : GetElem (Vector F n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.const) i

instance {F : Type} {n : ℕ} : GetElem (Vector (Expression F) n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.expr) i

instance {F : Type} {n : ℕ} : GetElem (Var (fields n) F) (U64Expr F) (FExpr F) (fun _ _ => True) :=
  inferInstanceAs (GetElem (Vector (Expression F) n) (U64Expr F) _ _)

instance {F : Type} {n : ℕ} : GetElem (Vector (FExpr F) n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet v.toList i

instance {F : Type} : GetElem (Array F) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem xs i _ := FExpr.listGet (xs.toList.map FExpr.const) i

/-! Desugar the `GetElem` instances above to `FExpr.listGet`, for the same reason as the
operator lemmas: matchers and simp keying do not see through the instances. -/

@[circuit_norm] theorem getElem_vector_const_def {F : Type} {n : ℕ} (v : Vector F n) (i : U64Expr F) :
    v[i] = FExpr.listGet (v.toList.map FExpr.const) i := rfl
@[circuit_norm] theorem getElem_vector_expr_def {F : Type} {n : ℕ} (v : Vector (Expression F) n) (i : U64Expr F) :
    v[i] = FExpr.listGet (v.toList.map FExpr.expr) i := rfl
@[circuit_norm] theorem getElem_vector_fexpr_def {F : Type} {n : ℕ} (v : Vector (FExpr F) n) (i : U64Expr F) :
    v[i] = FExpr.listGet v.toList i := rfl
@[circuit_norm] theorem getElem_array_const_def {F : Type} (xs : Array F) (i : U64Expr F) :
    xs[i] = FExpr.listGet (xs.toList.map FExpr.const) i := rfl

@[circuit_norm]
lemma evalList_map_vector_const {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector F n) (i : ℕ) :
    FExprOver.evalList (V := Expression F) ctx i (v.toList.map FExpr.const) = if hi : i < n then v[i] else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExprOver.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList, FExprOver.eval]

@[circuit_norm]
lemma evalList_map_array_const {F : Type} {ctx : Ctx F} [FiniteField F] (xs : Array F) (i : ℕ) :
    FExprOver.evalList (V := Expression F) ctx i (xs.toList.map FExpr.const) = xs[i]?.getD 0 := by
  rcases xs with ⟨xs⟩
  induction xs generalizing i with
  | nil => simp [FExprOver.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList, FExprOver.eval]

@[circuit_norm]
lemma evalList_map_list_const {F : Type} {ctx : Ctx F} [FiniteField F] (xs : List F) (i : ℕ) :
    FExprOver.evalList (V := Expression F) ctx i (xs.map FExpr.const) = xs[i]?.getD 0 := by
  simpa using evalList_map_array_const (ctx := ctx) xs.toArray i

@[circuit_norm]
lemma evalList_map_const_comp {F α : Type} {ctx : Ctx F} [FiniteField F] (xs : List α) (f : α → F)
    (i : ℕ) : FExprOver.evalList (V := Expression F) ctx i (xs.map (FExpr.const ∘ f))
      = (xs[i]?.map f).getD 0 := by
  simpa using evalList_map_list_const (ctx := ctx) (xs.map f) i

@[circuit_norm]
lemma evalList_map_vector_expr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (Expression F) n) (i : ℕ) :
    FExprOver.evalList ctx i (v.toList.map FExpr.expr) = if hi : i < n then v[i].eval ctx.env else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExprOver.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList, FExprOver.eval, WitgenEnv.readVar_eq]

@[circuit_norm]
lemma evalList_map_vector_fexpr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (FExpr F) n) (i : ℕ) :
    FExprOver.evalList ctx i v.toList = if hi : i < n then v[i].eval ctx else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExprOver.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList]

/-! ## Loop former -/

/-- Vector output built per index; the body receives the loop index as an `U64Expr`.
The lambda is applied to `.idx` at construction time — authoring-time HOAS,
first-order result. -/
def VExpr.range (n : ℕ) (body : U64Expr F → FExpr F) : VExpr F n :=
  .mapRange n (body .idx)

@[circuit_norm]
theorem VExpr.range_def (n : ℕ) (body : U64Expr F → FExpr F) :
    VExpr.range n body = .mapRange n (body .idx) := rfl

end Clean

namespace Witgen

/-! ## Builder monad for stepped programs -/

/-- Witness-program builder, generic over the variable atom `V`: accumulates
`let`-steps, so shared values are written in `do`-notation via `letF` / `letU`.
Main Clean's `M` instantiates `V := Expression F`; Halo2-Clean instantiates
`V := AssignedCell F`. -/
@[reducible]
def MOver (F V : Type) (α : Type) : Type :=
  Array (StepOver F V) → α × Array (StepOver F V)

/-- Main Clean's witness-program builder (variables are circuit `Expression`s). -/
abbrev M (F : Type) : Type → Type := MOver F (Clean.Expression F)

instance {V : Type} : Monad (MOver F V) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'
  map f m := fun s => let (a, s') := m s; (f a, s')

attribute [circuit_norm] Array.size_empty Array.getElem?_push

@[circuit_norm]
theorem M.pure_def {V : Type} (a : α) :
    (pure a : MOver F V α) = fun s => (a, s) := rfl

@[circuit_norm]
theorem M.bind_def {V : Type} (m : MOver F V α) (f : α → MOver F V β) :
    (m >>= f) = fun s => let (a, s') := m s; f a s' := rfl

@[circuit_norm]
theorem M.map_def {V : Type} (f : α → β) (m : MOver F V α) :
    (f <$> m) = fun s => let (a, s') := m s; (f a, s') := rfl

/-- Bind a u64-sorted value as a shared step; returns a reference to it. -/
def letU {V : Type} (e : U64ExprOver F V) : MOver F V (U64ExprOver F V) :=
  fun s => (.localVar s.size, s.push (.letU e))

instance {V : Type} : CoeOut (U64ExprOver F V) (MOver F V (U64ExprOver F V)) := ⟨letU⟩

@[circuit_norm]
theorem letU_def {V : Type} (e : U64ExprOver F V) :
    letU e = fun s => (.localVar s.size, s.push (.letU e)) := rfl

/-- Bind a field-sorted value as a shared step; returns a reference to it. -/
def letF {V : Type} (e : FExprOver F V) : MOver F V (FExprOver F V) :=
  fun s => (.localVar s.size, s.push (.letF e))

instance {V : Type} : CoeOut (FExprOver F V) (MOver F V (FExprOver F V)) := ⟨letF⟩

@[circuit_norm]
theorem letF_def {V : Type} (e : FExprOver F V) :
    letF e = fun s => (.localVar s.size, s.push (.letF e)) := rfl

end Witgen

namespace Clean

instance {F: Type} [Field F] : Inhabited (FExpr F) where
  default := .const 0

instance [Field F] {value : TypeMap} [ProvableType value] : Inhabited (value (FExpr F)) where
  default := fromElements default

end Clean

namespace Witgen

namespace MOver
variable [FiniteField F] {value : TypeMap} [ProvableType value]
variable {V Env : Type} [WitgenEnv F Env V]

-- TODO WITGENIR the simp behavior currently takes an ugly low-level path because we were
-- too lazy to craft a high-level path that works in all cases

@[circuit_norm]
def eval (env : Env) (program : MOver F V (value (FExprOver F V))) : value F :=
  let (out, steps) := program #[]
  Witgen.eval { env, locals := evalSteps env steps.toList } out

@[circuit_norm]
def evalBool (env : Env) (program : MOver F V (BExprOver F V)) : Bool :=
  let (out, steps) := program #[]
  out.eval { env, locals := evalSteps env steps.toList }

@[circuit_norm]
def evalU64 (env : Env) (program : MOver F V (U64ExprOver F V)) : UInt64 :=
  let (out, steps) := program #[]
  out.eval { env, locals := evalSteps env steps.toList }

theorem eval_pure (out : value (FExprOver F V)) (env : Env) :
    eval env (fun s => (out, s)) = Witgen.eval { env } out := by
  rfl

/-- Assemble a witness program from a builder computation returning the output vector. -/
@[circuit_norm]
def toIR {n : ℕ} (program : MOver F V (VExprOver F V n)) : WitgenIROver F Env V n :=
  let (out, steps) := program #[]
  .ir steps.toList out

/-- Assemble a single-scalar witness program from a builder computation — the per-cell
form (halo2's `assignAdvice` and friends consume one scalar per cell). Irreducible so
whnf walking an ops list does not repeatedly unfold into the (stuck) program run —
`circuit_norm` still unfolds it via the equation, `with_unfolding_all` still sees through. -/
@[circuit_norm]
irreducible_def toIRScalar (program : MOver F V (FExprOver F V)) : WitgenIROver F Env V 1 :=
  toIR ((fun e => .lit #v[e]) <$> program)

/-- Not tagged `@[circuit_norm]`: `toIRLiteral` must stay intact inside `.witness`
operations so that `witnessProgram`'s completeness obligation can be recognized and
rewritten at the level of provable values (`ProverEnvironment.extendsVector_toIRLiteral`
in `Clean.Circuit.Basic`), instead of unfolding element-wise into `toElements` internals. -/
def toIRLiteral (program : MOver F V (value (FExprOver F V))) :
    WitgenIROver F Env V (size value) :=
  let (out, steps) := program #[]
  .ir steps.toList (.lit (toElements out))

@[computable_witnesses]
theorem eval_toIRLiteral (program : MOver F V (value (FExprOver F V))) (env : Env) :
    (program.toIRLiteral (Env := Env)).eval env = toElements (program.eval env) := by
  simp [toIRLiteral, eval, WitgenIROver.eval, Witgen.eval, ProvableType.toElements_fromElements, VExprOver.eval]

/-- A `toIRScalar` witness's assigned value is the program's scalar evaluation. Tagged
`@[circuit_norm]` so witness facts land on the high-level `MOver.eval` atom during the
pipeline's normalization — gadget proofs compare witness values against hint-program
values without ever seeing the program run (`(p #[]).1/.2`) spelling. -/
@[circuit_norm]
theorem eval_toIRScalar (program : MOver F V (FExprOver F V)) (env : Env) :
    ((toIRScalar program (Env := Env)).eval env)[0]
      = MOver.eval (value := field) env program := by
  rcases h : program #[] with ⟨out, steps⟩
  rw [toIRScalar, M.map_def]
  simp [toIR, eval, WitgenIROver.eval, h, VExprOver.eval]
  with_unfolding_all rfl

instance {α : Type} [Inhabited α] : Inhabited (MOver F V α) where
  default := pure default

end MOver

-- Main Clean spellings (`Witgen.M.eval` &c.) — aliases into the `V`-generic
-- `MOver` namespace, so existing call sites keep working.
namespace M
export MOver (eval evalBool evalU64 eval_pure toIR toIRScalar toIRLiteral eval_toIRLiteral)
end M
end Witgen

namespace Clean

namespace WitgenIR
variable [FiniteField F] {value : TypeMap} [ProvableType value]

/-- Evaluation of a composite witness program: the elements of the witnessed value's evaluation.
Not in `circuit_norm`, whose normal form keeps the folded program, the left-hand side of
`ProverEnvironment.extendsVector_ofCompositeFExpr` that completeness proofs rewrite with. -/
@[computable_witnesses]
theorem eval_ofCompositeFExpr {value : TypeMap} [ProvableType value]
    (e : value (FExpr F)) (env : ProverEnvironment F) :
    (ofCompositeFExpr e).eval env = toElements (Witgen.eval { env } e) := by
  change (Witgen.M.toIRLiteral (pure e)).eval env = _
  rw [Witgen.M.eval_toIRLiteral]
  rfl

end WitgenIR

/--
IR-backed prover-only inputs for `GeneralFormalCircuit.WithHint`.

The verifier view is erased to `Unit`; the prover view is a typed witness program evaluated
against the prover environment. The closure-backed escape hatch is `UnconstrainedNative`.
-/
structure Unconstrained (M : TypeMap) (F : Type) where
  program : Witgen.M F (M (FExpr F))

namespace Unconstrained
variable {value : TypeMap} [ProvableType value]
open Witgen

@[reducible] instance : CircuitType (Unconstrained value) where
  Var F := M F (value (FExpr F))
  ProverValue := value
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := Witgen.MOver.eval env program

instance [Field F] : Inhabited (Var (Unconstrained value) F) :=
  inferInstanceAs (Inhabited (M F (value (FExpr F))))

@[circuit_norm] lemma var_of_unconstrained :
    Var (Unconstrained value) F = M F (value (FExpr F)) := rfl

@[circuit_norm] lemma proverValue_of_unconstrained :
    ProverValue (Unconstrained value) F = value F := rfl

@[circuit_norm] lemma value_of_unconstrained :
    Value (Unconstrained value) F = Unit := rfl

@[circuit_norm] lemma eval_unconstrained [FiniteField F]
    (env : Environment F) (v : Var (Unconstrained value) F) :
    eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrained_prover [FiniteField F]
    (env : ProverEnvironment F) (v : Var (Unconstrained value) F) :
    eval env v = M.eval (value := value) env v := by
  rw [CircuitType.eval_prover (M := Unconstrained value)]
  rfl

@[circuit_norm] lemma eval_unconstrained_prover' [FiniteField F] :
  @eval (ProverEnvironment F) (M F (value (FExpr F))) (value F) (CircuitType.proverEval (Unconstrained value))
    = M.eval := by
  with_unfolding_all rfl

end Unconstrained

@[circuit_norm]
def unconstrained {value : TypeMap} [ProvableType value]
    (program : Witgen.M F (value (FExpr F))) : Var (Unconstrained value) F :=
  program

/-- IR-backed prover-only Boolean input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedBool (F : Type) where
  program : Witgen.M F (BExpr F)

namespace UnconstrainedBool
open Witgen

@[reducible] instance : CircuitType UnconstrainedBool where
  Var F := M F (BExpr F)
  ProverValue _ := Bool
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := Witgen.MOver.evalBool env program

instance : Inhabited (Var UnconstrainedBool F) :=
  inferInstanceAs (Inhabited (M F (BExpr F)))

@[circuit_norm] lemma var_of_unconstrainedBool :
    Var UnconstrainedBool F = M F (BExpr F) := rfl

@[circuit_norm] lemma proverValue_of_unconstrainedBool :
    ProverValue UnconstrainedBool F = Bool := rfl

@[circuit_norm] lemma value_of_unconstrainedBool :
    Value UnconstrainedBool F = Unit := rfl

@[circuit_norm] lemma eval_unconstrainedBool [FiniteField F]
    (env : Environment F) (v : Var UnconstrainedBool F) :
    eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrainedBool_prover [FiniteField F]
    (env : ProverEnvironment F) (v : Var UnconstrainedBool F) :
    eval env v = M.evalBool env v := by
  rw [CircuitType.eval_prover (M := UnconstrainedBool)]
  rfl

@[circuit_norm] lemma eval_unconstrainedBool_prover' [FiniteField F] :
  @eval (ProverEnvironment F) (M F (BExpr F)) Bool (CircuitType.proverEval UnconstrainedBool)
    = M.evalBool := by
  with_unfolding_all rfl

end UnconstrainedBool

@[circuit_norm]
def unconstrainedBool (program : Witgen.M F (BExpr F)) : Var UnconstrainedBool F :=
  program

/-- IR-backed prover-only u64 input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedU64 (F : Type) where
  program : Witgen.M F (U64Expr F)

namespace UnconstrainedU64
open Witgen

@[reducible] instance : CircuitType UnconstrainedU64 where
  Var F := M F (U64Expr F)
  ProverValue _ := UInt64
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := Witgen.MOver.evalU64 env program

instance : Inhabited (Var UnconstrainedU64 F) :=
  inferInstanceAs (Inhabited (M F (U64Expr F)))

@[circuit_norm] lemma var_of_unconstrainedU64 :
    Var UnconstrainedU64 F = M F (U64Expr F) := rfl

@[circuit_norm] lemma proverValue_of_unconstrainedU64 :
    ProverValue UnconstrainedU64 F = UInt64 := rfl

@[circuit_norm] lemma value_of_unconstrainedU64 :
    Value UnconstrainedU64 F = Unit := rfl

@[circuit_norm] lemma eval_unconstrainedU64 [FiniteField F]
    (env : Environment F) (v : Var UnconstrainedU64 F) :
    eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrainedU64_prover [FiniteField F]
    (env : ProverEnvironment F) (v : Var UnconstrainedU64 F) :
    eval env v = M.evalU64 env v := by
  rw [CircuitType.eval_prover (M := UnconstrainedU64)]
  rfl

@[circuit_norm] lemma eval_unconstrainedU64_prover' [FiniteField F] :
  @eval (ProverEnvironment F) (M F (U64Expr F)) UInt64 (CircuitType.proverEval UnconstrainedU64)
    = M.evalU64 := by
  with_unfolding_all rfl

end UnconstrainedU64

@[circuit_norm]
def unconstrainedU64 (program : Witgen.M F (U64Expr F)) : Var UnconstrainedU64 F :=
  program

end Clean
