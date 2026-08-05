import Clean.Circuit.WitnessIR

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

variable {F : Type} {α β : Type}

namespace Witgen

/-! ## Operators and coercions -/

instance : Coe (Expression F) (FExpr F) := ⟨.expr⟩
instance : Coe (Expression F) (field (FExpr F)) where
  coe e := .expr e
instance : Coe F (FExpr F) := ⟨.const⟩
instance : Coe F (field (FExpr F)) := ⟨.const⟩
instance {M : TypeMap} [ProvableType M] : Coe (M (Expression F)) (M (FExpr F)) where
  coe v := fromElements (toElements v |>.map .expr)
instance {n : ℕ} [OfNat F n] : OfNat (FExpr F) n := ⟨.const (OfNat.ofNat n)⟩
instance : Add (FExpr F) := ⟨.add⟩
instance : Mul (FExpr F) := ⟨.mul⟩
instance : Inv (FExpr F) := ⟨.inv⟩
@[reducible] instance : Inv (field (Witgen.FExpr F)) := (inferInstance : Inv (Witgen.FExpr F))
instance [Field F] : Neg (FExpr F) := ⟨.neg⟩
instance [Field F] : Sub (FExpr F) := ⟨.sub⟩

instance : Coe ℕ (U64Expr F) := ⟨(.const <| UInt64.ofNat ·)⟩
instance : Coe UInt64 (U64Expr F) := ⟨.const⟩
instance {n : ℕ} : OfNat (U64Expr F) n := ⟨.const (OfNat.ofNat n)⟩
instance : Inhabited (U64Expr F) where
  default := .const 0
instance : Add (U64Expr F) := ⟨.add⟩
instance : Mul (U64Expr F) := ⟨.mul⟩
instance : Div (U64Expr F) := ⟨.div⟩
instance : HDiv (U64Expr F) ℕ (U64Expr F) where
  hDiv n m := .div n (.const (UInt64.ofNat m))
instance : Mod (U64Expr F) := ⟨.mod⟩
instance : HMod (U64Expr F) ℕ (U64Expr F) where
  hMod n m := .mod n (.const (UInt64.ofNat m))
instance : AndOp (U64Expr F) := ⟨.land⟩
instance : OrOp (U64Expr F) := ⟨.lor⟩
instance : XorOp (U64Expr F) := ⟨.lxor⟩
instance : ShiftLeft (U64Expr F) := ⟨.shiftL⟩
instance : ShiftRight (U64Expr F) := ⟨.shiftR⟩
instance : HShiftLeft (U64Expr F) ℕ (U64Expr F) where
  hShiftLeft n m := .shiftL n (.const (UInt64.ofNat m))
instance : HShiftRight (U64Expr F) ℕ (U64Expr F) where
  hShiftRight n m := .shiftR n (.const (UInt64.ofNat m))

/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩

/-! The `FExpr.eval`/`U64Expr.eval` matchers do not unfold the operator instances above,
so evaluation would get stuck on operator-sugared IR. Desugar to constructors in
`circuit_norm` via per-operator rfl-lemmas; the evaluators' own match equations then apply. -/

@[circuit_norm] theorem FExpr.add_def (x y : FExpr F) : x + y = .add x y := rfl
@[circuit_norm] theorem FExpr.mul_def (x y : FExpr F) : x * y = .mul x y := rfl
@[circuit_norm] theorem FExpr.inv_def (x : FExpr F) : x⁻¹ = .inv x := rfl
@[circuit_norm] theorem FExpr.neg_def [Field F] (x : FExpr F) : -x = FExpr.neg x := rfl
@[circuit_norm] theorem FExpr.sub_def [Field F] (x y : FExpr F) : x - y = FExpr.sub x y := rfl

@[circuit_norm] theorem U64Expr.add_def (x y : U64Expr F) : x + y = .add x y := rfl
@[circuit_norm] theorem U64Expr.mul_def (x y : U64Expr F) : x * y = .mul x y := rfl
@[circuit_norm] theorem U64Expr.div_def (x y : U64Expr F) : x / y = .div x y := rfl
@[circuit_norm] theorem U64Expr.hDiv_def (x : U64Expr F) (m : ℕ) :
  x / m = U64Expr.div x (.const (UInt64.ofNat m)) := rfl
@[circuit_norm] theorem U64Expr.mod_def (x y : U64Expr F) : x % y = .mod x y := rfl
@[circuit_norm] theorem U64Expr.hMod_def (x : U64Expr F) (m : ℕ) :
  x % m = U64Expr.mod x (.const (UInt64.ofNat m)) := rfl
@[circuit_norm] theorem U64Expr.land_def (x y : U64Expr F) : x &&& y = .land x y := rfl
@[circuit_norm] theorem U64Expr.lor_def (x y : U64Expr F) : x ||| y = .lor x y := rfl
@[circuit_norm] theorem U64Expr.lxor_def (x y : U64Expr F) : x ^^^ y = .lxor x y := rfl
@[circuit_norm] theorem U64Expr.shiftL_def (x y : U64Expr F) : x <<< y = .shiftL x y := rfl
@[circuit_norm] theorem U64Expr.shiftR_def (x y : U64Expr F) : x >>> y = .shiftR x y := rfl
@[circuit_norm] theorem U64Expr.hShiftL_def (x : U64Expr F) (m : ℕ) :
  x <<< m = U64Expr.shiftL x (.const (UInt64.ofNat m)) := rfl
@[circuit_norm] theorem U64Expr.hShiftR_def (x : U64Expr F) (m : ℕ) :
  x >>> m = U64Expr.shiftR x (.const (UInt64.ofNat m)) := rfl

/-! ## Bridges as dot notation -/

/-- The `u64` value of an IR field expression (truncated `ZMod.val`): `e.val`. -/
abbrev FExpr.val (e : FExpr F) : U64Expr F := .val e

/-- The `u64` value of a circuit expression, as a witness-IR expression: `x.val`. -/
abbrev _root_.Expression.val (e : Expression F) : U64Expr F := .val (.expr e)

/-- Cast a u64-sorted IR expression back into the field (via `FiniteField.fromNat`). -/
abbrev U64Expr.toField (n : U64Expr F) : FExpr F := .ofU64 n

/-- The `n` low bits of the field value of an IR expression, as a vector output. -/
abbrev VExpr.bits (n : ℕ) (e : FExpr F) : VExpr F n := .bitsOf e

/-- The `n` low bits of a circuit expression, as a vector output: `x.bits n`. -/
abbrev _root_.Expression.bits (e : Expression F) (n : ℕ) : VExpr F n := .bitsOf (.expr e)

/-- Cast a boolean expression to a field element that is 0 or 1. -/
abbrev BExpr.toField [Field F] (b : BExpr F) : FExpr F := .ite b 1 0

/-- Bit `i` of the field value of an IR expression, as the field element `0` or `1`. -/
abbrev FExpr.bit [Field F] (e : FExpr F) (i : ℕ) : FExpr F := (BExpr.bit e i).toField

/-- Bit `i` of the field value of a circuit expression: `x.bit i`. -/
abbrev _root_.Expression.bit [Field F] (e : Expression F) (i : ℕ) : FExpr F :=
  (BExpr.bit (.expr e) i).toField

/-- A bit-valued condition cast into the field is the corresponding `0`/`1` element —
the same normal form `VExpr.bitsOf` evaluates to, so bit-decomposition proofs see one
shape whether the bit index is static or the loop index. Keyed as a pre-rewrite so it
fires before `FExpr.eval` unfolds the underlying `ite`. -/
@[circuit_norm ↓]
theorem FExpr.eval_bit [FiniteField F] (ctx : Ctx F) (e : FExpr F) (i : ℕ) :
    FExpr.eval ctx (e.bit i) = FiniteField.fromNat (FiniteField.val (e.eval ctx) >>> i % 2) := by
  simp only [FExpr.eval, BExpr.eval, ← Nat.decide_shiftRight_mod_two_eq_one,
    decide_eq_true_eq]
  rcases Nat.mod_two_eq_zero_or_one (FiniteField.val (e.eval ctx) >>> i) with h | h <;>
    simp [h]

/-! ## Conditions -/

/-- Overload witness-IR equality tests while keeping a single parser entry for
`=?`. Field-sorted operands become `BExpr.feq`; u64-sorted operands become
`BExpr.neq` (u64 equality).  The operand types are heterogeneous so
`x =? 0` can keep `x` as an `Expression` while interpreting `0` as an IR
constant, preserving the exported witness shape. -/
class EqCond (α β : Type) (F : outParam Type) where
  /-- Build a witness-IR equality condition for these operand sorts. -/
  eqCond : α → β → BExpr F

@[inherit_doc EqCond.eqCond] infix:50 " =? " => EqCond.eqCond

instance : EqCond (FExpr F) (FExpr F) F := ⟨.feq⟩
instance : EqCond (Expression F) (FExpr F) F where eqCond x y := .feq x y
instance : EqCond (FExpr F) (Expression F) F where eqCond x y := .feq x y
instance : EqCond (FExpr F) F F where eqCond x y := .feq x y
instance : EqCond F (FExpr F) F where eqCond x y := .feq y x
instance : EqCond (Expression F) F F where eqCond x y := .feq x y
instance : EqCond F (Expression F) F where eqCond x y := .feq x y
instance [NatCast F] : EqCond (Expression F) ℕ F where eqCond x n := .feq x (n : F)
instance [NatCast F] : EqCond ℕ (Expression F) F where eqCond n x := .feq (n : F) x
instance [NatCast F] : EqCond (FExpr F) ℕ F where eqCond x n := .feq x (n : F)
instance [NatCast F] : EqCond ℕ (FExpr F) F where eqCond n x := .feq (n : F) x
instance : EqCond (U64Expr F) (U64Expr F) F := ⟨.neq⟩
instance : EqCond (U64Expr F) ℕ F where eqCond x n := .neq x (.const (UInt64.ofNat n))
instance : EqCond ℕ (U64Expr F) F where eqCond n x := .neq (.const (UInt64.ofNat n)) x

/-- Overload witness-IR less-than tests while keeping a single parser entry for `<?`.
Field-sorted operands become `BExpr.flt` (comparing `FiniteField.val`s, so it stays exact
on fields wider than 64 bits); u64-sorted operands become `BExpr.lt`. -/
class LtCond (α β : Type) (F : outParam Type) where
  /-- Build a witness-IR less-than condition for these operand sorts. -/
  ltCond : α → β → BExpr F

@[inherit_doc LtCond.ltCond] infix:50 " <? " => LtCond.ltCond

instance : LtCond (FExpr F) (FExpr F) F := ⟨.flt⟩
instance : LtCond (Expression F) (FExpr F) F where ltCond x y := .flt x y
instance : LtCond (FExpr F) (Expression F) F where ltCond x y := .flt x y
instance : LtCond (FExpr F) F F where ltCond x y := .flt x y
instance : LtCond F (FExpr F) F where ltCond x y := .flt x y
instance : LtCond (Expression F) F F where ltCond x y := .flt x y
instance : LtCond F (Expression F) F where ltCond x y := .flt x y
instance [NatCast F] : LtCond (Expression F) ℕ F where ltCond x n := .flt x (n : F)
instance [NatCast F] : LtCond ℕ (Expression F) F where ltCond n x := .flt (n : F) x
instance [NatCast F] : LtCond (FExpr F) ℕ F where ltCond x n := .flt x (n : F)
instance [NatCast F] : LtCond ℕ (FExpr F) F where ltCond n x := .flt (n : F) x
instance : LtCond (U64Expr F) (U64Expr F) F := ⟨.lt⟩
instance : LtCond (U64Expr F) ℕ F where ltCond x n := .lt x (.const (UInt64.ofNat n))
instance : LtCond ℕ (U64Expr F) F where ltCond n x := .lt (.const (UInt64.ofNat n)) x

instance : Inhabited (BExpr F) := ⟨.false⟩
instance : AndOp (BExpr F) := ⟨.and⟩

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
  (x =? y) = BExpr.feq y (.const x) := rfl
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

/-! ## Index access notation for .listGet -/

instance {F : Type} {n : ℕ} : GetElem (Vector F n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.const) i

instance {F : Type} {n : ℕ} : GetElem (Vector (Expression F) n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.expr) i

instance {F : Type} {n : ℕ} : GetElem (Var (fields n) F) (U64Expr F) (FExpr F) (fun _ _ => True) :=
  inferInstanceAs (GetElem (Vector (Expression F) n) (U64Expr F) _ _)

instance {F : Type} {n : ℕ} : GetElem (Vector (FExpr F) n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet v.toList i

/-! Desugar the `GetElem` instances above to `FExpr.listGet`, for the same reason as the
operator lemmas: matchers and simp keying do not see through the instances. -/

@[circuit_norm] theorem getElem_vector_const_def {F : Type} {n : ℕ} (v : Vector F n) (i : U64Expr F) :
    v[i] = FExpr.listGet (v.toList.map FExpr.const) i := rfl
@[circuit_norm] theorem getElem_vector_expr_def {F : Type} {n : ℕ} (v : Vector (Expression F) n) (i : U64Expr F) :
    v[i] = FExpr.listGet (v.toList.map FExpr.expr) i := rfl
@[circuit_norm] theorem getElem_vector_fexpr_def {F : Type} {n : ℕ} (v : Vector (FExpr F) n) (i : U64Expr F) :
    v[i] = FExpr.listGet v.toList i := rfl

@[circuit_norm]
lemma evalList_map_vector_const {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector F n) (i : ℕ) :
    FExpr.evalList ctx i (v.toList.map FExpr.const) = if hi : i < n then v[i] else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExpr.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExpr.evalList, FExpr.eval]

@[circuit_norm]
lemma evalList_map_vector_expr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (Expression F) n) (i : ℕ) :
    FExpr.evalList ctx i (v.toList.map FExpr.expr) = if hi : i < n then v[i].eval ctx.env else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExpr.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExpr.evalList, FExpr.eval]

@[circuit_norm]
lemma evalList_map_vector_fexpr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (FExpr F) n) (i : ℕ) :
    FExpr.evalList ctx i v.toList = if hi : i < n then v[i].eval ctx else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExpr.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExpr.evalList]

/-! ## Loop former -/

/-- Vector output built per index; the body receives the loop index as an `U64Expr`.
The lambda is applied to `.idx` at construction time — authoring-time HOAS,
first-order result. -/
def VExpr.range (n : ℕ) (body : U64Expr F → FExpr F) : VExpr F n :=
  .mapRange n (body .idx)

@[circuit_norm]
theorem VExpr.range_def (n : ℕ) (body : U64Expr F → FExpr F) :
    VExpr.range n body = .mapRange n (body .idx) := rfl

/-! ## Builder monad for stepped programs -/

/-- Witness-program builder: accumulates `let`-steps, so shared values are written
in `do`-notation via `letF` / `letU`. -/
def M (F : Type) (α : Type) : Type :=
  Array (Step F) → α × Array (Step F)

instance : Monad (M F) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'
  map f m := fun s => let (a, s') := m s; (f a, s')

attribute [circuit_norm] Array.size_empty Array.getElem?_push

@[circuit_norm]
theorem M.pure_def (a : α) :
    (pure a : M F α) = fun s => (a, s) := rfl

@[circuit_norm]
theorem M.bind_def (m : M F α) (f : α → M F β) :
    (m >>= f) = fun s => let (a, s') := m s; f a s' := rfl

@[circuit_norm]
theorem M.map_def (f : α → β) (m : M F α) :
    (f <$> m) = fun s => let (a, s') := m s; (f a, s') := rfl

/-- Bind a u64-sorted value as a shared step; returns a reference to it. -/
def letU (e : U64Expr F) : M F (U64Expr F) :=
  fun s => (.localVar s.size, s.push (.letU e))

instance : CoeOut (U64Expr F) (M F (U64Expr F)) := ⟨letU⟩

@[circuit_norm]
theorem letU_def (e : U64Expr F) :
    letU e = fun s => (.localVar s.size, s.push (.letU e)) := rfl

/-- Bind a field-sorted value as a shared step; returns a reference to it. -/
def letF (e : FExpr F) : M F (FExpr F) :=
  fun s => (.localVar s.size, s.push (.letF e))

instance : CoeOut (FExpr F) (M F (FExpr F)) := ⟨letF⟩

@[circuit_norm]
theorem letF_def (e : FExpr F) :
    letF e = fun s => (.localVar s.size, s.push (.letF e)) := rfl

instance {F: Type} [Field F] : Inhabited (FExpr F) where
  default := .const 0

instance [Field F] {value : TypeMap} [ProvableType value] : Inhabited (value (FExpr F)) where
  default := fromElements default

namespace M
variable [FiniteField F] {value : TypeMap} [ProvableType value]

-- TODO WITGENIR the simp behavior currently takes an ugly low-level path because we were
-- too lazy to craft a high-level path that works in all cases

@[circuit_norm]
def eval (env : ProverEnvironment F) (program : M F (value (FExpr F))) : value F :=
  let (out, steps) := program #[]
  Witgen.eval { env, locals := evalSteps env steps.toList } out

@[circuit_norm]
def evalBool (env : ProverEnvironment F) (program : M F (BExpr F)) : Bool :=
  let (out, steps) := program #[]
  out.eval { env, locals := evalSteps env steps.toList }

@[circuit_norm]
def evalU64 (env : ProverEnvironment F) (program : M F (U64Expr F)) : UInt64 :=
  let (out, steps) := program #[]
  out.eval { env, locals := evalSteps env steps.toList }

theorem eval_pure (out : value (FExpr F)) (env : ProverEnvironment F) :
    eval env (fun s => (out, s)) = Witgen.eval { env } out := by
  rfl

/-- Assemble a witness program from a builder computation returning the output vector. -/
@[circuit_norm]
def toIR {n : ℕ} (program : M F (VExpr F n)) : WitgenIR F n :=
  let (out, steps) := program #[]
  .ir steps.toList out

/-- Not tagged `@[circuit_norm]`: `toIRLiteral` must stay intact inside `.witness`
operations so that `witnessProgram`'s completeness obligation can be recognized and
rewritten at the level of provable values (`ProverEnvironment.extendsVector_toIRLiteral`
in `Clean.Circuit.Basic`), instead of unfolding element-wise into `toElements` internals. -/
def toIRLiteral (program : M F (value (FExpr F))) : WitgenIR F (size value) :=
  let (out, steps) := program #[]
  .ir steps.toList (.lit (toElements out))

@[computable_witnesses_norm]
theorem eval_toIRLiteral (program : M F (value (FExpr F))) (env : ProverEnvironment F) :
    program.toIRLiteral.eval env = toElements (program.eval env) := by
  simp [toIRLiteral, eval, WitgenIR.eval, Witgen.eval, ProvableType.toElements_fromElements, VExpr.eval]

instance {α : Type} [Inhabited α] : Inhabited (M F α) where
  default := pure default
end M

namespace WitgenIR
variable [FiniteField F] {value : TypeMap} [ProvableType value]

/-- TODO this is not in `circuit_norm`, but currently needed for `computableWitnesses` proofs.
in `circuit_norm` it would change the normal form away from the LHS
of `ProverEnvironment.extendsVector_ofCompositeFExpr` which is an important
rewrite lemma in completeness proofs. -/
@[computable_witnesses_norm]
theorem eval_ofCompositeFExpr {value : TypeMap} [ProvableType value]
    (e : value (FExpr F)) (env : ProverEnvironment F) :
    (ofCompositeFExpr e).eval env = toElements (Witgen.eval { env } e) := by
  change (M.toIRLiteral (pure e)).eval env = _
  rw [M.eval_toIRLiteral]
  rfl

/--
TODO this would be the preferred form of `eval_ofCompositeFExpr` for `computableWitnesses` proofs,
but empirically doesn't fire early enough before the implicit `size value` Vector length (in `eval`) gets rewritten
to a literal which stops making this fire in simp. -/
@[circuit_norm ↓ high]
theorem eval_ofCompositeFExpr_eq_iff (xs : value (FExpr F)) (env env' : ProverEnvironment F) :
    (ofCompositeFExpr xs).eval env = (ofCompositeFExpr xs).eval env' ↔
    Witgen.eval { env } xs = Witgen.eval { env := env' } xs := by
  simp_rw [eval_ofCompositeFExpr, ProvableType.toElements_inj_iff]

end WitgenIR
end Witgen

/--
IR-backed prover-only inputs for `GeneralFormalCircuit.WithHint`.

The verifier view is erased to `Unit`; the prover view is a typed witness program evaluated
against the prover environment. The closure-backed escape hatch is `UnconstrainedNative`.
-/
structure Unconstrained (M : TypeMap) (F : Type) where
  program : Witgen.M F (M (Witgen.FExpr F))

namespace Unconstrained
variable {value : TypeMap} [ProvableType value]
open Witgen

@[reducible] instance : CircuitType (Unconstrained value) where
  Var F := M F (value (FExpr F))
  ProverValue := value
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.eval env

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

@[circuit_norm]
def unconstrained (program : Witgen.M F (value (Witgen.FExpr F))) : Var (Unconstrained value) F :=
  program
end Unconstrained

export Unconstrained (unconstrained)

/-- IR-backed prover-only Boolean input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedBool (F : Type) where
  program : Witgen.M F (Witgen.BExpr F)

namespace UnconstrainedBool
open Witgen

@[reducible] instance : CircuitType UnconstrainedBool where
  Var F := M F (BExpr F)
  ProverValue _ := Bool
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.evalBool env

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

@[circuit_norm]
def unconstrainedBool (program : Witgen.M F (Witgen.BExpr F)) : Var UnconstrainedBool F :=
  program
end UnconstrainedBool

export UnconstrainedBool (unconstrainedBool)

/-- IR-backed prover-only u64 input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedU64 (F : Type) where
  program : Witgen.M F (Witgen.U64Expr F)

namespace UnconstrainedU64
open Witgen

@[reducible] instance : CircuitType UnconstrainedU64 where
  Var F := M F (U64Expr F)
  ProverValue _ := UInt64
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.evalU64 env

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

@[circuit_norm]
def unconstrainedU64 (program : Witgen.M F (Witgen.U64Expr F)) : Var UnconstrainedU64 F :=
  program
end UnconstrainedU64

export UnconstrainedU64 (unconstrainedU64)
