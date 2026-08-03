import Clean.Circuit.WitnessIR

/-!
# Authoring sugar for the witness IR

Makes witness-IR programs read like normal code:

- typeclass operators on the IR expression types (`+ * - ⁻¹` on `FExpr`;
  `+ * / % &&& ||| ^^^ <<< >>>` on `UExpr`), numeric literals via `OfNat`,
  and a coercion from circuit `Expression`s,
- dot-notation bridges `x.val : UExpr` (on `Expression` and `FExpr`) and
  `n.toField : FExpr`,
- condition notation `=?` / `<?`,
- `VExpr.range n fun i => ...` — loop former whose body receives the index as an
  `UExpr` (applied to `.idx` at construction time, so the lambda is authoring-time
  only and the result is first-order data),
- a builder monad `Witgen.M` with `letF`/`letU` for shared intermediate values.

Example (SHA256 `Add32`-style):
```
witnessVectorProgram 32 do
  let s ← (bitsVal a + bitsVal b) % ((2^32 : ℕ) : UExpr F)
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

instance : Coe ℕ (UExpr F) := ⟨.const⟩
instance {n : ℕ} : OfNat (UExpr F) n := ⟨.const n⟩
instance : Inhabited (UExpr F) where
  default := .const 0
instance : Add (UExpr F) := ⟨.add⟩
instance : Mul (UExpr F) := ⟨.mul⟩
instance : Div (UExpr F) := ⟨.div⟩
instance : HDiv (UExpr F) ℕ (UExpr F) where
  hDiv n m := .div n m
instance : Mod (UExpr F) := ⟨.mod⟩
instance : HMod (UExpr F) ℕ (UExpr F) where
  hMod n m := .mod n m
instance : AndOp (UExpr F) := ⟨.land⟩
instance : OrOp (UExpr F) := ⟨.lor⟩
instance : XorOp (UExpr F) := ⟨.lxor⟩
instance : ShiftLeft (UExpr F) := ⟨.shiftL⟩
instance : ShiftRight (UExpr F) := ⟨.shiftR⟩
instance : HShiftLeft (UExpr F) ℕ (UExpr F) where
  hShiftLeft n m := .shiftL n m
instance : HShiftRight (UExpr F) ℕ (UExpr F) where
  hShiftRight n m := .shiftR n m

/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩

/-! ## Bridges as dot notation -/

/-- The `u64` value of an IR field expression (truncated `ZMod.val`): `e.val`. -/
abbrev FExpr.val (e : FExpr F) : UExpr F := .val e

/-- The `u64` value of a circuit expression, as a witness-IR expression: `x.val`. -/
abbrev _root_.Expression.val (e : Expression F) : UExpr F := .val (.expr e)

/-- Cast a u64-sorted IR expression back into the field (via `FiniteField.fromNat`). -/
abbrev UExpr.toField (n : UExpr F) : FExpr F := .ofU64 n

/-- Bit `i` of the field value of an IR expression, as the field element `0` or `1`.
Unlike `(e.val >>> i) % 2` this is computed at the field level, so `i` may exceed 64. -/
abbrev FExpr.bit (e : FExpr F) (i : ℕ) : FExpr F := .bitOf e i

/-- Bit `i` of the field value of a circuit expression: `x.bit i`. -/
abbrev _root_.Expression.bit (e : Expression F) (i : ℕ) : FExpr F := .bitOf (.expr e) i

/-- The `n` low bits of the field value of an IR expression, as a vector output. -/
abbrev VExpr.bits (n : ℕ) (e : FExpr F) : VExpr F n := .bitsOf e

/-- The `n` low bits of a circuit expression, as a vector output: `x.bits n`. -/
abbrev _root_.Expression.bits (e : Expression F) (n : ℕ) : VExpr F n := .bitsOf (.expr e)

/-- Cast a boolean expression to a field element that is 0 or 1. -/
abbrev BExpr.toField [Field F] (b : BExpr F) : FExpr F := .ite b 1 0

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
instance : EqCond (UExpr F) (UExpr F) F := ⟨.neq⟩
instance : EqCond (UExpr F) ℕ F where eqCond x n := .neq x (.const n)
instance : EqCond ℕ (UExpr F) F where eqCond n x := .neq (.const n) x

@[inherit_doc BExpr.lt] infix:50 " <? " => BExpr.lt

instance : Inhabited (BExpr F) := ⟨.false⟩
instance : AndOp (BExpr F) := ⟨.and⟩

/-! ## Index access notation for .listGet -/

instance {F : Type} {n : ℕ} : GetElem (Vector F n) (UExpr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.const) i

instance {F : Type} {n : ℕ} : GetElem (Vector (Expression F) n) (UExpr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.expr) i

instance {F : Type} {n : ℕ} : GetElem (Var (fields n) F) (UExpr F) (FExpr F) (fun _ _ => True) :=
  inferInstanceAs (GetElem (Vector (Expression F) n) (UExpr F) _ _)

instance {F : Type} {n : ℕ} : GetElem (Vector (FExpr F) n) (UExpr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet v.toList i

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

/-- Vector output built per index; the body receives the loop index as an `UExpr`.
The lambda is applied to `.idx` at construction time — authoring-time HOAS,
first-order result. -/
def VExpr.range (n : ℕ) (body : UExpr F → FExpr F) : VExpr F n :=
  .mapRange n (body .idx)

@[circuit_norm]
theorem VExpr.range_def (n : ℕ) (body : UExpr F → FExpr F) :
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
def letU (e : UExpr F) : M F (UExpr F) :=
  fun s => (.localVar s.size, s.push (.letU e))

instance : CoeOut (UExpr F) (M F (UExpr F)) := ⟨letU⟩

@[circuit_norm]
theorem letU_def (e : UExpr F) :
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
def evalU64 (env : ProverEnvironment F) (program : M F (UExpr F)) : UInt64 :=
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

theorem eval_toIRLiteral (program : M F (value (FExpr F))) (env : ProverEnvironment F) :
    program.toIRLiteral.eval env = toElements (program.eval env) := by
  simp [toIRLiteral, eval, WitgenIR.eval, Witgen.eval, ProvableType.toElements_fromElements, VExpr.eval]

instance {α : Type} [Inhabited α] : Inhabited (M F α) where
  default := pure default
end M
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
  program : Witgen.M F (Witgen.UExpr F)

namespace UnconstrainedU64
open Witgen

@[reducible] instance : CircuitType UnconstrainedU64 where
  Var F := M F (UExpr F)
  ProverValue _ := UInt64
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.evalU64 env

instance : Inhabited (Var UnconstrainedU64 F) :=
  inferInstanceAs (Inhabited (M F (UExpr F)))

@[circuit_norm] lemma var_of_unconstrainedU64 :
    Var UnconstrainedU64 F = M F (UExpr F) := rfl

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
  @eval (ProverEnvironment F) (M F (UExpr F)) UInt64 (CircuitType.proverEval UnconstrainedU64)
    = M.evalU64 := by
  with_unfolding_all rfl

@[circuit_norm]
def unconstrainedU64 (program : Witgen.M F (Witgen.UExpr F)) : Var UnconstrainedU64 F :=
  program
end UnconstrainedU64

export UnconstrainedU64 (unconstrainedU64)
