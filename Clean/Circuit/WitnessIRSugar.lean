import Clean.Circuit.WitnessIR

/-!
# Authoring sugar for the witness IR

Makes witness-IR programs read like normal code:

- typeclass operators on the IR expression types (`+ * - ⁻¹` on `FExpr`;
  `+ * / % &&& ||| ^^^ <<< >>>` on `NExpr`), numeric literals via `OfNat`,
  and a coercion from circuit `Expression`s,
- dot-notation bridges `x.val : NExpr` (on `Expression` and `FExpr`) and
  `n.toField : FExpr`,
- condition notation `=?` / `<?`,
- `VExpr.range n fun i => ...` — loop former whose body receives the index as an
  `NExpr` (applied to `.idx` at construction time, so the lambda is authoring-time
  only and the result is first-order data),
- a builder monad `Witgen.M` with `letF`/`letN` for shared intermediate values.

Example (SHA256 `Add32`-style):
```
witnessVectorProgram 32 do
  let s ← (bitsVal a + bitsVal b) % ((2^32 : ℕ) : NExpr F)
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
@[reducible] instance : Inv (field (Witgen.FExpr F)) := (inferInstance : Inv (Witgen.FExpr F))
instance {V : Type} [Field F] : Neg (FExprOver F V) := ⟨.neg⟩
instance {V : Type} [Field F] : Sub (FExprOver F V) := ⟨.sub⟩

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

/- The Nat-sorted instances are atom-generic like the field-sorted ones above. -/
instance {V : Type} : Coe ℕ (NExprOver F V) := ⟨.const⟩
instance {V : Type} {n : ℕ} : OfNat (NExprOver F V) n := ⟨.const n⟩
instance {V : Type} : Inhabited (NExprOver F V) where
  default := .const 0
instance {V : Type} : Add (NExprOver F V) := ⟨.add⟩
instance {V : Type} : Mul (NExprOver F V) := ⟨.mul⟩
instance {V : Type} : Div (NExprOver F V) := ⟨.div⟩
instance {V : Type} : HDiv (NExprOver F V) ℕ (NExprOver F V) where
  hDiv n m := .div n m
instance {V : Type} : Mod (NExprOver F V) := ⟨.mod⟩
instance {V : Type} : HMod (NExprOver F V) ℕ (NExprOver F V) where
  hMod n m := .mod n m
instance {V : Type} : AndOp (NExprOver F V) := ⟨.land⟩
instance {V : Type} : OrOp (NExprOver F V) := ⟨.lor⟩
instance {V : Type} : XorOp (NExprOver F V) := ⟨.lxor⟩
instance {V : Type} : ShiftLeft (NExprOver F V) := ⟨.shiftL⟩
instance {V : Type} : ShiftRight (NExprOver F V) := ⟨.shiftR⟩
instance {V : Type} : HShiftLeft (NExprOver F V) ℕ (NExprOver F V) where
  hShiftLeft n m := .shiftL n m
instance {V : Type} : HShiftRight (NExprOver F V) ℕ (NExprOver F V) where
  hShiftRight n m := .shiftR n m

/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩

/-! ## Bridges as dot notation -/

/-- The `ℕ` value of an IR field expression: `e.val`. -/
abbrev FExprOver.val {V : Type} (e : FExprOver F V) : NExprOver F V := .val e

/-- The `ℕ` value of a circuit expression, as a witness-IR expression: `x.val`. -/
abbrev _root_.Expression.val (e : Expression F) : NExpr F := .val (.expr e)

/-- Cast a Nat-sorted IR expression back into the field (via `FiniteField.fromNat`). -/
abbrev NExprOver.toField {V : Type} (n : NExprOver F V) : FExprOver F V := .ofNat n

/-- Cast a boolean expression to a field element that is 0 or 1. -/
abbrev BExprOver.toField {V : Type} [Field F] (b : BExprOver F V) : FExprOver F V := .ite b 1 0

/-! ## Conditions -/

/-- Overload witness-IR equality tests while keeping a single parser entry for
`=?`. Field-sorted operands become `BExpr.feq`; Nat-sorted operands become
`BExpr.neq` (Nat equality).  The operand types are heterogeneous so
`x =? 0` can keep `x` as an `Expression` while interpreting `0` as an IR
constant, preserving the exported witness shape. The output is generic over the
variable atom `V` (an `outParam`, determined by the operands), so conditions build
over any atom — main Clean's `Expression F` or Halo2-Clean's `AssignedCell F`. -/
class EqCond (α β : Type) (F : outParam Type) (V : outParam Type) where
  /-- Build a witness-IR equality condition for these operand sorts. -/
  eqCond : α → β → BExprOver F V

@[inherit_doc EqCond.eqCond] infix:50 " =? " => EqCond.eqCond

instance {V : Type} : EqCond (FExprOver F V) (FExprOver F V) F V := ⟨.feq⟩
instance : EqCond (Expression F) (FExpr F) F (Expression F) where eqCond x y := .feq x y
instance : EqCond (FExpr F) (Expression F) F (Expression F) where eqCond x y := .feq x y
instance {V : Type} : EqCond (FExprOver F V) F F V where eqCond x y := .feq x (.const y)
instance {V : Type} : EqCond F (FExprOver F V) F V where eqCond x y := .feq (.const x) y
instance : EqCond (Expression F) F F (Expression F) where eqCond x y := .feq x y
instance : EqCond F (Expression F) F (Expression F) where eqCond x y := .feq x y
instance [NatCast F] : EqCond (Expression F) ℕ F (Expression F) where eqCond x n := .feq x (n : F)
instance [NatCast F] : EqCond ℕ (Expression F) F (Expression F) where eqCond n x := .feq (n : F) x
instance {V : Type} [NatCast F] : EqCond (FExprOver F V) ℕ F V where
  eqCond x n := .feq x (.const (n : F))
instance {V : Type} [NatCast F] : EqCond ℕ (FExprOver F V) F V where
  eqCond n x := .feq (.const (n : F)) x
instance {V : Type} : EqCond (NExprOver F V) (NExprOver F V) F V := ⟨.neq⟩
instance {V : Type} : EqCond (NExprOver F V) ℕ F V where eqCond x n := .neq x (.const n)
instance {V : Type} : EqCond ℕ (NExprOver F V) F V where eqCond n x := .neq (.const n) x

@[inherit_doc BExpr.lt] infix:50 " <? " => BExpr.lt

instance {V : Type} : Inhabited (BExprOver F V) := ⟨.false⟩
instance {V : Type} : AndOp (BExprOver F V) := ⟨.and⟩

/-! ## Index access notation for .listGet -/

instance {F : Type} {n : ℕ} : GetElem (Vector F n) (NExpr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.const) i

instance {F : Type} {n : ℕ} : GetElem (Vector (Expression F) n) (NExpr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.expr) i

instance {F : Type} {n : ℕ} : GetElem (Var (fields n) F) (NExpr F) (FExpr F) (fun _ _ => True) :=
  inferInstanceAs (GetElem (Vector (Expression F) n) (NExpr F) _ _)

instance {F : Type} {n : ℕ} : GetElem (Vector (FExpr F) n) (NExpr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet v.toList i

@[circuit_norm]
lemma evalList_map_vector_const {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector F n) (i : ℕ) :
    FExprOver.evalList (V := Expression F) ctx i (v.toList.map FExpr.const) = if hi : i < n then v[i] else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExprOver.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList, FExprOver.eval]

@[circuit_norm]
lemma evalList_map_vector_expr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (Expression F) n) (i : ℕ) :
    FExprOver.evalList ctx i (v.toList.map FExpr.expr) = if hi : i < n then v[i].eval ctx.env else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExprOver.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList, FExprOver.eval, WitgenEnv.readVar_main]

@[circuit_norm]
lemma evalList_map_vector_fexpr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (FExpr F) n) (i : ℕ) :
    FExprOver.evalList ctx i v.toList = if hi : i < n then v[i].eval ctx else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExprOver.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList]

/-! ## Loop former -/

/-- Vector output built per index; the body receives the loop index as an `NExpr`.
The lambda is applied to `.idx` at construction time — authoring-time HOAS,
first-order result. -/
def VExpr.range (n : ℕ) (body : NExpr F → FExpr F) : VExpr F n :=
  .mapRange n (body .idx)

@[circuit_norm]
theorem VExpr.range_def (n : ℕ) (body : NExpr F → FExpr F) :
    VExpr.range n body = .mapRange n (body .idx) := rfl

/-! ## Builder monad for stepped programs -/

/-- Witness-program builder: accumulates `let`-steps, so shared values are written
in `do`-notation via `letF` / `letN`. -/
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

/-- Bind a Nat-sorted value as a shared step; returns a reference to it. -/
def letN (e : NExpr F) : M F (NExpr F) :=
  fun s => (.localVar s.size, s.push (.letN e))

instance : CoeOut (NExpr F) (M F (NExpr F)) := ⟨letN⟩

@[circuit_norm]
theorem letN_def (e : NExpr F) :
    letN e = fun s => (.localVar s.size, s.push (.letN e)) := rfl

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
def evalNat (env : ProverEnvironment F) (program : M F (NExpr F)) : ℕ :=
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
  simp [toIRLiteral, eval, WitgenIROver.eval, Witgen.eval, ProvableType.toElements_fromElements, VExprOver.eval]

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

/-- IR-backed prover-only Nat input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedNat (F : Type) where
  program : Witgen.M F (Witgen.NExpr F)

namespace UnconstrainedNat
open Witgen

@[reducible] instance : CircuitType UnconstrainedNat where
  Var F := M F (NExpr F)
  ProverValue _ := ℕ
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.evalNat env

instance : Inhabited (Var UnconstrainedNat F) :=
  inferInstanceAs (Inhabited (M F (NExpr F)))

@[circuit_norm] lemma var_of_unconstrainedNat :
    Var UnconstrainedNat F = M F (NExpr F) := rfl

@[circuit_norm] lemma proverValue_of_unconstrainedNat :
    ProverValue UnconstrainedNat F = ℕ := rfl

@[circuit_norm] lemma value_of_unconstrainedNat :
    Value UnconstrainedNat F = Unit := rfl

@[circuit_norm] lemma eval_unconstrainedNat [FiniteField F]
    (env : Environment F) (v : Var UnconstrainedNat F) :
    eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrainedNat_prover [FiniteField F]
    (env : ProverEnvironment F) (v : Var UnconstrainedNat F) :
    eval env v = M.evalNat env v := by
  rw [CircuitType.eval_prover (M := UnconstrainedNat)]
  rfl

@[circuit_norm] lemma eval_unconstrainedNat_prover' [FiniteField F] :
  @eval (ProverEnvironment F) (M F (NExpr F)) ℕ (CircuitType.proverEval UnconstrainedNat)
    = M.evalNat := by
  with_unfolding_all rfl

@[circuit_norm]
def unconstrainedNat (program : Witgen.M F (Witgen.NExpr F)) : Var UnconstrainedNat F :=
  program
end UnconstrainedNat

export UnconstrainedNat (unconstrainedNat)
