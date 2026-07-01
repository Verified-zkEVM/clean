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
- a builder monad `Witgen.M` with `letF`/`letN` for shared intermediate values,
  assembled by `WitgenIR.build`.

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
instance {n : ℕ} [OfNat F n] : OfNat (FExpr F) n := ⟨.const (OfNat.ofNat n)⟩
instance : Add (FExpr F) := ⟨.add⟩
instance : Mul (FExpr F) := ⟨.mul⟩
instance : Inv (FExpr F) := ⟨.inv⟩
instance : Inv (field (Witgen.FExpr F)) := inferInstanceAs (Inv (Witgen.FExpr F))
instance [Field F] : Neg (FExpr F) := ⟨.neg⟩
instance [Field F] : Sub (FExpr F) := ⟨.sub⟩

instance : Coe ℕ (NExpr F) := ⟨.const⟩
instance {n : ℕ} : OfNat (NExpr F) n := ⟨.const n⟩
instance : Inhabited (NExpr F) where
  default := .const 0
instance : Add (NExpr F) := ⟨.add⟩
instance : Mul (NExpr F) := ⟨.mul⟩
instance : Div (NExpr F) := ⟨.div⟩
instance : HDiv (NExpr F) ℕ (NExpr F) where
  hDiv n m := .div n m
instance : Mod (NExpr F) := ⟨.mod⟩
instance : HMod (NExpr F) ℕ (NExpr F) where
  hMod n m := .mod n m
instance : AndOp (NExpr F) := ⟨.land⟩
instance : OrOp (NExpr F) := ⟨.lor⟩
instance : XorOp (NExpr F) := ⟨.lxor⟩
instance : ShiftLeft (NExpr F) := ⟨.shiftL⟩
instance : ShiftRight (NExpr F) := ⟨.shiftR⟩
instance : HShiftLeft (NExpr F) ℕ (NExpr F) where
  hShiftLeft n m := .shiftL n m
instance : HShiftRight (NExpr F) ℕ (NExpr F) where
  hShiftRight n m := .shiftR n m

/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩

/-! ## Bridges as dot notation -/

/-- The `ℕ` value of an IR field expression: `e.val`. -/
abbrev FExpr.val (e : FExpr F) : NExpr F := .val e

/-- The `ℕ` value of a circuit expression, as a witness-IR expression: `x.val`. -/
abbrev _root_.Expression.val (e : Expression F) : NExpr F := .val (.expr e)

/-- Cast a Nat-sorted IR expression back into the field (via `FiniteField.fromNat`). -/
abbrev NExpr.toField (n : NExpr F) : FExpr F := .ofNat n

/-- Cast a boolean expression to a field element that is 0 or 1. -/
abbrev BExpr.toField [Field F] (b : BExpr F) : FExpr F := .ite b 1 0

/-! ## Conditions -/

@[inherit_doc BExpr.feq] infix:50 " =? " => BExpr.feq
@[inherit_doc BExpr.neq] infix:50 " =? " => BExpr.neq
@[inherit_doc BExpr.lt] infix:50 " <? " => BExpr.lt

instance : Inhabited (BExpr F) := ⟨.false⟩
instance : AndOp (BExpr F) := ⟨.and⟩

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

@[circuit_norm]
def toIR (program : M F (value (FExpr F))) : WitgenIR F (size value) :=
  let built := program #[]
  .ir built.2.toList (.lit (toElements built.1))

theorem eval_toIR (program : M F (value (FExpr F))) (env : ProverEnvironment F) :
    program.toIR.eval env = toElements (program.eval env) := by
  simp [toIR, eval, WitgenIR.eval, Witgen.eval, ProvableType.toElements_fromElements, VExpr.eval]

instance {α : Type} [Inhabited α] : Inhabited (M F α) where
  default := pure default
end M

/-- Assemble a witness program from a builder computation returning the output vector. -/
def WitgenIR.build {n : ℕ} (m : M F (VExpr F n)) : WitgenIR F n :=
  .ir (m #[]).2.toList (m #[]).1

@[circuit_norm]
theorem WitgenIR.build_def {n : ℕ} (m : M F (VExpr F n)) :
    WitgenIR.build m = .ir (m #[]).2.toList (m #[]).1 := rfl

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

instance : CircuitType (Unconstrained value) where
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

instance : CircuitType UnconstrainedBool where
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

instance : CircuitType UnconstrainedNat where
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
