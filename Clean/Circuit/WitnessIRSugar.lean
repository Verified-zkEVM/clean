import Clean.Circuit.WitnessIR

open Clean

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

end Witgen

namespace Clean

/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩

/-- The `ℕ` value of a circuit expression, as a witness-IR expression: `x.val`. -/
abbrev Expression.val (e : Expression F) : NExpr F := .val (.expr e)

end Clean

namespace Witgen

/-! ## Bridges as dot notation -/

/-- The `ℕ` value of an IR field expression: `e.val`. -/
abbrev FExprOver.val {V : Type} (e : FExprOver F V) : NExprOver F V := .val e

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
instance {V : Type} : EqCond (FExprOver F V) F F V where eqCond x y := .feq x (.const y)
instance {V : Type} : EqCond F (FExprOver F V) F V where eqCond x y := .feq (.const x) y
instance {V : Type} [NatCast F] : EqCond (FExprOver F V) ℕ F V where
  eqCond x n := .feq x (.const (n : F))
instance {V : Type} [NatCast F] : EqCond ℕ (FExprOver F V) F V where
  eqCond n x := .feq (.const (n : F)) x
instance {V : Type} : EqCond (NExprOver F V) (NExprOver F V) F V := ⟨.neq⟩
instance {V : Type} : EqCond (NExprOver F V) ℕ F V where eqCond x n := .neq x (.const n)
instance {V : Type} : EqCond ℕ (NExprOver F V) F V where eqCond n x := .neq (.const n) x

@[inherit_doc BExprOver.lt] infix:50 " <? " => BExprOver.lt

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
  | cons hd tl ih => cases i <;> simp_all [FExprOver.evalList, FExprOver.eval, WitgenEnv.readVar_eq]

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

end Clean

namespace Witgen

/-! ## Builder monad for stepped programs -/

/-- Witness-program builder, generic over the variable atom `V`: accumulates
`let`-steps, so shared values are written in `do`-notation via `letF` / `letN`.
Main Clean's `M` instantiates `V := Expression F`; Halo2-Clean instantiates
`V := AssignedCell F`. -/
def MOver (F V : Type) (α : Type) : Type :=
  Array (StepOver F V) → α × Array (StepOver F V)

/-- Main Clean's witness-program builder (variables are circuit `Expression`s). -/
abbrev M (F : Type) : Type → Type := MOver F (Expression F)

instance {V : Type} : Monad (MOver F V) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'
  map f m := fun s => let (a, s') := m s; (f a, s')

attribute [circuit_norm] Array.size_empty Array.getElem?_push

theorem M.pure_def {V : Type} (a : α) :
    (pure a : MOver F V α) = fun s => (a, s) := rfl

theorem M.bind_def {V : Type} (m : MOver F V α) (f : α → MOver F V β) :
    (m >>= f) = fun s => let (a, s') := m s; f a s' := rfl

theorem M.map_def {V : Type} (f : α → β) (m : MOver F V α) :
    (f <$> m) = fun s => let (a, s') := m s; (f a, s') := rfl

/-- Bind a Nat-sorted value as a shared step; returns a reference to it. -/
def letN {V : Type} (e : NExprOver F V) : MOver F V (NExprOver F V) :=
  fun s => (.localVar s.size, s.push (.letN e))

instance {V : Type} : CoeOut (NExprOver F V) (MOver F V (NExprOver F V)) := ⟨letN⟩

theorem letN_def {V : Type} (e : NExprOver F V) :
    letN e = fun s => (.localVar s.size, s.push (.letN e)) := rfl

/-- Bind a field-sorted value as a shared step; returns a reference to it. -/
def letF {V : Type} (e : FExprOver F V) : MOver F V (FExprOver F V) :=
  fun s => (.localVar s.size, s.push (.letF e))

instance {V : Type} : CoeOut (FExprOver F V) (MOver F V (FExprOver F V)) := ⟨letF⟩

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

def eval (env : Env) (program : MOver F V (value (FExprOver F V))) : value F :=
  let (out, steps) := program #[]
  Witgen.eval { env, locals := evalSteps env steps.toList } out

def evalBool (env : Env) (program : MOver F V (BExprOver F V)) : Bool :=
  let (out, steps) := program #[]
  out.eval { env, locals := evalSteps env steps.toList }

def evalNat (env : Env) (program : MOver F V (NExprOver F V)) : ℕ :=
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
  simp [toIRScalar, toIR, eval, WitgenIROver.eval, h, VExprOver.eval]
  with_unfolding_all rfl

instance {α : Type} [Inhabited α] : Inhabited (MOver F V α) where
  default := pure default

end MOver

section EvalMapProj
open Lean Meta Simp

/-- `MOver.eval env (Point.x <$> p)  ~~>  (MOver.eval env p).x` — a projected hint
program evaluates to the projection of the whole program's evaluation, so projected
programs stay compositions of the WHOLE program's `MOver.eval` atom and meet the
row-level `h_input` facts. A simproc because a lemma cannot quantify over an arbitrary
structure projection; validated by `.all`-transparency defeq (the kernel re-checks). -/
private def evalMapProjSimproc (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Witgen.MOver.eval && args.size >= 2 do
    return .continue
  let env := args[args.size - 2]!
  let prog ← instantiateMVars args[args.size - 1]!
  -- view `prog` as `f <$> p`
  unless prog.getAppFn.isConstOf ``Functor.map do return .continue
  let pargs := prog.getAppArgs
  unless pargs.size ≥ 2 do return .continue
  let f ← instantiateMVars pargs[pargs.size - 2]!
  let p := pargs[pargs.size - 1]!
  -- view `f` as a structure projection: the projection constant (possibly η-expanded)
  let fromApp : Expr → MetaM (Option Name) := fun body => do
    let .const pn _ := body.getAppFn | pure none
    let some pinfo ← getProjectionFnInfo? pn | pure none
    let bargs := body.getAppArgs
    if bargs.size == pinfo.numParams + 1 && bargs.back? == some (.bvar 0) then
      pure (some pn)
    else pure none
  let projName? : Option Name ←
    match f with
    | .lam _ _ body _ =>
      match body with
      | .proj sName idx (.bvar 0) => do
        let genv ← getEnv
        let fields := getStructureFields genv sName
        if h : idx < fields.size then
          pure (some (sName ++ fields[idx]))
        else pure none
      | _ => fromApp body
    | _ => fromApp (mkApp f (.bvar 0))
  let some projName := projName? | return .continue
  -- the parent value TypeMap, read off the `Functor.map` application's source type
  -- `α = Ty (FExprOver F V)` (the program's own type may arrive view-spelled)
  unless pargs.size ≥ 4 do return .continue
  let tyArg ← instantiateMVars pargs[pargs.size - 4]!
  let parent := tyArg.getAppFn
  unless parent.isConst do return .continue
  try
    let evalWhole ← withTransparency .all <| mkAppOptM ``Witgen.MOver.eval
      #[none, none, some parent, none, none, none, none, some env, some p]
    let rhs ← mkProjection evalWhole (Name.mkSimple projName.getString!)
    if ← withTransparency .all (isDefEq e rhs) then
      return .done { expr := rhs, proof? := none }
    return .continue
  catch _ => return .continue

simproc evalMapProj (Witgen.MOver.eval _ _) := evalMapProjSimproc
attribute [circuit_norm] evalMapProj

end EvalMapProj

namespace MOver
end MOver

-- Main Clean spellings (`Witgen.M.eval` &c.) — aliases into the `V`-generic
-- `MOver` namespace, so existing call sites keep working.
namespace M
export MOver (eval evalBool evalNat eval_pure toIR toIRScalar toIRLiteral eval_toIRLiteral)
end M
end Witgen

namespace Clean

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

/-- IR-backed prover-only Nat input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedNat (F : Type) where
  program : Witgen.M F (NExpr F)

namespace UnconstrainedNat
open Witgen

@[reducible] instance : CircuitType UnconstrainedNat where
  Var F := M F (NExpr F)
  ProverValue _ := ℕ
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := Witgen.MOver.evalNat env program

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

end UnconstrainedNat

@[circuit_norm]
def unconstrainedNat (program : Witgen.M F (NExpr F)) : Var UnconstrainedNat F :=
  program

end Clean
