import Clean.Circuit.WitnessIR
import Clean.Halo2.Provable

/-!
# Halo2 witness-generation IR

The shared witgen IR (`Clean/Circuit/WitnessIR.lean`), instantiated for halo2: variable
atoms are cell references, environments are placed prover environments. Witness
generation is thereby exportable for halo2 circuits exactly as for main Clean ones.

The main-Clean-specific atoms are inert here: `envGet` (no tape indices) and `dataGet`
(no committed prover data — lookup tables are fixed columns) evaluate to junk and are
rejected by export well-formedness. `hintGet` works, reading the prover hints.
-/

namespace Halo2

variable {F : Type}

/-- Halo2's witness environment: variables are cell reads (which need the placement);
`get`/`data` are inert. -/
instance [Field F] : Witgen.WitgenEnv F (Placed ProverEnvironment F) (AssignedCell F) where
  readVar pe c := c.eval pe.place pe.env.toEnvironment
  get _ _ := 0
  data _ := fun _ _ => #[]
  hint pe := pe.env.hint

/-- Halo2-instance witness reads normalize to the assigned-cell eval (the counterpart of
main Clean's `WitgenEnv.readVar_main`), so witness-program reads meet the query and
assigned-cell eval paths on the same row form without a per-proof unfold. -/
@[circuit_norm]
lemma WitgenEnv.readVar_halo2 [Field F] (pe : Placed ProverEnvironment F)
    (c : AssignedCell F) :
    Witgen.WitgenEnv.readVar pe c = c.eval pe.place pe.env.toEnvironment := rfl

/-- Halo2 field-sorted witness expressions: variables are cell references. -/
abbrev FExpr (F : Type) := Witgen.FExprOver F (AssignedCell F)

instance [Field F] : Inhabited (FExpr F) := ⟨.const 0⟩
/-- Halo2 Nat-sorted witness expressions. -/
abbrev NExpr (F : Type) := Witgen.NExprOver F (AssignedCell F)
/-- Halo2 witness conditions. -/
abbrev BExpr (F : Type) := Witgen.BExprOver F (AssignedCell F)
/-- Halo2 witness-generation programs. -/
abbrev WitgenIR (F : Type) :=
  Witgen.WitgenIROver F (Placed ProverEnvironment F) (AssignedCell F)

/-- A single-scalar `ofFExpr` witness program evaluates to its expression. -/
@[circuit_norm]
lemma eval_ofFExpr_zero [FiniteField F] (e : FExpr F) (env : Placed ProverEnvironment F) :
    ((Witgen.WitgenIROver.ofFExpr e).eval env)[0] = Witgen.FExprOver.eval { env } e := by
  with_unfolding_all rfl

/-- Instance-read witness atom: a single-scalar witness program reading instance column
`instCol` at absolute row `instRow`. The witgen half of the `assign_advice_from_instance`
sugar (`Basic.lean`) — the paired `assignAdvice` witnesses the public input this program
returns, and the region's `constrainInstance` then copies the advice cell against it.
Instance columns are absolute, so this cannot be a cell atom (`.expr`); it reads the
placed prover environment directly via a `.native` closure. -/
def instanceGet (instCol : Column .instance) (instRow : ℕ) : WitgenIR F 1 :=
  .native fun pe => #v[pe.env.get instCol (instRow : ℤ)]

/-- The `instanceGet` witness reduces to the instance read `env.get instCol instRow` (which
`Environment.get_inst` further normalizes to `env.inst`), so a paired `assignAdvice`'s
`ExtendsWitness` equation lines up with the `constrainInstance` copy target. -/
@[circuit_norm]
lemma eval_instanceGet [FiniteField F] (instCol : Column .instance) (instRow : ℕ)
    (pe : Placed ProverEnvironment F) :
    ((instanceGet instCol instRow).eval pe)[0] = pe.env.get instCol (instRow : ℤ) := by
  with_unfolding_all rfl

/-!
## Prover-only inputs

`Unconstrained value` is a prover-only circuit input (halo2's `Value<T>`): the verifier
view is erased to `Unit`, the prover view is the evaluated `value F`, supplied by the
caller as witness IR for the honest prover to evaluate. Port of main Clean's
`Unconstrained`. Used for `Value<Affine>`-style inputs that the gadget witnesses
internally.

The `Var` view is one `WitgenIR F 1` program per component (`value (WitgenIR F 1)`),
so components carry full let-step witness programs and plug directly into the
per-cell witness ops. For `field` this is exactly `WitgenIR F 1` — what `loadPrivate`
and friends consume.

`UnconstrainedExpr value` is the plain-expression variant: its `Var` is
`value (FExpr F)`, for inputs a gadget *embeds inside* its own witness expressions
(e.g. the variable-base mul children's scalar-cell reading) rather than assigning to
cells.
-/

/-- Marker `TypeMap` for a prover-only input carrying a `value` as per-component
witness-IR programs. -/
structure Unconstrained (value : TypeMap) (F : Type) where
  program : value (WitgenIR F 1)

namespace Unconstrained
variable {value : TypeMap} [ProvableType value]

/-- Componentwise witness-program evaluation: the prover view of an `Unconstrained`
input (the engine's canonical spelling, produced by the eval-dispatch simproc below). -/
def evalIR {F : Type} [FiniteField F] {value : TypeMap} [ProvableType value]
    (pe : Placed ProverEnvironment F) (v : value (WitgenIR F 1)) : value F :=
  fromElements ((toElements v).map fun w => (w.eval pe)[0])

@[reducible] instance : CircuitType (Unconstrained value) where
  Var F := value (WitgenIR F 1)
  Value := unit
  ProverValue := value
  evalVerifier _ _ := ()
  evalProver pe program := evalIR pe program

/-- Construct a prover-only input from per-component witness programs. -/
@[circuit_norm]
def unconstrained (program : value (WitgenIR F 1)) : Var (Unconstrained value) F :=
  program

/-- Construct a prover-only input from plain per-component expressions. -/
@[circuit_norm]
def ofFExprs (program : value (FExpr F)) : Var (Unconstrained value) F :=
  (fromElements ((toElements program).map Witgen.WitgenIROver.ofFExpr)
    : value (WitgenIR F 1))

-- note: these being in `circuit_norm` mean that we often have to target the
-- simplified way of writing the Var/Value/ProverValue types
@[circuit_norm] lemma var_of_unconstrained :
    Halo2.Var (Unconstrained value) F = value (WitgenIR F 1) := rfl
@[circuit_norm] lemma value_of_unconstrained :
    Halo2.Value (Unconstrained value) F = Unit := rfl

instance : ProvableType (Halo2.Value (Unconstrained value)) :=
  (inferInstance : ProvableType unit)
@[circuit_norm] lemma proverValue_of_unconstrained :
    Halo2.ProverValue (Unconstrained value) F = value F := rfl

instance [Field F] : Inhabited (WitgenIR F 1) :=
  ⟨Witgen.WitgenIROver.ofFExpr default⟩

instance [Field F] : Inhabited (Var (Unconstrained value) F) :=
  ⟨(fromElements default : value (WitgenIR F 1))⟩

variable [FiniteField F]

@[reducible] instance : Eval (Placed Environment F) (value (WitgenIR F 1)) Unit :=
  CircuitType.verifierEval (Unconstrained value)
@[reducible] instance :
    Eval (Placed ProverEnvironment F) (value (WitgenIR F 1)) (value F) :=
  CircuitType.proverEval (Unconstrained value)

@[circuit_norm] lemma eval_unconstrained
    (pe : Placed Environment F) (v : value (WitgenIR F 1)) :
    eval pe v = () := rfl

@[circuit_norm] lemma eval_unconstrained_prover
    (pe : Placed ProverEnvironment F) (v : value (WitgenIR F 1)) :
    eval pe v
      = evalIR ({ place := pe.place, env := pe.env } : Placed ProverEnvironment F) v := by
  with_unfolding_all rfl

/-- The same reduction keyed on the raw `CircuitType.proverEval` instance application — the
spelling `completeness_iff`'s generic `eval env input_var = input` hypothesis carries (the
named forwarder instance above is a different constant, which keyed matching does not see
through). -/
@[circuit_norm] lemma eval_unconstrained_prover_raw
    (pe : Placed ProverEnvironment F) (v : value (WitgenIR F 1)) :
    @Eval.eval (Placed ProverEnvironment F) (value (WitgenIR F 1)) (value F)
        (CircuitType.proverEval (Unconstrained value)) pe v
      = evalIR ({ place := pe.place, env := pe.env } : Placed ProverEnvironment F) v := by
  with_unfolding_all rfl

/-- Scalar (`field`) reduction of the componentwise evaluator. -/
@[circuit_norm] lemma evalIR_field
    (pe : Placed ProverEnvironment F) (w : WitgenIR F 1) :
    evalIR (value := field) pe w = (w.eval pe)[0] := by
  with_unfolding_all rfl

end Unconstrained

export Unconstrained (unconstrained)

/-- Marker `TypeMap` for a prover-only input carried as plain per-component witness
*expressions* — for inputs a gadget embeds inside its own witness programs rather than
assigning to cells. -/
structure UnconstrainedExpr (value : TypeMap) (F : Type) where
  program : value (FExpr F)

namespace UnconstrainedExpr
variable {value : TypeMap} [ProvableType value]

@[reducible] instance : CircuitType (UnconstrainedExpr value) where
  Var F := value (FExpr F)
  Value := unit
  ProverValue := value
  evalVerifier _ _ := ()
  evalProver pe program := Witgen.eval { env := pe } program

instance : ProvableType (Halo2.Value (UnconstrainedExpr value)) :=
  (inferInstance : ProvableType unit)

@[circuit_norm] lemma var_of_unconstrainedExpr {F : Type} :
    Halo2.Var (UnconstrainedExpr value) F = value (FExpr F) := rfl
@[circuit_norm] lemma value_of_unconstrainedExpr {F : Type} :
    Halo2.Value (UnconstrainedExpr value) F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedExpr {F : Type} :
    Halo2.ProverValue (UnconstrainedExpr value) F = value F := rfl

instance {F : Type} [Field F] : Inhabited (Var (UnconstrainedExpr value) F) :=
  ⟨(fromElements default : value (FExpr F))⟩

variable {F : Type} [FiniteField F]

@[reducible] instance : Eval (Placed Environment F) (value (FExpr F)) Unit :=
  CircuitType.verifierEval (UnconstrainedExpr value)
@[reducible] instance : Eval (Placed ProverEnvironment F) (value (FExpr F)) (value F) :=
  CircuitType.proverEval (UnconstrainedExpr value)

@[circuit_norm] lemma eval_unconstrainedExpr
    (pe : Placed Environment F) (v : value (FExpr F)) :
    eval pe v = () := rfl

@[circuit_norm] lemma eval_unconstrainedExpr_prover
    (pe : Placed ProverEnvironment F) (v : value (FExpr F)) :
    eval pe v
      = Witgen.eval { env := ({ place := pe.place, env := pe.env } : Placed ProverEnvironment F) } v := by
  with_unfolding_all rfl

@[circuit_norm] lemma eval_unconstrainedExpr_prover_raw
    (pe : Placed ProverEnvironment F) (v : value (FExpr F)) :
    @Eval.eval (Placed ProverEnvironment F) (value (FExpr F)) (value F)
        (CircuitType.proverEval (UnconstrainedExpr value)) pe v
      = Witgen.eval { env := ({ place := pe.place, env := pe.env } : Placed ProverEnvironment F) } v := by
  with_unfolding_all rfl

end UnconstrainedExpr

/-- Prover-only Nat-sorted scalar input (a value the prover knows, entering witgen at
Nat sort — halo2's `Value<pallas::Scalar>`-style, e.g. a fixed-base mul scalar): the
`Var` view is a Nat-sorted witness expression, the prover value is the number. -/
structure UnconstrainedNat (F : Type) where
  program : NExpr F

namespace UnconstrainedNat

@[reducible] instance : CircuitType UnconstrainedNat where
  Var F := NExpr F
  Value := unit
  ProverValue _ := ℕ
  evalVerifier _ _ := ()
  evalProver pe e := e.eval { env := pe }

instance : ProvableType (Halo2.Value UnconstrainedNat) :=
  (inferInstance : ProvableType unit)

@[circuit_norm] lemma var_of_unconstrainedNat {F : Type} :
    Halo2.Var UnconstrainedNat F = NExpr F := rfl
@[circuit_norm] lemma value_of_unconstrainedNat {F : Type} :
    Halo2.Value UnconstrainedNat F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedNat {F : Type} :
    Halo2.ProverValue UnconstrainedNat F = ℕ := rfl

instance {F : Type} : Inhabited (Var UnconstrainedNat F) := ⟨.const 0⟩

variable {F : Type} [FiniteField F]

@[reducible] instance : Eval (Placed Environment F) (NExpr F) Unit :=
  CircuitType.verifierEval UnconstrainedNat
@[reducible] instance : Eval (Placed ProverEnvironment F) (NExpr F) ℕ :=
  CircuitType.proverEval UnconstrainedNat

@[circuit_norm] lemma eval_unconstrainedNat
    (pe : Placed Environment F) (e : NExpr F) :
    eval pe (e : Var UnconstrainedNat F) = () := rfl

@[circuit_norm] lemma eval_unconstrainedNat_prover_raw
    (pe : Placed ProverEnvironment F) (e : NExpr F) :
    @Eval.eval (Placed ProverEnvironment F) (NExpr F) ℕ
        (CircuitType.proverEval UnconstrainedNat) pe e
      = e.eval { env := ({ place := pe.place, env := pe.env }
          : Placed ProverEnvironment F) } := by
  with_unfolding_all rfl

end UnconstrainedNat

/-- Prover-only Bool-sorted input (halo2's `Value<bool>`-style, e.g. a swap flag): the
`Var` view is a Bool-sorted witness expression, the prover value is the `Bool`. -/
structure UnconstrainedBool (F : Type) where
  program : BExpr F

namespace UnconstrainedBool

@[reducible] instance : CircuitType UnconstrainedBool where
  Var F := BExpr F
  Value := unit
  ProverValue _ := Bool
  evalVerifier _ _ := ()
  evalProver pe e := e.eval { env := pe }

instance : ProvableType (Halo2.Value UnconstrainedBool) :=
  (inferInstance : ProvableType unit)

@[circuit_norm] lemma var_of_unconstrainedBool {F : Type} :
    Halo2.Var UnconstrainedBool F = BExpr F := rfl
@[circuit_norm] lemma value_of_unconstrainedBool {F : Type} :
    Halo2.Value UnconstrainedBool F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedBool {F : Type} :
    Halo2.ProverValue UnconstrainedBool F = Bool := rfl

instance {F : Type} : Inhabited (Var UnconstrainedBool F) := ⟨.false⟩

variable {F : Type} [FiniteField F]

@[reducible] instance : Eval (Placed Environment F) (BExpr F) Unit :=
  CircuitType.verifierEval UnconstrainedBool
@[reducible] instance : Eval (Placed ProverEnvironment F) (BExpr F) Bool :=
  CircuitType.proverEval UnconstrainedBool

@[circuit_norm] lemma eval_unconstrainedBool
    (pe : Placed Environment F) (e : BExpr F) :
    eval pe (e : Var UnconstrainedBool F) = () := rfl

@[circuit_norm] lemma eval_unconstrainedBool_prover_raw
    (pe : Placed ProverEnvironment F) (e : BExpr F) :
    @Eval.eval (Placed ProverEnvironment F) (BExpr F) Bool
        (CircuitType.proverEval UnconstrainedBool) pe e
      = e.eval { env := ({ place := pe.place, env := pe.env }
          : Placed ProverEnvironment F) } := by
  with_unfolding_all rfl

end UnconstrainedBool

end Halo2

/-! ## Honest-witness IR reduction over an arbitrary `WitgenEnv`

The shared getElem-keyed eval lemmas (`Clean/Circuit/WitnessIR.lean`) are stated at main Clean's
instantiation (`ProverEnvironment F`, `Expression F`), so they do not fire on halo2's
(`Placed ProverEnvironment F`, `AssignedCell F`). These restate the same reductions over the
abstract `WitgenEnv F Env V`, so honest witness IR reduces through `circuit_norm` — and no gadget
proof names the raw `WitgenIROver.eval`/`VExprOver.eval`/`ofFExpr` recursors. Getelem-keyed (`↓`),
matching main Clean's, to keep the opaque-until-consumed lazy-vector discipline (the raw recursors
stay untagged). -/

namespace Witgen

variable {F Env V : Type} [FiniteField F] [WitgenEnv F Env V]

@[circuit_norm]
theorem WitgenIROver.eval_native_apply {m : ℕ} (f : Env → Vector F m) (env : Env) :
    (WitgenIROver.native f : WitgenIROver F Env V m).eval env = f env := rfl

@[circuit_norm ↓]
theorem VExprOver.getElem_eval_mapRange (ctx : CtxOver F Env) (n : ℕ) (body : FExprOver F V)
    (i : ℕ) (hi : i < n) :
    (VExprOver.eval ctx (.mapRange n body))[i] = body.eval { ctx with idx := i } := by
  simp [VExprOver.eval, Vector.getElem_mapRange]

@[circuit_norm ↓]
theorem VExprOver.getElem_eval_lit {n : ℕ} (ctx : CtxOver F Env) (es : Vector (FExprOver F V) n)
    (i : ℕ) (hi : i < n) :
    (VExprOver.eval ctx (.lit es))[i] = es[i].eval ctx := by
  simp [VExprOver.eval]

@[circuit_norm ↓]
theorem WitgenIROver.getElem_eval_ir {n : ℕ} (steps : List (StepOver F V)) (out : VExprOver F V n)
    (env : Env) (i : ℕ) (hi : i < n) :
    ((WitgenIROver.ir steps out).eval env)[i]
      = (out.eval { env := env, locals := evalSteps env steps })[i] := rfl

@[circuit_norm ↓]
theorem WitgenIROver.getElem_eval_ofFExpr (e : FExprOver F V) (env : Env) (i : ℕ) (hi : i < 1) :
    ((WitgenIROver.ofFExpr e).eval env)[i] = e.eval { env } := by
  rcases Nat.lt_one_iff.mp hi
  simp [WitgenIROver.ofFExpr, WitgenIROver.eval, VExprOver.eval, evalSteps]

@[circuit_norm ↓]
theorem WitgenIROver.getElem_eval_ofFExprs {n : ℕ} (es : Vector (FExprOver F V) n) (env : Env)
    (i : ℕ) (hi : i < n) :
    ((WitgenIROver.ofFExprs es).eval env)[i] = es[i].eval { env } := by
  simp [WitgenIROver.ofFExprs, WitgenIROver.eval, VExprOver.eval, evalSteps]

end Witgen

/-! ## Hint-input evaluation dispatch

The `_iff` statements evaluate an `Unconstrained` input generically (`eval env input_var`),
with the `Eval` instance arriving in several spellings (the named forwarder above, the raw
`CircuitType.proverEval` application). Keyed lemma matching does not see through those, so
a simproc dispatches on the whnf'd instance and reduces: prover view to the witness-program
evaluation in the engine's canonical spelling (`Witgen.eval { env := ⟨pe.place, pe.env⟩ } v`
— the reconstructed-`Placed` form the witness closures receive), verifier view to `()`. -/

open Lean Meta Simp in
def Halo2.unconstrainedEvalProc : Simproc := fun e => do
  unless e.isAppOfArity ``Eval.eval 6 do return .continue
  let args := e.getAppArgs
  let inst := args[3]!
  let pe := args[4]!
  let v := args[5]!
  -- unfold the instance just far enough to expose the verifier/prover dispatch head (a
  -- plain whnf would reduce past it, to the `Eval.mk` structure literal)
  let (instW, isProver) ← withTransparency .default do
    if let some x ← whnfUntil inst ``Halo2.CircuitType.proverEval then
      pure (some x, true)
    else if let some x ← whnfUntil inst ``Halo2.CircuitType.verifierEval then
      pure (some x, false)
    else
      pure (none, false)
  let some instW := instW | return .continue
  let isVerifier := !isProver
  let some m := instW.getAppArgs[2]? | return .continue
  let isIRCarrier := m.getAppFn.isConstOf ``Halo2.Unconstrained
  let isExprCarrier := m.getAppFn.isConstOf ``Halo2.UnconstrainedExpr
  let isNatCarrier := m.getAppFn.isConstOf ``Halo2.UnconstrainedNat
  let isBoolCarrier := m.getAppFn.isConstOf ``Halo2.UnconstrainedBool
  unless isIRCarrier || isExprCarrier || isNatCarrier || isBoolCarrier do
    return .continue
  if isVerifier then
    let rhs := mkConst ``Unit.unit
    let pf ← withTransparency .all <| mkExpectedTypeHint (← mkEqRefl e) (← mkEq e rhs)
    return .visit { expr := rhs, proof? := some pf }
  let pePlace ← mkAppM ``Halo2.Placed.place #[pe]
  let peEnv ← mkAppM ``Halo2.Placed.env #[pe]
  let pe' ← mkAppM ``Halo2.Placed.mk #[pePlace, peEnv]
  let fF := (← withTransparency .default (whnf (← inferType pe'))).getAppArgs[1]!
  let sumTy ← mkAppM ``Sum #[fF, mkConst ``Nat]
  let locals ← mkAppOptM ``List.toArray
    #[some sumTy, some (← mkAppOptM ``List.nil #[some sumTy])]
  let ctx ← withTransparency .default <| mkAppM ``Witgen.CtxOver.mk #[pe', locals, mkNatLit 0]
  let rhs ← withTransparency .default <|
    if isNatCarrier then
      mkAppM ``Witgen.NExprOver.eval #[ctx, v]
    else if isBoolCarrier then
      mkAppM ``Witgen.BExprOver.eval #[ctx, v]
    else if isIRCarrier then do
      -- `M := value` must be supplied explicitly: higher-order unification cannot
      -- recover it from the folded `Var (Unconstrained value) F` type of `v`
      let some value := m.getAppArgs[0]? | failure
      mkAppOptM ``Halo2.Unconstrained.evalIR #[none, none, some value, none, some pe', some v]
    else do
      let some value := m.getAppArgs[0]? | failure
      mkAppOptM ``Witgen.eval #[none, none, none, none, none, some value, none, some ctx, some v]
  let pf ← withTransparency .all <| mkExpectedTypeHint (← mkEqRefl e) (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some pf }

open Lean Meta Elab in
run_cmd Command.liftTermElabM do
  let f ← mkConstWithFreshMVarLevels ``Eval.eval
  let (mvars, _, _) ← forallMetaTelescope (← inferType f)
  let keys ← withSimpGlobalConfig <| DiscrTree.mkPath (mkAppN f mvars)
  Simp.registerSimproc ``Halo2.unconstrainedEvalProc keys

attribute [circuit_norm] Halo2.unconstrainedEvalProc
