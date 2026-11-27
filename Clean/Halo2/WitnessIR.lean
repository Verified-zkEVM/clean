module

public import Clean.Circuit.WitnessIR
public import Clean.Circuit.WitnessIRSugar
public import Clean.Circuit.WitnessIRLimbs
public import Clean.Halo2.Provable

@[expose] public section

/-!
# Halo2 witness-generation IR

The shared witgen IR (`Clean/Circuit/WitnessIR.lean`), instantiated for halo2: variable
atoms are cell references, environments are placed prover environments. Witness
generation is thereby exportable for halo2 circuits exactly as for main Clean ones.

The main-Clean-specific atoms are inert here: `envRange` (no tape indices) and `dataGet`
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
  data _ := .empty F
  hint pe := pe.env.hint

/-- Halo2-instance witness reads normalize to the assigned-cell eval (the counterpart of
main Clean's `Clean.WitgenEnv.readVar_eq`), so witness-program reads meet the query and
assigned-cell eval paths on the same row form without a per-proof unfold. -/
@[circuit_norm]
lemma WitgenEnv.readVar_halo2 [Field F] (pe : Placed ProverEnvironment F)
    (c : AssignedCell F) :
    Witgen.WitgenEnv.readVar pe c = c.eval pe.place pe.env.toEnvironment := rfl

/-- Halo2 field-sorted witness expressions: variables are cell references. -/
abbrev FExpr (F : Type) := Witgen.FExprOver F (AssignedCell F)

instance [Field F] : Inhabited (FExpr F) := ⟨.const 0⟩
/-- Halo2 u64-sorted witness expressions. -/
abbrev U64Expr (F : Type) := Witgen.U64ExprOver F (AssignedCell F)
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
Because `Cell.row` treats `.instance` columns as absolute rows (ignoring region placement),
this is a structured `.ofFExpr (.expr …)` program rather than a `.native` closure, so
syntactic read checkers (`Fast.ordered*`) accept it at any placement. -/
def instanceGet (instCol : Column .instance) (instRow : ℕ) : WitgenIR F 1 :=
  .ofFExpr (.expr (.of 0 instRow instCol))

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

The `Var` view mirrors main Clean's `Unconstrained`: a `Witgen.MOver` builder
computation yielding per-component expressions. Assignment sites convert via
`Witgen.MOver.toIR`/`toIRLiteral`; embedding sites compose via monad `bind`.
-/

/-- Marker `TypeMap` for a prover-only input carrying a `value` as a witness program:
main Clean's `Unconstrained` design at the placed-cell variable atom. The `Var` view is
a `Witgen.MOver` builder computation yielding per-component expressions — a monad, so a
gadget embeds a hint's reading program inside its own witness programs via `bind`, and
shared intermediates use `letF`/`letN`. -/
structure Unconstrained (value : TypeMap) (F : Type) where
  program : Witgen.MOver F (AssignedCell F) (value (FExpr F))

namespace Unconstrained
variable {value : TypeMap} [ProvableType value]

@[reducible] instance : CircuitType (Unconstrained value) where
  Var F := Witgen.MOver F (AssignedCell F) (value (FExpr F))
  Value := unit
  ProverValue := value
  evalVerifier _ _ := ()
  evalProver pe program := Witgen.MOver.eval pe program

/-- Construct a prover-only input from a witness program. -/
@[circuit_norm]
def unconstrained (program : Witgen.MOver F (AssignedCell F) (value (FExpr F))) :
    Var (Unconstrained value) F :=
  program

-- note: these being in `circuit_norm` mean that we often have to target the
-- simplified way of writing the Var/Value/ProverValue types
@[circuit_norm] lemma var_of_unconstrained :
    Halo2.Var (Unconstrained value) F
      = Witgen.MOver F (AssignedCell F) (value (FExpr F)) := rfl
@[circuit_norm] lemma value_of_unconstrained :
    Halo2.Value (Unconstrained value) F = Unit := rfl

instance : ProvableType (Halo2.Value (Unconstrained value)) :=
  (inferInstance : ProvableType unit)
@[circuit_norm] lemma proverValue_of_unconstrained :
    Halo2.ProverValue (Unconstrained value) F = value F := rfl

instance [Field F] : Inhabited (Var (Unconstrained value) F) :=
  ⟨(pure (fromElements default) : Witgen.MOver F (AssignedCell F) (value (FExpr F)))⟩

variable [FiniteField F]

@[reducible] instance :
    Eval (Placed Environment F) (Witgen.MOver F (AssignedCell F) (value (FExpr F))) Unit :=
  CircuitType.verifierEval (Unconstrained value)
@[reducible] instance :
    Eval (Placed ProverEnvironment F) (Witgen.MOver F (AssignedCell F) (value (FExpr F)))
      (value F) :=
  CircuitType.proverEval (Unconstrained value)

@[circuit_norm] lemma eval_unconstrained
    (pe : Placed Environment F) (v : Var (Unconstrained value) F) :
    eval pe v = () := rfl

@[circuit_norm] lemma eval_unconstrained_prover
    (pe : Placed ProverEnvironment F) (v : Var (Unconstrained value) F) :
    eval pe v = Witgen.MOver.eval pe v := by
  with_unfolding_all rfl

/-- The same reduction keyed on the raw `CircuitType.proverEval` instance application, as
a function-level equation — the spelling the generic `eval env input_var = input`
hypotheses carry (keyed matching does not see through the named forwarder instance). -/
@[circuit_norm] lemma eval_unconstrained_prover' :
    @Eval.eval (Placed ProverEnvironment F)
        (Witgen.MOver F (AssignedCell F) (value (FExpr F))) (value F)
        (CircuitType.proverEval (Unconstrained value))
      = Witgen.MOver.eval := by
  with_unfolding_all rfl

end Unconstrained

export Unconstrained (unconstrained)

/-- Prover-only u64-sorted input (a value the prover knows, entering witgen at u64 sort):
the `Var` view is a builder computation yielding a u64-sorted witness expression, the
prover value is the number. -/
structure UnconstrainedU64 (F : Type) where
  program : Witgen.MOver F (AssignedCell F) (U64Expr F)

namespace UnconstrainedU64

@[reducible] instance : CircuitType UnconstrainedU64 where
  Var F := Witgen.MOver F (AssignedCell F) (U64Expr F)
  Value := unit
  ProverValue _ := UInt64
  evalVerifier _ _ := ()
  evalProver pe program := Witgen.MOver.evalU64 pe program

instance : ProvableType (Halo2.Value UnconstrainedU64) :=
  (inferInstance : ProvableType unit)

@[circuit_norm] lemma var_of_unconstrainedU64 {F : Type} :
    Halo2.Var UnconstrainedU64 F = Witgen.MOver F (AssignedCell F) (U64Expr F) := rfl
@[circuit_norm] lemma value_of_unconstrainedU64 {F : Type} :
    Halo2.Value UnconstrainedU64 F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedU64 {F : Type} :
    Halo2.ProverValue UnconstrainedU64 F = UInt64 := rfl

instance {F : Type} : Inhabited (Var UnconstrainedU64 F) :=
  ⟨(pure (.const 0) : Witgen.MOver F (AssignedCell F) (U64Expr F))⟩

variable {F : Type} [FiniteField F]

@[reducible] instance : Eval (Placed Environment F)
    (Witgen.MOver F (AssignedCell F) (U64Expr F)) Unit :=
  CircuitType.verifierEval UnconstrainedU64
@[reducible] instance : Eval (Placed ProverEnvironment F)
    (Witgen.MOver F (AssignedCell F) (U64Expr F)) UInt64 :=
  CircuitType.proverEval UnconstrainedU64

@[circuit_norm] lemma eval_unconstrainedU64
    (pe : Placed Environment F) (v : Var UnconstrainedU64 F) :
    eval pe (v : Var UnconstrainedU64 F) = () := rfl

@[circuit_norm] lemma eval_unconstrainedU64_prover
    (pe : Placed ProverEnvironment F) (v : Var UnconstrainedU64 F) :
    eval pe v = Witgen.MOver.evalU64 pe v := by
  with_unfolding_all rfl

@[circuit_norm] lemma eval_unconstrainedU64_prover' :
    @Eval.eval (Placed ProverEnvironment F)
        (Witgen.MOver F (AssignedCell F) (U64Expr F)) UInt64
        (CircuitType.proverEval UnconstrainedU64)
      = Witgen.MOver.evalU64 := by
  with_unfolding_all rfl

end UnconstrainedU64

/-- Prover-only wide unsigned input (a number the prover knows that does not fit in 64 bits,
such as a scalar-field trapdoor): the `Var` view is a builder computation yielding `n`
little-endian 64-bit limbs, the prover value is the number they represent. -/
structure UnconstrainedLimbs (n : ℕ) (F : Type) where
  program : Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n)

namespace UnconstrainedLimbs
variable {n : ℕ}

/-- The number a limb-valued builder computation evaluates to. -/
@[circuit_norm]
def evalProgram {F : Type} [FiniteField F] (pe : Placed ProverEnvironment F)
    (program : Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n)) : ℕ :=
  let (out, steps) := program #[]
  out.toNat { env := pe, locals := Witgen.evalSteps pe steps.toList }

@[reducible] instance : CircuitType (UnconstrainedLimbs n) where
  Var F := Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n)
  Value := unit
  ProverValue _ := ℕ
  evalVerifier _ _ := ()
  evalProver pe program := evalProgram pe program

instance : ProvableType (Halo2.Value (UnconstrainedLimbs n)) :=
  (inferInstance : ProvableType unit)

@[circuit_norm] lemma var_of_unconstrainedLimbs {F : Type} :
    Halo2.Var (UnconstrainedLimbs n) F
      = Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n) := rfl
@[circuit_norm] lemma value_of_unconstrainedLimbs {F : Type} :
    Halo2.Value (UnconstrainedLimbs n) F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedLimbs {F : Type} :
    Halo2.ProverValue (UnconstrainedLimbs n) F = ℕ := rfl

instance {F : Type} : Inhabited (Var (UnconstrainedLimbs n) F) :=
  ⟨(pure (Witgen.LimbsOver.const 0 n) :
    Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n))⟩

variable {F : Type} [FiniteField F]

@[reducible] instance : Eval (Placed Environment F)
    (Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n)) Unit :=
  CircuitType.verifierEval (UnconstrainedLimbs n)
@[reducible] instance : Eval (Placed ProverEnvironment F)
    (Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n)) ℕ :=
  CircuitType.proverEval (UnconstrainedLimbs n)

@[circuit_norm] lemma eval_unconstrainedLimbs
    (pe : Placed Environment F) (v : Var (UnconstrainedLimbs n) F) :
    eval pe (v : Var (UnconstrainedLimbs n) F) = () := rfl

@[circuit_norm] lemma eval_unconstrainedLimbs_prover
    (pe : Placed ProverEnvironment F) (v : Var (UnconstrainedLimbs n) F) :
    eval pe v = evalProgram pe v := by
  with_unfolding_all rfl

@[circuit_norm] lemma eval_unconstrainedLimbs_prover' :
    @Eval.eval (Placed ProverEnvironment F)
        (Witgen.MOver F (AssignedCell F) (Witgen.LimbsOver F (AssignedCell F) n)) ℕ
        (CircuitType.proverEval (UnconstrainedLimbs n))
      = evalProgram := by
  with_unfolding_all rfl

end UnconstrainedLimbs

/-- Prover-only Bool-sorted input: the `Var` view is a builder computation yielding a
witness condition, the prover value is the boolean. -/
structure UnconstrainedBool (F : Type) where
  program : Witgen.MOver F (AssignedCell F) (BExpr F)

namespace UnconstrainedBool

@[reducible] instance : CircuitType UnconstrainedBool where
  Var F := Witgen.MOver F (AssignedCell F) (BExpr F)
  Value := unit
  ProverValue _ := Bool
  evalVerifier _ _ := ()
  evalProver pe program := Witgen.MOver.evalBool pe program

instance : ProvableType (Halo2.Value UnconstrainedBool) :=
  (inferInstance : ProvableType unit)

@[circuit_norm] lemma var_of_unconstrainedBool {F : Type} :
    Halo2.Var UnconstrainedBool F = Witgen.MOver F (AssignedCell F) (BExpr F) := rfl
@[circuit_norm] lemma value_of_unconstrainedBool {F : Type} :
    Halo2.Value UnconstrainedBool F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedBool {F : Type} :
    Halo2.ProverValue UnconstrainedBool F = Bool := rfl

instance {F : Type} : Inhabited (Var UnconstrainedBool F) :=
  ⟨(pure .false : Witgen.MOver F (AssignedCell F) (BExpr F))⟩

variable {F : Type} [FiniteField F]

@[reducible] instance : Eval (Placed Environment F)
    (Witgen.MOver F (AssignedCell F) (BExpr F)) Unit :=
  CircuitType.verifierEval UnconstrainedBool
@[reducible] instance : Eval (Placed ProverEnvironment F)
    (Witgen.MOver F (AssignedCell F) (BExpr F)) Bool :=
  CircuitType.proverEval UnconstrainedBool

@[circuit_norm] lemma eval_unconstrainedBool
    (pe : Placed Environment F) (v : Var UnconstrainedBool F) :
    eval pe v = () := rfl

@[circuit_norm] lemma eval_unconstrainedBool_prover
    (pe : Placed ProverEnvironment F) (v : Var UnconstrainedBool F) :
    eval pe v = Witgen.MOver.evalBool pe v := by
  with_unfolding_all rfl

@[circuit_norm] lemma eval_unconstrainedBool_prover' :
    @Eval.eval (Placed ProverEnvironment F)
        (Witgen.MOver F (AssignedCell F) (BExpr F)) Bool
        (CircuitType.proverEval UnconstrainedBool)
      = Witgen.MOver.evalBool := by
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
theorem WitgenIROver.getElem_eval_ofCompositeFExpr {value : TypeMap} [ProvableType value]
    (e : value (FExprOver F V)) (env : Env) (i : ℕ) (hi : i < size value) :
    ((WitgenIROver.ofCompositeFExpr e).eval env)[i] = (toElements e)[i].eval { env } := by
  simp [WitgenIROver.ofCompositeFExpr, WitgenIROver.eval, VExprOver.eval, evalSteps]

end Witgen
