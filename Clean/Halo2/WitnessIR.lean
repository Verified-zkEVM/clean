import Clean.Circuit.WitnessIR
import Clean.Circuit.WitnessIRSugar
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

/-- Prover-only Nat-sorted scalar input (a value the prover knows, entering witgen at
Nat sort — halo2's `Value<pallas::Scalar>`-style, e.g. a fixed-base mul scalar): the
`Var` view is a builder computation yielding a Nat-sorted witness expression, the
prover value is the number. -/
structure UnconstrainedNat (F : Type) where
  program : Witgen.MOver F (AssignedCell F) (NExpr F)

namespace UnconstrainedNat

@[reducible] instance : CircuitType UnconstrainedNat where
  Var F := Witgen.MOver F (AssignedCell F) (NExpr F)
  Value := unit
  ProverValue _ := ℕ
  evalVerifier _ _ := ()
  evalProver pe program := Witgen.MOver.evalNat pe program

instance : ProvableType (Halo2.Value UnconstrainedNat) :=
  (inferInstance : ProvableType unit)

@[circuit_norm] lemma var_of_unconstrainedNat {F : Type} :
    Halo2.Var UnconstrainedNat F = Witgen.MOver F (AssignedCell F) (NExpr F) := rfl
@[circuit_norm] lemma value_of_unconstrainedNat {F : Type} :
    Halo2.Value UnconstrainedNat F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedNat {F : Type} :
    Halo2.ProverValue UnconstrainedNat F = ℕ := rfl

instance {F : Type} : Inhabited (Var UnconstrainedNat F) :=
  ⟨(pure (.const 0) : Witgen.MOver F (AssignedCell F) (NExpr F))⟩

variable {F : Type} [FiniteField F]

@[reducible] instance : Eval (Placed Environment F)
    (Witgen.MOver F (AssignedCell F) (NExpr F)) Unit :=
  CircuitType.verifierEval UnconstrainedNat
@[reducible] instance : Eval (Placed ProverEnvironment F)
    (Witgen.MOver F (AssignedCell F) (NExpr F)) ℕ :=
  CircuitType.proverEval UnconstrainedNat

@[circuit_norm] lemma eval_unconstrainedNat
    (pe : Placed Environment F) (v : Var UnconstrainedNat F) :
    eval pe (v : Var UnconstrainedNat F) = () := rfl

@[circuit_norm] lemma eval_unconstrainedNat_prover
    (pe : Placed ProverEnvironment F) (v : Var UnconstrainedNat F) :
    eval pe v = Witgen.MOver.evalNat pe v := by
  with_unfolding_all rfl

@[circuit_norm] lemma eval_unconstrainedNat_prover' :
    @Eval.eval (Placed ProverEnvironment F)
        (Witgen.MOver F (AssignedCell F) (NExpr F)) ℕ
        (CircuitType.proverEval UnconstrainedNat)
      = Witgen.MOver.evalNat := by
  with_unfolding_all rfl

end UnconstrainedNat

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
theorem WitgenIROver.getElem_eval_ofFExprs {n : ℕ} (es : Vector (FExprOver F V) n) (env : Env)
    (i : ℕ) (hi : i < n) :
    ((WitgenIROver.ofFExprs es).eval env)[i] = es[i].eval { env } := by
  simp [WitgenIROver.ofFExprs, WitgenIROver.eval, VExprOver.eval, evalSteps]

end Witgen

