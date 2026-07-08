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

/-!
## Prover-only inputs

`Unconstrained value` is a prover-only circuit input (halo2's `Value<T>`): the verifier
view is erased to `Unit`, the prover view is a witness program producing `value F`,
supplied by the caller for the honest prover to evaluate. Port of main Clean's
`Unconstrained`. Used for `Value<Affine>`-style inputs that the gadget witnesses
internally.

Minimal version: the program is a plain `value (FExpr F)` (a provable value of witness
expressions). The `let`-step builder monad (`Witgen.M`, for shared intermediate values)
is not yet ported — a follow-up when complex witness programs land; for a `Value<Affine>`
input the plain form suffices.
-/

/-- Marker `TypeMap` for a prover-only input carrying a `value`. -/
structure Unconstrained (value : TypeMap) (F : Type) where
  program : value (FExpr F)

namespace Unconstrained
variable {value : TypeMap} [ProvableType value]

@[reducible] instance : CircuitType (Unconstrained value) where
  Var F := value (FExpr F)
  Value := unit
  ProverValue := value
  evalVerifier _ _ := ()
  evalProver pe program := Witgen.eval { env := pe } program

@[circuit_norm] lemma var_of_unconstrained :
    Halo2.Var (Unconstrained value) F = value (FExpr F) := rfl
@[circuit_norm] lemma value_of_unconstrained :
    Halo2.Value (Unconstrained value) F = Unit := rfl
@[circuit_norm] lemma proverValue_of_unconstrained :
    Halo2.ProverValue (Unconstrained value) F = value F := rfl

instance [Field F] : Inhabited (Var (Unconstrained value) F) :=
  ⟨(fromElements default : value (FExpr F))⟩

@[circuit_norm] lemma eval_unconstrained [FiniteField F]
    (pe : Placed Environment F) (v : Var (Unconstrained value) F) :
    eval pe v = () := rfl

@[circuit_norm] lemma eval_unconstrained_prover [FiniteField F]
    (pe : Placed ProverEnvironment F) (v : Var (Unconstrained value) F) :
    eval pe v = Witgen.eval { env := pe } v := by with_unfolding_all rfl

/-- Construct a prover-only input from its witness program. -/
@[circuit_norm]
def unconstrained (program : value (FExpr F)) : Var (Unconstrained value) F := program

end Unconstrained

export Unconstrained (unconstrained)

end Halo2
