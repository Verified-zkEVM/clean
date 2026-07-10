import Clean.Circuit.Provable
import Clean.Halo2.Expression

/-!
# Provable types over halo2 cells

Halo2 counterpart of the evaluation layer of `Clean/Circuit/Provable.lean`.

The `ProvableType` class itself — `size`/`toElements`/`fromElements`, all its instances
(`field`, `fields n`, `ProvablePair`, `ProvableVector`, …) and the `ProvableStruct`
deriving machinery — is fully generic over the element type and is **shared** with main
Clean, not ported. Likewise, the `CircuitTypeOver` machinery (and with it the
`Unconstrained*Native` hint types) is generic over the environment pair; halo2
instantiates it at `Placed Environment`/`Placed ProverEnvironment`, so circuit inputs
can mix cell references with prover hints exactly as in main Clean.

This file only supplies what is element-specific:

- `Halo2.Var M F` is `M (AssignedCell F)` for provable `M` (main Clean:
  `M (Expression F)`): structured circuit values are structs of cell references, halo2's
  composition currency (Rust gadgets do the same: `EccPoint` is a struct of
  `AssignedCell`s).
- `ProvableType.eval place env` evaluates them to values `M F`, given the region
  placement.

Deliberately absent, with no halo2 analogue:

- `const : M F → M (Expression F)` — there are no constant-valued variables; constants
  enter circuits through `assignAdviceFromConstant`/`constrainConstant`, i.e. as real
  cells copy-constrained to fixed cells.
- `varFromOffset` — cells are not allocated in blocks from a linear tape; each cell is
  created by an assignment operation at a specific (region, column, row offset).
-/

namespace Halo2

variable {F : Type} [FiniteField F] {M : TypeMap} [ProvableType M]

instance : Inhabited Cell where
  default := ⟨0, 0, ⟨.advice, 0⟩⟩

instance : Inhabited (AssignedCell F) where
  default := ⟨default⟩

instance (priority := low) : Inhabited (M (AssignedCell F)) where
  default := fromElements default

/--
Pair a region placement with an environment. This is the environment form used by
halo2's typed evaluation interface (`CircuitTypeOver`): evaluating a cell reference
needs both the cell assignment and the placement of regions.

In the circuit semantics themselves, `place` remains a separate parameter (the analogue
of main Clean's `offset`) — `Placed` is plumbing for the `Eval`/`CircuitTypeOver`
typeclasses, which take a single environment type.
-/
structure Placed (E : Type → Type) (F : Type) where
  place : RegionIndex → ℕ
  env : E F

/-- Halo2's `CircuitType`: `CircuitTypeOver` at the placed cell environments. -/
abbrev CircuitType (M : TypeMap) :=
  CircuitTypeOver (Placed Environment) (Placed ProverEnvironment) M

/- Halo2-specialized views of the bundled types, mirroring main Clean's
`Var`/`Value`/`ProverValue`. -/
@[reducible] def Var (M : TypeMap) [CircuitType M] : TypeMap :=
  CircuitTypeOver.Var (Env := Placed Environment) (PEnv := Placed ProverEnvironment) (M := M)
@[reducible] def Value (M : TypeMap) [CircuitType M] : TypeMap :=
  CircuitTypeOver.Value (Env := Placed Environment) (PEnv := Placed ProverEnvironment) (M := M)
@[reducible] def ProverValue (M : TypeMap) [CircuitType M] : TypeMap :=
  CircuitTypeOver.ProverValue (Env := Placed Environment) (PEnv := Placed ProverEnvironment) (M := M)

namespace CircuitType

/-- Verifier-view evaluation of a halo2 circuit variable, given a placement + env. -/
instance verifierEval M [CircuitType M] : Eval (Placed Environment F) (Var M F) (Value M F) where
  eval := CircuitType.evalVerifier

/-- Prover-view evaluation (hints visible). -/
instance proverEval M [CircuitType M] : Eval (Placed ProverEnvironment F) (Var M F) (ProverValue M F) where
  eval := CircuitType.evalProver

end CircuitType

namespace ProvableType

/--
Evaluate a structured variable in the given environment: every cell reference is read
from its column at its region's placement plus its row offset.

`place` is the region-placement parameter of the semantics (the analogue of main Clean's
`offset`); proofs are generic over it, the top level instantiates the floor planner's
output.

Note: like main Clean's `ProvableType.eval`, this is not tagged with `circuit_norm`, to
enable higher-level `ProvableStruct` decompositions.
-/
@[explicit_provable_type]
def eval (place : RegionIndex → ℕ) (env : Environment F) (x : M (AssignedCell F)) : M F :=
  let cells := toElements x
  let values := cells.map (AssignedCell.eval place env)
  fromElements values

/--
`ProvableType`s are halo2 `CircuitType`s: verifier- and prover-value coincide with the
input type, and `Var` is `M (AssignedCell ·)`. Halo2 counterpart of main Clean's
`ProvableType.toCircuitType`.
-/
@[reducible] instance toCircuitType {M : TypeMap} [ProvableType M] : CircuitType M where
  Var F := M (AssignedCell F)
  Value := M
  ProverValue := M
  evalVerifier pe v := ProvableType.eval pe.place pe.env v
  evalProver pe v := ProvableType.eval pe.place pe.env.toEnvironment v

/- Normalize `Var`/`Value`/`ProverValue` of a provable type to their concrete forms, so
the *concrete* form is the single simp normal form (matching main Clean, and symmetric
with `Unconstrained`'s `var_of_unconstrained`). Without these, `Var M` stays abstract in
goals while `Unconstrained` reduces — the eval-lemma normal-form asymmetry. -/
@[circuit_norm] lemma var_of_provableType (F) : Var M F = M (AssignedCell F) := rfl
@[circuit_norm] lemma value_of_provableType (F) : Value M F = M F := rfl
@[circuit_norm] lemma proverValue_of_provableType (F) : ProverValue M F = M F := rfl

instance : Eval (Placed Environment F) (AssignedCell F) F := CircuitType.verifierEval field
instance : Eval (Placed ProverEnvironment F) (AssignedCell F) F := CircuitType.proverEval field
instance : Eval (Placed Environment F) (M (AssignedCell F)) (M F) := CircuitType.verifierEval M
instance : Eval (Placed ProverEnvironment F) (M (AssignedCell F)) (M F) := CircuitType.proverEval M

/-- Evaluating a single-cell variable reads that cell. -/
@[circuit_norm]
lemma eval_field (env : Placed Environment F) (x : AssignedCell F) :
    Eval.eval env x = AssignedCell.eval env.place env.env x := by
  with_unfolding_all rfl

/-- Prover-view single-cell evaluation. -/
@[circuit_norm]
lemma eval_field_prover (env : Placed ProverEnvironment F) (x : AssignedCell F) :
    Eval.eval env x = AssignedCell.eval env.place env.env.toEnvironment x := by
  with_unfolding_all rfl

/-!
General struct-eval bridges (main Clean's `eval_var`/`eval_expression`): rewrite the
`Eval.eval` of a provable variable to `ProvableType.eval`, which `explicit_provable_type`
then unfolds componentwise for *any* provable type. Provided at BOTH the abstract
`Var M F` form and the concrete `M (AssignedCell F)` form, so they fire regardless of
which spelling a goal carries — this replaces per-gadget eval-split lemmas.
-/

@[explicit_provable_type] lemma eval_var (env : Placed Environment F) (v : Var M F) :
    Eval.eval env v = ProvableType.eval env.place env.env (v : M (AssignedCell F)) := by
  with_unfolding_all rfl

@[explicit_provable_type] lemma eval_var_prover (env : Placed ProverEnvironment F) (v : Var M F) :
    Eval.eval env v = ProvableType.eval env.place env.env.toEnvironment (v : M (AssignedCell F)) := by
  with_unfolding_all rfl

@[explicit_provable_type] lemma eval_cells (env : Placed Environment F) (v : M (AssignedCell F)) :
    Eval.eval env v = ProvableType.eval env.place env.env v := by
  with_unfolding_all rfl

@[explicit_provable_type] lemma eval_cells_prover (env : Placed ProverEnvironment F) (v : M (AssignedCell F)) :
    Eval.eval env v = ProvableType.eval env.place env.env.toEnvironment v := by
  with_unfolding_all rfl

end ProvableType

end Halo2
