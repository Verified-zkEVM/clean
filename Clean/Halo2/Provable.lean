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

/-- The verifier view of a placed prover environment: same placement, hints erased
(via `ProverEnvironment.toEnvironment`). This is how completeness statements evaluate
verifier-side values under the honest prover's environment. -/
def Placed.toEnvironment {F : Type} (env : Placed ProverEnvironment F) : Placed Environment F :=
  { place := env.place, env := env.env.toEnvironment }

@[circuit_norm] lemma ProverEnvironment.toEnvironment_advice {F : Type}
    (e : ProverEnvironment F) (col : Column .advice) (row : ℤ) :
    e.toEnvironment.advice col row = e.advice col row := rfl

@[circuit_norm] lemma ProverEnvironment.toEnvironment_get {F : Type}
    (e : ProverEnvironment F) (col : AnyColumn) (row : ℤ) :
    e.toEnvironment.get col row = e.get col row := rfl

/-- `toEnvironment` of a reconstructed placed environment, reduced — the spelling the
split-`env` proof states carry after `circuit_proof_start` destructures the binder. -/
@[circuit_norm] lemma Placed.toEnvironment_mk {F : Type} (p : RegionIndex → ℕ)
    (e : ProverEnvironment F) :
    (Placed.mk p e).toEnvironment = ⟨p, e.toEnvironment⟩ := rfl

@[circuit_norm] lemma Placed.toEnvironment_place {F : Type} (env : Placed ProverEnvironment F) :
    env.toEnvironment.place = env.place := rfl

@[circuit_norm] lemma Placed.toEnvironment_env {F : Type} (env : Placed ProverEnvironment F) :
    env.toEnvironment.env = env.env.toEnvironment := rfl

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

-- low priority: with a reducible `toCircuitType`, this head is close to universal;
-- prefer direct instances (mirror of main Clean's forwarder, for `deriving CircuitType`'s
-- `Value`-companion `ProvableStruct`)
instance (priority := low) : ProvableType (Value M) :=
  (inferInstance : ProvableType M)

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

/-- `Var field`-keyed spelling of `eval_field` (cf. the hint carriers' `eval_*_prover'`
keying lemmas): a scalar-cell eval synthesized from the `Var field F` type spelling — as
the struct-literal simproc builds for a derived mixed record's scalar field — carries the
`CircuitType.verifierEval field` instance at `Var field F`, whose simp keys stop at the
`field` head and so never match `eval_field`'s `AssignedCell F` pattern. -/
@[circuit_norm]
lemma eval_field' (env : Placed Environment F) (x : Var field F) :
    @Eval.eval _ _ _ (CircuitType.verifierEval field) env x
      = AssignedCell.eval env.place env.env x := by
  with_unfolding_all rfl

/-- Prover-side companion of `eval_field'`. -/
@[circuit_norm]
lemma eval_field_prover' (env : Placed ProverEnvironment F) (x : Var field F) :
    @Eval.eval _ _ _ (CircuitType.proverEval field) env x
      = AssignedCell.eval env.place env.env.toEnvironment x := by
  with_unfolding_all rfl

/-!
General struct-eval bridges (main Clean's `eval_var`/`eval_expression`): rewrite the
`Eval.eval` of a provable variable to `ProvableType.eval`, which `explicit_provable_type`
then unfolds componentwise for *any* provable type. Provided at BOTH the abstract
`Var M F` form and the concrete `M (AssignedCell F)` form, so they fire regardless of
which spelling a goal carries — this replaces per-gadget eval-split lemmas.
-/

-- Deliberately `explicit_provable_type` only, NOT `circuit_norm`: `Eval.eval` is the normal
-- form (nicer to state facts against), so `circuit_norm` must not flatten plain
-- `ProvableType`s to `ProvableType.eval`. `provable_type_simp` decomposes plain-type
-- *literals* directly on the `Eval.eval` head instead (see `StructEvalSimprocs`).
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

/-!
### Vector-of-cells evaluation

A `fields n` component of a provable struct (e.g. an `Output.zs` running-sum vector) evaluates
to the `Vector.map` of the per-cell read. Only the **lazy** `getElem` bridges are `circuit_norm`
members: they resolve `(eval env v)[i]` to a single cell read **on demand** — the vector analogue
of `evalProjectionLift`, so a length-`n` `zs` eval stays a folded row atom until an index projects
it, never re-inflating to a mapped vector nobody uses. The whole-vector `map` equations
(`eval_fields_cells`/`_prover`) are the *stated* facts the `getElem` proofs are built on; they are
deliberately **NOT** `circuit_norm` (an eager map form would fight the `getElem` bridges — the
PR-424 getElem/map loop hazard — and eagerly decompose vectors nobody projects). -/

/-- Evaluating a `fields n` vector of cells is the elementwise cell read. Stated with the
explicit `fields n` `Eval` instance: the plain `Eval` synthesis cannot recover `M = fields n`
from a raw `Vector (AssignedCell F) n` field type (the reason the struct-eval simproc threads
the component instance in via `buildFieldEval`); this is the same instance that simproc builds.
Deliberately **not** `@[circuit_norm]` — see the section note (the eager map form is a loop hazard
against the `getElem` bridge and re-inflates unprojected vectors). -/
lemma eval_fields_cells {n : ℕ} (env : Placed Environment F) (v : fields n (AssignedCell F)) :
    (Eval.eval env v : fields n F) = v.map (AssignedCell.eval env.place env.env) := by
  with_unfolding_all rfl

/-- Prover-view `fields n` vector-of-cells evaluation. Not `@[circuit_norm]` (see `eval_fields_cells`). -/
lemma eval_fields_cells_prover {n : ℕ} (env : Placed ProverEnvironment F)
    (v : fields n (AssignedCell F)) :
    (Eval.eval env v : fields n F) = v.map (AssignedCell.eval env.place env.env.toEnvironment) := by
  with_unfolding_all rfl

/-- Indexing into an evaluated `fields n` vector of cells reads that cell — the LAZY bridge that
fires when a goal carries `(eval env v)[i]` (e.g. `output.zs[i]` for a vector-valued `Output`).
`circuit_norm`, so projections resolve on demand without eagerly mapping the whole vector.

The evaluated value `v` is typed `fields n (AssignedCell F)` (not a bare `Vector`), so the
`Eval.eval` instance elaborates to the `fields n` circuit-type evaluator — the SAME instance the
struct-eval simproc's `buildFieldEval` threads in — and the `circuit_norm` discrimination key
matches the vector-component eval the splitter produces. -/
@[circuit_norm]
lemma getElem_eval_fields_cells {n : ℕ} (env : Placed Environment F)
    (v : fields n (AssignedCell F)) (i : ℕ) (hi : i < n) :
    (Eval.eval env v : fields n F)[i] = AssignedCell.eval env.place env.env v[i] := by
  rw [show (Eval.eval env v : fields n F) = v.map (AssignedCell.eval env.place env.env) from
    eval_fields_cells env v]
  rw [Vector.getElem_map]

/-- Prover-view lazy `getElem` bridge for a `fields n` vector of cells. -/
@[circuit_norm]
lemma getElem_eval_fields_cells_prover {n : ℕ} (env : Placed ProverEnvironment F)
    (v : fields n (AssignedCell F)) (i : ℕ) (hi : i < n) :
    (Eval.eval env v : fields n F)[i] = AssignedCell.eval env.place env.env.toEnvironment v[i] := by
  rw [show (Eval.eval env v : fields n F) = v.map (AssignedCell.eval env.place env.env.toEnvironment)
    from eval_fields_cells_prover env v]
  rw [Vector.getElem_map]

end ProvableType

/-!
## Struct-preserving evaluation

Halo2 counterpart of main Clean's `ProvableStruct.eval` (`Clean/Circuit/Provable.lean`):
evaluate a struct of cell references component-by-component, keeping the high-level
`ProvableStruct` shape instead of flattening to a field vector. The `@[circuit_norm ↓ high]`
bridges rewrite `Eval.eval env x` (verifier and prover views) to this form for *any*
derived `ProvableStruct`, so a derived-struct input decomposes into its components without
a per-gadget `eval_eq` lemma — matching main Clean, and symmetric with the witgen-side
`Witgen.StructEval.eval` (`Clean/Circuit/WitnessIR.lean`).
-/

namespace ProvableStruct
open _root_.ProvableStruct (WithProvableType ProvableTypeList componentsToElements componentsFromElements combinedSize')
variable {α : TypeMap} [ProvableStruct α]

/-- Evaluate each component of a struct of cell references separately, given the region
placement + verifier environment.

Deliberately *not* `@[circuit_norm]` (nor `.go`): the def stays folded so opaque structs
remain row-level atoms (consumable by `h_input`-style facts); the `structEvalLiteral`
simproc owns literal decomposition. This matches main Clean's PR #424 design and is what
lets the same normal form survive the 4.31 matcher-eta change. -/
def eval (place : RegionIndex → ℕ) (env : Environment F) (var : α (AssignedCell F)) : α F :=
  toComponents var |> go (components α) |> fromComponents
where
  go : (cs : List WithProvableType) → ProvableTypeList (AssignedCell F) cs → ProvableTypeList F cs
    | [], .nil => .nil
    | _ :: cs, .cons a as => .cons (ProvableType.eval place env a) (go cs as)

/-- `ProvableStruct.eval` agrees with the flat `ProvableType.eval`. -/
theorem eval_eq_eval (place : RegionIndex → ℕ) (env : Environment F) (x : α (AssignedCell F)) :
    ProvableType.eval place env x = ProvableStruct.eval place env x := by
  symm
  simp only [eval, ProvableType.eval, fromElements, toElements, size]
  congr 1
  apply eval_eq_eval_aux
where
  eval_eq_eval_aux (place : RegionIndex → ℕ) (env : Environment F) :
      (cs : List WithProvableType) → (as : ProvableTypeList (AssignedCell F) cs) →
      eval.go place env cs as
        = (componentsToElements cs as |> Vector.map (AssignedCell.eval place env)
            |> componentsFromElements cs)
    | [], .nil => rfl
    | c :: cs, .cons a as => by
      simp only [componentsToElements, componentsFromElements, eval.go,
        combinedSize', List.map_cons, List.sum_cons]
      simp only [Vector.map_append, Vector.cast_take_append_of_eq_length,
        Vector.cast_drop_append_of_eq_length]
      congr 1
      apply eval_eq_eval_aux

/-- Verifier `Eval.eval` of a derived struct variable is componentwise. Preferred over the
flat unfold (`↓ high`), so goals keep the struct shape. -/
@[circuit_norm ↓ high]
theorem eval_var_eq_eval (env : Placed Environment F) (x : Var α F) :
    Eval.eval env x = ProvableStruct.eval env.place env.env (x : α (AssignedCell F)) := by
  rw [ProvableType.eval_var]; exact eval_eq_eval env.place env.env (x : α (AssignedCell F))

/-- Prover-view componentwise `Eval.eval` of a derived struct variable. -/
@[circuit_norm ↓ high]
theorem eval_var_eq_eval_prover (env : Placed ProverEnvironment F) (x : Var α F) :
    Eval.eval env x = ProvableStruct.eval env.place env.env.toEnvironment (x : α (AssignedCell F)) := by
  rw [ProvableType.eval_var_prover]; exact eval_eq_eval env.place _ (x : α (AssignedCell F))

/-- Verifier componentwise `Eval.eval`, concrete `α (AssignedCell F)` spelling. -/
@[circuit_norm ↓ high]
theorem eval_cells_eq_eval (env : Placed Environment F) (x : α (AssignedCell F)) :
    Eval.eval env x = ProvableStruct.eval env.place env.env x := by
  rw [ProvableType.eval_cells]; exact eval_eq_eval env.place env.env x

/-- Prover componentwise `Eval.eval`, concrete `α (AssignedCell F)` spelling. -/
@[circuit_norm ↓ high]
theorem eval_cells_eq_eval_prover (env : Placed ProverEnvironment F) (x : α (AssignedCell F)) :
    Eval.eval env x = ProvableStruct.eval env.place env.env.toEnvironment x := by
  rw [ProvableType.eval_cells_prover]; exact eval_eq_eval env.place _ x

end ProvableStruct

end Halo2
