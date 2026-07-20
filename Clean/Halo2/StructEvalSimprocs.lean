import Clean.Halo2.Provable

/-!
# Simprocs for halo2 provable-type evaluation

Verifier-side counterpart of the witgen simprocs (`Clean.Circuit.WitnessIR`:
`evalProjection`, `evalStructLiteral`) and the port of main Clean's PR #424
`Clean.Circuit.StructEvalSimprocs`, adapted to halo2's evaluators
(`Halo2.ProvableStruct.eval`, `Halo2.ProvableType.eval`, and the `Eval.eval` class head)
over `Placed Environment`/`AssignedCell`.

The `circuit_norm` normal form for evaluation is component-preserving and row-level:

* `eval env ⟨a, b, …⟩` on a *literal* decomposes into `⟨eval env a, eval env b, …⟩`
  (higher-level components stay whole — a `U32` field is evaluated to a `U32 F` value, not
  four field reads);
* evaluation of a *projection* lifts to a projection of the row-level evaluation,
  `Eval.eval env s.f ~~> (Eval.eval env s).f`;
* evaluation of an *opaque* struct stays a folded row-level atom, consumed by row-level
  facts (`h_input : eval env input_var = input`);
* a constructor equality of provable types splits field-wise.

Two evaluation heads matter, in priority order (see `Halo2.ProvableStruct.eval_var_eq_eval`,
tagged `↓ high`): a **`ProvableStruct`** value decomposes along its semantic component
boundaries; a plain **`ProvableType`** value (e.g. `Point`) decomposes componentwise via
the same literal simproc, validated by definitional equality (structure eta survives; only
matcher reduction was lost in 4.31). This mirrors the witgen `evalStructLiteral` two-route
design.
-/

open Lean Meta Simp

namespace Halo2.StructEval

/-- Run a speculative step of the simproc machinery under a LOCAL heartbeat budget
(fresh baseline via `withCurrHeartbeats`): a pathological component — e.g. a list-indexed
`HVec (zLengths ns)` slot over an *abstract* width list (Sinsemilla's Chain output) —
sends instance synthesis and the `.all` defeq validation into six-figure reduction
counts. Speculative work must FAIL FAST and leave such values folded (parents consume
them via explicit bridges), not eat the calling tactic's entire budget. The cap is far
above any legitimate corpus step (small record/vector instances and defeqs). -/
def speculative {α : Type} (act : MetaM α) (fallback : α) : MetaM α :=
  withCurrHeartbeats <| withOptions (fun o => o.set `maxHeartbeats (8000 : Nat)) do
    try
      act
    catch _ =>
      return fallback

/-- The `.all`-transparency definitional-equality validation, capped (see `speculative`). -/
def validatedDefEq (a b : Expr) : MetaM Bool :=
  speculative (withTransparency .all <| isDefEq a b) false

/-- Whether `type` is `α ps` with `α` a `ProvableType` (behind `Var`/`Value` synonyms, so
`.instances` whnf). This is the gate for destructuring, projection lift and equality split:
`ProvableStruct` types qualify too (they have a `ProvableType` instance), and are handled
at higher priority by the struct-eval bridges. -/
def isProvableTypeLike (type : Expr) (allowDecomposable : Bool := true) : MetaM Bool :=
  speculative (α := Bool) (do
    let type' ← withTransparency .instances <| whnf type
    let .app tycon _ := type' | return false
    if (← trySynthInstance (← mkAppM ``ProvableType #[tycon])) matches .some _ then
      return true
    unless allowDecomposable do return false
    -- `deriving CircuitType` view companions of mixed provable/hint records: no
    -- `ProvableType`, but componentwise decomposable by the simprocs (the deriver marks
    -- them). The variable DESTRUCTURE gate passes `allowDecomposable := false`: a mixed
    -- record variable stays whole (its componentwise normal form comes from the derived
    -- `eval_*_raw` lemmas over its projections, not from `cases`).
    return (← trySynthInstance (← mkAppM ``DecomposableStruct #[tycon])) matches .some _)
    false

/-- View an expression as a structure projection `base.field`, returning the base and a
function that rebuilds the same projection on a new base. Handles both `.proj` nodes and
projection-function applications. -/
def projectionView? (e : Expr) : MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  match e with
  | .proj structName idx base =>
    return some (base, fun newBase => pure <| mkProj structName idx newBase)
  | _ =>
    let .const projName _ := e.getAppFn | return none
    let some pinfo ← getProjectionFnInfo? projName | return none
    let projArgs := e.getAppArgs
    if h : pinfo.numParams < projArgs.size then
      return some (projArgs[pinfo.numParams],
        fun newBase => mkProjection newBase (Name.mkSimple projName.getString!))
    else
      return none

/-- Evaluation heads that carry a `(… place env value)` / `(… env value)` shape. -/
private def evalHeads : Array Name :=
  #[``Eval.eval, ``Halo2.ProvableStruct.eval, ``Halo2.ProvableType.eval]

/-- Unfold a `List` literal expression into its element expressions. -/
private partial def listLitElems (e : Expr) : MetaM (Array Expr) := do
  match (← whnf e).getAppFnArgs with
  | (``List.cons, #[_, h, t]) => return #[h] ++ (← listLitElems t)
  | (``List.nil, _) => return #[]
  | _ => throwError "structEvalLiteral: components is not a list literal: {← ppExpr e}"

/--
Per-field evaluation term `Eval.eval placedEnv field`.

The plain route (`mkAppM ``Eval.eval #[placedEnv, field]`) synthesizes the `Eval` instance
from the *field's syntactic type*. That works for scalar fields (`AssignedCell F`) and
higher-level struct/point fields (`M (AssignedCell F)` with `M` a visible head), but *fails*
on a `Vector (AssignedCell F) n` field: the `Eval` instance is stated over `M (AssignedCell F)`
and `M = fields n` cannot be recovered by higher-order unification from a bare `Vector`.

When a fallback component `M`/`ProvableType`-instance is supplied (from the enclosing
`ProvableStruct`'s `components` list, where the vector field's `M = fields n` is spelled out
explicitly), we build the `Eval` instance directly — `CircuitType.verifierEval`/`proverEval M`
under the provable-type `CircuitType` — picking the verifier/prover view from the placed env's
constructor. This mirrors the witgen struct-literal simproc, which likewise routes each
component through its `ProvableStruct.components` entry rather than re-synthesizing from the raw
field type; here we keep halo2's record-literal normal form (`⟨eval a, eval v, …⟩`). -/
private def buildFieldEval (placedEnv field : Expr)
    (fallback? : Option (Expr × Expr)) : MetaM Expr := do
  if let some r ← speculative
      (some <$> (withTransparency .default <| mkAppM ``Eval.eval #[placedEnv, field]))
      none then
    return r
  let some (compTy, compInst) := fallback? |
    throwError "structEvalLiteral: no Eval instance for field {← ppExpr field} and no fallback"
  let placedTy ← whnf (← inferType placedEnv)
  let (``Halo2.Placed, #[envCtor, fF]) := placedTy.getAppFnArgs |
    throwError "structEvalLiteral: env is not `Placed …`: {← ppExpr placedTy}"
  withTransparency .default do
    let ctInst ← mkAppOptM ``ProvableType.toCircuitType #[some compTy, some compInst]
    let evalInst ←
      if envCtor.isConstOf ``Halo2.Environment then
        mkAppOptM ``Halo2.CircuitType.verifierEval #[some fF, none, some compTy, some ctInst]
      else
        mkAppOptM ``Halo2.CircuitType.proverEval #[some fF, none, some compTy, some ctInst]
    -- `Var M F` (the instance's declared `Var` slot) is reducibly `M (AssignedCell F)`, i.e. the
    -- raw `Vector (AssignedCell F) n` field type; check the app at `.default` so it is accepted.
    mkAppOptM ``Eval.eval #[none, none, none, some evalInst, some placedEnv, some field]

/--
Decompose evaluation of a struct/point **literal** component-wise:
```
Halo2.ProvableStruct.eval place env ⟨a, b, …⟩  ~~>  ⟨Eval.eval ⟨place,env⟩ a, …⟩
Halo2.ProvableType.eval   place env ⟨a, b, …⟩  ~~>  ⟨Eval.eval ⟨place,env⟩ a, …⟩
```
Fires only on constructor literals (opaque values stay folded atoms — the restriction that
makes the pair {literal-decompose, projection-lift} confluent). Each field is re-evaluated
through the `Eval.eval` class head, so struct fields recurse via the `↓ high` bridge and
scalar fields normalize to `AssignedCell.eval` in the same pass. Validated by definitional
equality at `.all` (matches the witgen struct-literal simproc).

A `Vector (AssignedCell F) n` field (e.g. an `Output.zs`, or any future bundle with a
vector-valued Output such as Sinsemilla) is handled via the enclosing `ProvableStruct`'s
`components` list: the plain `Eval.eval` synthesis cannot recover `M = fields n` from the raw
`Vector` field type, so on the `ProvableStruct.eval` route we thread the component's spelled-out
`M`/instance into `buildFieldEval` as a fallback. The vector field decomposes to
`Eval.eval placedEnv v` (a `Value (fields n) F`, i.e. `Vector F n`), which `circuit_norm`
further reduces to `Vector.map (AssignedCell.eval …)`. -/
def structEvalLiteralProc : Simproc := fun e => do
  let .const hname _ := e.getAppFn | return .continue
  let args := e.getAppArgs
  -- Recover the `Placed` env for the per-field `Eval.eval` calls, plus the value:
  --   `Eval.eval env x`                          — env is already `Placed`
  --   `Halo2.Provable{Struct,Type}.eval place env x` — reconstruct `⟨place, env⟩`
  -- On the `ProvableStruct.eval` route the type map `α` and its `ProvableStruct` instance are
  -- explicit args, giving a per-field fallback `M`/instance list from `components α` (the vector
  -- field's `M = fields n`, unrecoverable from the raw `Vector` field type). The other routes are
  -- plain `ProvableType` literals (scalar-only fields), where the plain `Eval.eval` synthesis
  -- always succeeds, so no fallback is needed.
  let (placedEnv?, x, fallbacks?) ← (do
    match hname with
    | ``Eval.eval =>
      unless args.size ≥ 2 do return (none, default, none)
      -- only a *provable-type* literal (avoid firing on `Eval.eval` of a scalar cell etc.)
      unless ← isProvableTypeLike (← inferType args[args.size - 1]!) do return (none, default, none)
      pure (some args[args.size - 2]!, args[args.size - 1]!, none)
    | ``Halo2.ProvableType.eval =>
      unless args.size ≥ 3 do return (none, default, none)
      let placed ← withTransparency .default <|
        mkAppM ``Halo2.Placed.mk #[args[args.size - 3]!, args[args.size - 2]!]
      pure (some placed, args[args.size - 1]!, none)
    | ``Halo2.ProvableStruct.eval =>
      unless args.size ≥ 7 do return (none, default, none)
      let placed ← withTransparency .default <|
        mkAppM ``Halo2.Placed.mk #[args[args.size - 3]!, args[args.size - 2]!]
      -- args: F, FiniteField, α, ProvableStruct α, place, env, value
      -- `.default` transparency so the `components` instance projection unfolds to its list
      -- literal (the simproc runs at `.reducible` by default, where it stays folded).
      let fallbacks? ← withTransparency .default <| (do
        try
          let comps ← mkAppOptM ``_root_.ProvableStruct.components #[args[args.size - 5]!, args[args.size - 4]!]
          let compExprs ← listLitElems comps
          let pairs ← compExprs.mapM fun c => do
            let ty ← whnf (← mkAppM ``_root_.ProvableStruct.WithProvableType.type #[c])
            let inst ← mkAppM ``_root_.ProvableStruct.WithProvableType.provableType #[c]
            pure (ty, inst)
          pure (some pairs)
        catch _ => pure none)
      pure (some placed, args[args.size - 1]!, fallbacks?)
    | _ => pure (none, default, none) : MetaM (Option Expr × Expr × Option (Array (Expr × Expr))))
  let some placedEnv := placedEnv? | return .continue
  let .const fn _ := x.getAppFn | return .continue
  let some (.ctorInfo info) := (← getEnv).find? fn | return .continue
  unless info.numFields > 0 do return .continue
  try
    let ctorArgs := x.getAppArgs
    if ctorArgs.size != info.numParams + info.numFields then return .continue
    -- fallbacks (when present) are aligned with the constructor's fields (in order)
    if let some fbs := fallbacks? then
      unless fbs.size == info.numFields do return .continue
    -- Rebuild with the constructor of the eval's RESULT type: for a pure provable struct
    -- that is `fn` itself at the value-side parameters (re-inferred), but a derived mixed
    -- record has a DIFFERENT companion structure per view (`Inputs.Var` vs `Inputs.Value` /
    -- `Inputs.ProverValue`), so the target constructor must come from the result type, not
    -- from the literal.
    let targetInfo ← (do
      let resultTy ← withTransparency .instances <| whnf (← inferType e)
      let .const resultTyName _ := resultTy.getAppFn | return info
      unless isStructure (← getEnv) resultTyName do return info
      let ctor := getStructureCtor (← getEnv) resultTyName
      unless ctor.numFields == info.numFields do return info
      pure ctor)
    let mut newArgs : Array (Option Expr) := #[]
    for _ in [0:targetInfo.numParams] do
      newArgs := newArgs.push none
    for i in [0:info.numFields] do
      let a := ctorArgs[info.numParams + i]!
      let fallback? := fallbacks?.map (·[i]!)
      newArgs := newArgs.push (some (← buildFieldEval placedEnv a fallback?))
    -- `.default` transparency to see through the reducible `CircuitType` instance behind
    -- `Value M F`-spelled field types (cf. the witgen simproc)
    let rhs ← withTransparency .default <| mkAppOptM targetInfo.name newArgs
    unless ← validatedDefEq e rhs do
      trace[Meta.Tactic.simp.rewrite] "structEvalLiteral: defeq validation failed {e} vs {rhs}"
      return .continue
    return .visit { expr := rhs, proof? := none }
  catch _ => return .continue

/--
Lift evaluation of a structure projection to a projection of the evaluation:
```
Eval.eval env s.f  ~~>  (Eval.eval env s).f
```
Registered on all `evalHeads`; the lift target keeps the same head with the projection base
swapped in, so it is env-shape agnostic. Gated to `ProvableType` bases (not pairs) and
validated by `.all` definitional equality. A simproc, not a lemma, because lemmas cannot
quantify over an arbitrary structure projection. -/
def evalProjectionLiftProc : Simproc := fun e => do
  let .const hname _ := e.getAppFn | return .continue
  -- number of *explicit* env-args preceding the evaluated value (so the value is the last):
  -- `Eval.eval env x` has 1; `Halo2.Provable{Struct,Type}.eval place env x` have 2.
  let nEnv ← match hname with
    | ``Eval.eval => pure 1
    | ``Halo2.ProvableStruct.eval | ``Halo2.ProvableType.eval => pure 2
    | _ => return .continue
  let args := e.getAppArgs
  unless args.size ≥ nEnv + 1 do return .continue
  let projected := args[args.size - 1]!
  let envArgs := args.extract (args.size - 1 - nEnv) (args.size - 1)
  let some (base, mkRhs) ← projectionView? projected | return .continue
  unless ← isProvableTypeLike (← inferType base) do return .continue
  -- rebuild `head envArgs base` via `mkAppM` so implicits/instances are re-inferred for the
  -- new base type (raw arg replacement would keep the projected field's stale implicits).
  -- The rebuild can fail for mixed (`deriving CircuitType`) bases whose eval type stays
  -- view-headed — those keep the componentwise form (the derived unfolding lemmas' RHS).
  let rhs ← try
      let evalOfBase ← withTransparency .default <| mkAppM hname (envArgs.push base)
      mkRhs evalOfBase
    catch _ => return .continue
  unless ← validatedDefEq rhs e do return .continue
  return .done { expr := rhs, proof? := none }

/--
Split a constructor equality of provable types into field-wise equalities:
```
(⟨a, b, …⟩ : S _) = ⟨a', b', …⟩  ~~>  a = a' ∧ b = b' ∧ …
```
Proof is the structure's generated `mk.injEq`. Gated to `ProvableType`(-like) structures so
`circuit_norm` does not change how simp treats arbitrary record equalities. -/
def structEqSplitProc : Simproc := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let args := e.getAppArgs
  let lhs := args[1]!.consumeMData
  let rhs := args[2]!.consumeMData
  let .const ctorName _ := lhs.getAppFn | return .continue
  unless rhs.getAppFn.isConstOf ctorName do return .continue
  let some (.ctorInfo info) := (← getEnv).find? ctorName | return .continue
  unless info.numFields > 0 do return .continue
  unless lhs.getAppNumArgs == info.numParams + info.numFields &&
      rhs.getAppNumArgs == info.numParams + info.numFields do return .continue
  let injEqName := ctorName ++ `injEq
  unless (← getEnv).contains injEqName do return .continue
  unless ← isProvableTypeLike args[0]! do return .continue
  try
    let params := lhs.getAppArgs[:info.numParams].toArray.map some
    let lhsFields := lhs.getAppArgs[info.numParams:].toArray.map some
    let rhsFields := rhs.getAppArgs[info.numParams:].toArray.map some
    let proof ← withTransparency .default <| mkAppOptM injEqName (params ++ lhsFields ++ rhsFields)
    let some (_, _, conj) := (← inferType proof).eq? | return .continue
    return .visit { expr := conj, proof? := some proof }
  catch _ => return .continue

simproc structEqSplit (_ = _) := structEqSplitProc
attribute [circuit_norm] structEqSplit

/- Distinct simproc names per evaluation head (one `registerSimproc` per name), all
delegating to the two cores above. -/
def structEvalLiteralStructProc : Simproc := structEvalLiteralProc
def structEvalLiteralTypeProc : Simproc := structEvalLiteralProc
def structEvalLiteralEvalProc : Simproc := structEvalLiteralProc
def evalProjectionLiftStructProc : Simproc := evalProjectionLiftProc
def evalProjectionLiftTypeProc : Simproc := evalProjectionLiftProc
def evalProjectionLiftEvalProc : Simproc := evalProjectionLiftProc

/-!
The surface `simproc … (Halo2.ProvableStruct.eval _ _)` syntax insists on synthesizing the
`ProvableStruct ?α` instance during pattern elaboration; compute the discrimination keys
with plain metavariables and register directly.
-/
open Elab in
run_cmd Command.liftTermElabM do
  let mkKeys := fun (head : Name) => do
    let f ← mkConstWithFreshMVarLevels head
    let (mvars, _, _) ← forallMetaTelescope (← inferType f)
    withSimpGlobalConfig <| DiscrTree.mkPath (mkAppN f mvars)
  let structKeys ← mkKeys ``Halo2.ProvableStruct.eval
  let typeKeys ← mkKeys ``Halo2.ProvableType.eval
  let evalKeys ← mkKeys ``Eval.eval
  registerSimproc ``structEvalLiteralStructProc structKeys
  registerSimproc ``structEvalLiteralTypeProc typeKeys
  registerSimproc ``structEvalLiteralEvalProc evalKeys
  registerSimproc ``evalProjectionLiftStructProc structKeys
  registerSimproc ``evalProjectionLiftTypeProc typeKeys
  registerSimproc ``evalProjectionLiftEvalProc evalKeys

attribute [circuit_norm] structEvalLiteralStructProc structEvalLiteralTypeProc
  structEvalLiteralEvalProc
  evalProjectionLiftStructProc evalProjectionLiftTypeProc evalProjectionLiftEvalProc

end Halo2.StructEval
