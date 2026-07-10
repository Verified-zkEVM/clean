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

/-- Whether `type` is `α ps` with `α` a `ProvableType` (behind `Var`/`Value` synonyms, so
`.instances` whnf). This is the gate for destructuring, projection lift and equality split:
`ProvableStruct` types qualify too (they have a `ProvableType` instance), and are handled
at higher priority by the struct-eval bridges. -/
def isProvableTypeLike (type : Expr) : MetaM Bool := do
  let type' ← withTransparency .instances <| whnf type
  let .app tycon _ := type' | return false
  try
    return (← trySynthInstance (← mkAppM ``ProvableType #[tycon])) matches .some _
  catch _ => return false

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
equality at `.all` (matches the witgen struct-literal simproc). -/
def structEvalLiteralProc : Simproc := fun e => do
  let head := e.getAppFn
  unless head.isConstOf ``Halo2.ProvableStruct.eval || head.isConstOf ``Halo2.ProvableType.eval do
    return .continue
  let args := e.getAppArgs
  unless args.size ≥ 3 do return .continue
  let place := args[args.size - 3]!
  let env := args[args.size - 2]!
  let x := args[args.size - 1]!
  let .const fn _ := x.getAppFn | return .continue
  let some (.ctorInfo info) := (← getEnv).find? fn | return .continue
  unless info.numFields > 0 do return .continue
  try
    let ctorArgs := x.getAppArgs
    if ctorArgs.size != info.numParams + info.numFields then return .continue
    -- `Placed` env for the per-field `Eval.eval` calls
    let placedEnv ← withTransparency .default <| mkAppM ``Halo2.Placed.mk #[place, env]
    let mut newArgs : Array (Option Expr) := #[]
    for _ in [0:info.numParams] do
      newArgs := newArgs.push none
    for a in ctorArgs[info.numParams:] do
      newArgs := newArgs.push (some (← withTransparency .default <| mkAppM ``Eval.eval #[placedEnv, a]))
    -- `.default` transparency to see through the reducible `CircuitType` instance behind
    -- `Value M F`-spelled field types (cf. the witgen simproc)
    let rhs ← withTransparency .default <| mkAppOptM fn newArgs
    unless ← withTransparency .all <| isDefEq e rhs do
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
  -- new base type (raw arg replacement would keep the projected field's stale implicits)
  let evalOfBase ← try withTransparency .default <| mkAppM hname (envArgs.push base)
    catch _ => return .continue
  let rhs ← mkRhs evalOfBase
  unless ← withTransparency .all <| isDefEq rhs e do return .continue
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
  registerSimproc ``evalProjectionLiftStructProc structKeys
  registerSimproc ``evalProjectionLiftTypeProc typeKeys
  registerSimproc ``evalProjectionLiftEvalProc evalKeys

attribute [circuit_norm] structEvalLiteralStructProc structEvalLiteralTypeProc
  evalProjectionLiftStructProc evalProjectionLiftTypeProc evalProjectionLiftEvalProc

end Halo2.StructEval
