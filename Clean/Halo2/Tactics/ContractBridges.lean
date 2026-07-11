import Lean.Elab.Command
import Clean.Halo2.Formal

/-!
# `derive_contract_bridges`

Generates the hand-written contract-projection `rfl`-bridges for a `FormalRegionCircuit` /
`FormalCircuit` child bundle mechanically (C2a #2). For a consumer that composes a child `c`,
the pattern (from `Mul.lean`/`MulComplete.lean`/`Chain.lean`) is a stack of

```
private theorem c_spec_eq … : c.Spec = <reduced> := rfl
private theorem c_assumptions_eq … : c.Assumptions = <reduced> := rfl
private theorem c_envAssumptions_eq … : c.EnvAssumptions = <reduced> := rfl
private theorem c_proverAssumptions_eq … : c.ProverAssumptions = <reduced> := rfl
private theorem c_proverSpec_eq … : c.ProverSpec = <reduced> := rfl
```

— ~5-6 per consumer, ×4 consumers per file. `<reduced>` is the *value the bundle assigns to
that field*, obtained by projecting the field out of the bundle literal (a `whnf` that reduces
the structure projection but does not unfold the field's own body). The bridges then let a
consumer `simp only [c_spec_eq, …]` rewrite `c.Spec`/… to their concrete forms without unfolding
the whole bundle literal (the "child stays folded" discipline).

## Usage

```
derive_contract_bridges myChild := <bundle-term>
```

generates `myChild_spec_eq`, `myChild_assumptions_eq`, `myChild_envAssumptions_eq`,
`myChild_proverAssumptions_eq`, `myChild_proverSpec_eq`, each `:= rfl`, generalized over the free
variables of `<bundle-term>` (the section variables and explicit arguments it mentions). The
command elaborates `<bundle-term>`, projects each contract field, `whnf`-reduces the projection
to its assigned value, and emits the equality theorem. Any field whose projection does not reduce
by `rfl` is skipped with a warning (e.g. a bundle that leaves a default).
-/

open Lean Elab Command Meta Term

namespace Halo2.ContractBridges

/-- The contract fields to bridge, with the theorem-name suffix used for each. -/
def contractFields : Array (Name × String) := #[
  (`Spec, "spec"), (`Assumptions, "assumptions"), (`EnvAssumptions, "envAssumptions"),
  (`ProverAssumptions, "proverAssumptions"), (`ProverSpec, "proverSpec")]

/-- Elaborate `bundle`, and for each contract field build the `rfl`-bridge
`<projection> = <whnf projection>`, generalized over the term's free variables. Returns the
theorem name + type + proof for the ones that hold by `rfl`. -/
def buildBridges (baseName : Name) (bundle : Expr) :
    MetaM (Array (Name × Expr × Expr)) := do
  let mut out := #[]
  let bundleTy ← inferType bundle
  -- the structure the bundle inhabits (FormalRegionCircuit / FormalCircuit), to resolve the
  -- projection function names
  let .const structName _ := bundleTy.getAppFn |
    throwError "derive_contract_bridges: bundle type is not a structure application: {bundleTy}"
  for (fieldName, suffix) in contractFields do
    let projName := structName ++ fieldName
    unless (← getEnv).contains projName do continue
    let lhs ← try mkProjection bundle fieldName catch _ => continue
    -- reduce the projection to the assigned value (one delta of the projection, not the body)
    let rhs ← whnf lhs
    let eqTy ← mkEq lhs rhs
    -- generalize over the free variables the equation mentions (section vars + explicit args)
    let fvars ← getFVars eqTy
    let genTy ← mkForallFVars fvars eqTy
    -- prove by rfl (validating the projection reduces to `rhs` definitionally)
    let proof? ← try
      let pf ← mkForallFVars fvars (← mkEqRefl lhs)
      if ← isDefEq (← inferType pf) genTy then pure (some pf) else pure none
    catch _ => pure none
    match proof? with
    | some pf =>
      -- single-component name `<base>_<suffix>_eq`, in the base's namespace
      let thmName := match baseName with
        | .str p s => p ++ Name.mkSimple (s ++ "_" ++ suffix ++ "_eq")
        | _ => baseName ++ Name.mkSimple (suffix ++ "_eq")
      out := out.push (thmName, genTy, pf)
    | none =>
      logWarning m!"derive_contract_bridges: {projName} did not reduce by rfl; skipped"
  return out
where
  /-- The free variables appearing in `e`, in context order. -/
  getFVars (e : Expr) : MetaM (Array Expr) := do
    let fvarIds := (collectFVars {} e).fvarSet
    let mut acc := #[]
    for decl in ← getLCtx do
      if fvarIds.contains decl.fvarId && !decl.isImplementationDetail then
        acc := acc.push (.fvar decl.fvarId)
    return acc

syntax (name := deriveContractBridges)
  "derive_contract_bridges" ident " := " term : command

@[command_elab deriveContractBridges]
def elabDeriveContractBridges : CommandElab := fun stx => do
  match stx with
  | `(derive_contract_bridges $name:ident := $t:term) =>
    let baseName := (← getCurrNamespace) ++ name.getId
    liftTermElabM do
      let bundle ← Term.elabTermAndSynthesize t none
      let bridges ← buildBridges baseName bundle
      for (thmName, ty, pf) in bridges do
        addDecl (.thmDecl {
          name := thmName, levelParams := [], type := ty, value := pf })
  | _ => throwUnsupportedSyntax

end Halo2.ContractBridges
