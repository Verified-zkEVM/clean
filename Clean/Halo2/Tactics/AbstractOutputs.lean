import Lean.Elab.Tactic
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw

/-!
# `abstract_outputs` — make subcircuit-call outputs opaque in the proof state

The thesis (maintainer): a parent proof never needs a child subcircuit output's *exact
expression*. Everything the parent consumes about a child output lives in the child's
`Spec`/`ProverSpec`, stated over the output as an opaque value. So the proof state should carry
each child output as an OPAQUE local, with every fact restated over it, and NO escape hatch back
to the concrete cell-record expression.

This tactic is that abstraction mechanism — and only that. It does not consume child contracts
(`subcircuit_rw` does), does not peel binds (`circuit_norm` does), does not decompose provable
evals (`provable_type_simp` does). It runs in the pipeline

    circuit_norm → provable_type_simp → **abstract_outputs** → subcircuit_rw → row-fact chaining

replacing the hand-rolled `have hout1 : (child.call …).output self = child.output … self := rfl`
+ `set`/`rw` idiom that composite gadgets (MulComplete, Mul, Chain) write out by hand today.

## The occurrence inventory (Phase 1 — the guises a child output takes)

Catalogued from real proof states of `Add` (leaf, no calls), `MulComplete` (loop, two chained
calls), `Chain` (list-recursive), and `Mul` (deep 5-child assembly). Every syntactic guise a
child-call output takes at the point abstraction runs, and how this tactic handles it:

| # | Guise | Where seen | Handling |
|---|-------|-----------|----------|
| 1 | `(child.call cfg off inp).output self` (region: `RegionCircuit.output`; layouter: `Circuit.output`) | `hC2`/goal chunk inputs, `h_spec_i`, `hwit` | **canonicalized** to guise 2 (syntactic rewrite by a `rfl`-proved map) first, then abstracted |
| 2 | `child.output cfg off inp self` (`FormalRegionCircuit.output`/`FormalCircuit.output`) | after the `hout1`/`hout2` rfl bridge; engine-emitted `h_spec_i` own-output | **the canonical abstraction target** |
| 3 | output as a field of a LATER call's input record: `{ p := acc, q := (child.call …).output self }` | chained-call goal chunks, `h_spec_1` input | guise-1 inside → canonicalized → abstracted as a whole `.output` subterm |
| 4 | nested output-in-output `(child.call off+1 { …, q := (child.call off …).output self }).output self` | pre-abstraction goal (MulComplete SND-A) | inner canonicalized+abstracted first (innermost-first order), outer then over the now-opaque input |
| 5 | `eval env <output>` whole | child `Spec` facts, goal output equation | the `<output>` subterm inside the `eval` is abstracted; the `eval` wraps the fresh local (`eval env o`) |
| 6 | projections `output.x`/`.acc`/`.xANext`/`.zs`/`.zs[i]` | Chain/Mul threading + parent output record | the WHOLE `output` under the projection is abstracted; the projection then reads the opaque local (`o.xANext` etc.) |
| 7 | post-`provable_type_simp` per-cell atoms `env.advice col row` | leaf gadgets, own-cell reads | **not an output** — these are the parent's own cells, never abstracted (opacity of guise 2 keeps the child output from ever decomposing into these) |
| 8 | raw composed output `(do …).output i₀` (`Bind.bind`-bodied `RegionCircuit.output`/`Circuit.output`) | a parent's OWN region output feeding a later chunk's input (Mul: `(mainRegion …).output`'s components in the overflow input) | abstracted whole, same as a bundle output — no child `Spec`, but its value facts flow through the parent's own `h_output`/witness equations, reconnected via `← h_gen_out_i` (see `isRawComposedOutput` for the `Bind.bind` gate rationale) |

Guise 7 is the ordering constraint's whole point: once a child output is an opaque local,
`provable_type_simp` *cannot* scatter it into `env.advice` atoms (there is nothing to
destructure). Abstraction must run at/after enough `circuit_norm`/`provable_type_simp` peeling that
guises 1–2 have stabilized, and BEFORE further eval-decomposition — but since a child output is
already an opaque `.output` accessor that `provable_type_simp` treats as an atom (confirmed:
MulComplete's `Add.add.output …` survives `provable_type_simp` whole), the natural placement is
right after `provable_type_simp` and right before `subcircuit_rw`.

## Granularity (Phase 2 decision): whole-output opaque local

`o : Var Output F` at the var level. Rationale from the inventory: MulComplete consumes each add
output *whole* (`Add.add.Spec input output _ := output.Valid ∧ output = …`); Chain projects it
(`out.xANext`, `out.zs`) but those are projections of the whole record, which `o.xANext` serves
directly. No proof consumes a child output's field without going through the whole output first, so
per-component locals would be strictly more machinery for no gain. The `_iff`-pattern componentwise
destructuring (`rintro ⟨ox, oy⟩`) happens downstream on the child's *Spec value*, fed by the
whole-output local — not on the output var.

## Var vs value split

Guises 1–4/6 abstract at the **var** level (`Var Output F`): later inputs embed the output var, so
those occurrences must all point at one `o`. Guise 5's `eval env o` is the value the Spec consumes;
it is covered for free, because the `eval` is not part of the abstracted subterm — every
`eval env <output>` becomes `eval env o`. No separate value-local is minted; the caller may layer
`set ov := eval env o` if it wants a named value.

## Reused technique (Phase 2)

Non-forcing abstraction via kabstract at `.reducible` with no `isTypeCorrect` re-check
(`SubcircuitRw.abstractInExpr`), so a deep composed `.output` never unfolds during matching. This
tactic generalizes that helper from "deep chunk inputs" to "all child outputs", which is why the
engine's threshold-gated deep-input machinery is subsumed: once every call output is an opaque
local, the inputs that used to be deep (they embedded a composed `.output`) are shallow by
construction.

## Engine cooperation (Phase 2/3)

`subcircuit_rw`'s completeness mode emits `h_spec_i` statements — and its soundness mode the
weakened `EnvA → A → Spec` consequence — that mention the child's own output. Run order:
`abstract_outputs` runs BEFORE `subcircuit_rw`. The cooperation contract is that the engine, when
building a chunk's contract statement, first checks for an existing `h_gen_out_i : <output> = x`
abstraction equation in context and, if present, emits the statement OVER `x` at the source rather
than materializing the concrete output term. So the abstraction is never undone and no post-hoc
reuse pass is needed — `abstract_outputs` mints fresh locals + equations once, and the engine
consults them. This tactic leaves those equations in context (named `h_gen_out_<i>`) precisely so
the engine can find them. See `SubcircuitRw.findOutputLocal?` / `SubcircuitRw.abstractOutputsIn`.
-/

open Lean Elab Tactic Meta

namespace Halo2

initialize registerTraceClass `Halo2.abstract_outputs

namespace AbstractOutputs

/-! ## Recognizing a child-call output term (guises 1–2) -/

/-- Is `e` a canonical output-form application `FormalRegionCircuit.output …` /
`FormalCircuit.output …`? -/
def isCanonicalOutput (e : Expr) : Bool :=
  e.isAppOf ``FormalRegionCircuit.output || e.isAppOf ``FormalCircuit.output

/-- Is `e` a **raw composed** output — `RegionCircuit.output body self` / `Circuit.output body i₀`
with a `Bind.bind`-headed `body` (an unfolded do-block, e.g. a parent's own composed main region)?

These are abstracted alongside child-bundle outputs: the opacity thesis applies uniformly to ALL
output expressions. A raw region output has no child `Spec`, but that doesn't matter for opacity —
its value facts flow through the parent's own `h_output`/witness/constraint equations, which the
abstraction equation reconnects (`rw [← h_gen_out_i]`) at componentwise sites exactly like a bundle
output.

The `Bind.bind` gate is the design choice (vs abstracting all `.output` applications uniformly): a
FOLDED def application (`(mainRegion cfg inp).output i₀`) is already opaque — the def name *is* the
abstraction, and consumers own `rfl` projection lemmas for it — and single-op primitives
(`(assignAdvice …).output`, cell handles) are the shallow atoms proofs consume via their `output_*`
lemmas. Only the composed bind chain has lost its name and goes deep, so only it is abstracted.
(Call-form child outputs share these heads but are canonicalized to bundle form before collection;
their body is a folded `call`, never a bind.) Consumers whose witness facts still carry the FOLDED
spelling of the same output must unfold it to the goal's bind spelling first (Mul completeness:
`simp only [mainRegion] at hWOv`), so one local serves both sides. -/
def isRawComposedOutput (e : Expr) : Bool :=
  (e.isAppOfArity ``RegionCircuit.output 5 || e.isAppOfArity ``Circuit.output 5)
    && (e.getAppArgs[3]!).isAppOf ``Bind.bind

/-- If `e` is a **call-form** output `RegionCircuit.output (child.call …) self` /
`Circuit.output (child.call …) i₀`, return the equivalent **canonical output-form** term. `none`
otherwise. Reads `child`/`cfg`/`off`/`inp` off the folded `call` boundary (`whnfR` + head-const
check), mirroring `SubcircuitRw.matchChunk?`. The result is `rfl`-equal to `e`. -/
def callFormToCanonical? (e : Expr) : MetaM (Option Expr) := do
  let fn := e.getAppFn
  let .const headName _ := fn | return none
  let args := e.getAppArgs
  let (isRegion, body, regionIdx) ←
    if headName == ``RegionCircuit.output && args.size == 5 then pure (true, args[3]!, args[4]!)
    else if headName == ``Circuit.output && args.size == 5 then pure (false, args[3]!, args[4]!)
    else return none
  let body ← whnfR body
  let bodyFn := body.getAppFn
  let .const callName _ := bodyFn | return none
  let callArgs := body.getAppArgs
  if isRegion && callName == ``FormalRegionCircuit.call && callArgs.size == 12 then
    -- callArgs: [8]child [9]config [10]offset [11]input; `mkAppM` infers the type implicits from
    -- these explicit args, so we don't hand-thread the ConfigInput/Config/Input/Output params.
    return some (← mkAppM ``FormalRegionCircuit.output
      #[callArgs[8]!, callArgs[9]!, callArgs[10]!, callArgs[11]!, regionIdx])
  else if !isRegion && callName == ``FormalCircuit.call && callArgs.size == 11 then
    -- callArgs: [8]child [9]config [10]input
    return some (← mkAppM ``FormalCircuit.output
      #[callArgs[8]!, callArgs[9]!, callArgs[10]!, regionIdx])
  else
    return none

/-! ## Canonicalization: call form → output form, as a pure syntactic substitution

We turn every call-form output occurrence (guise 1) into canonical output form (guise 2) by a
single `Expr.replace` over each target (goal + hyps), justified by a `rfl` proof of `old = new`
(they are definitionally equal). Pure syntactic replacement avoids simp's discrimination-tree
spelling fragility and never reduces the deep composed input. Innermost-first so nested call forms
(guise 4) canonicalize bottom-up. -/

/-- Build the call-form → canonical-form replacement as a function usable by `Expr.replace`.
Returns `some new` when `e` is a call-form output, else `none` (so `replace` recurses). -/
partial def canonicalizeExpr (e : Expr) : MetaM Expr := do
  -- `Expr.replaceM`-style: try the whole node; if it's a call form, replace and recurse into the
  -- (already-canonical) result's arguments to catch nested outputs inside the input record.
  match ← callFormToCanonical? e with
  | some canon =>
    -- recurse into the canonical form's arguments (the input record may embed further outputs)
    canonicalizeChildren canon
  | none => canonicalizeChildren e
where
  canonicalizeChildren (e : Expr) : MetaM Expr := do
    match e with
    | .app f a => return .app (← canonicalizeExpr f) (← canonicalizeExpr a)
    | .lam n t b bi => return .lam n (← canonicalizeExpr t) (← canonicalizeExpr b) bi
    | .forallE n t b bi => return .forallE n (← canonicalizeExpr t) (← canonicalizeExpr b) bi
    | .letE n t v b nd => return .letE n (← canonicalizeExpr t) (← canonicalizeExpr v) (← canonicalizeExpr b) nd
    | .mdata m b => return .mdata m (← canonicalizeExpr b)
    | .proj s i b => return .proj s i (← canonicalizeExpr b)
    | _ => return e

/-- Canonicalize call-form outputs to output form in the goal + every non-implementation
hypothesis, via `Eq.mpr`/`replaceLocalDecl` with a `rfl`-proved equation. No-op when everything is
already canonical (the replacement equals the original ⇒ we skip). Returns the number of
targets changed. -/
def canonicalizePass : TacticM Nat := withMainContext do
  let mut changed := 0
  -- goal
  let goalTy ← instantiateMVars (← getMainTarget)
  let goalTy' ← canonicalizeExpr goalTy
  unless goalTy' == goalTy do
    let g ← getMainGoal
    let eqPf ← mkExpectedTypeHint (← mkEqRefl goalTy) (← mkEq goalTy goalTy')
    let g' ← g.replaceTargetEq goalTy' eqPf
    replaceMainGoal [g']
    changed := changed + 1
  -- hypotheses (snapshot fvarIds; re-fetch each decl fresh since replaceLocalDecl remaps the goal)
  let fvarIds := (← getLCtx).foldl (init := #[]) fun acc decl =>
    if decl.isImplementationDetail then acc else acc.push decl.fvarId
  for fvarId in fvarIds do
    let didChange ← withMainContext do
      let some decl := (← getLCtx).find? fvarId | return false
      let ty ← instantiateMVars decl.type
      let ty' ← canonicalizeExpr ty
      if ty' == ty then return false
      let g ← getMainGoal
      let eqPf ← mkExpectedTypeHint (← mkEqRefl ty) (← mkEq ty ty')
      let r ← g.replaceLocalDecl fvarId ty' eqPf
      replaceMainGoal [r.mvarId]
      return true
    if didChange then changed := changed + 1
  return changed

/-! ## Collecting the outputs (canonical + raw-composed form, innermost-first) -/

/-- Collect every canonical output-form subterm of `e` (child bundle outputs) AND every
raw-composed output (`Bind.bind`-bodied, guise 8 — a parent's own unfolded composed region),
innermost first, deduped by `Expr` equality. Skips subterms with loose bvars — in particular, the
child calls inside a raw output's bind continuations sit under the continuation lambdas, so a raw
output abstracts as ONE whole opaque local; the child outputs proofs consume appear as separate
closed occurrences in chunk inputs and get their own locals first (innermost-first). -/
partial def collectOutputs (e : Expr) : StateRefT (Array Expr) MetaM Unit := do
  let e := e.consumeMData
  match e with
  | .app .. =>
    for a in e.getAppArgs do collectOutputs a
    collectOutputs e.getAppFn
    if (isCanonicalOutput e || isRawComposedOutput e) && !e.hasLooseBVars then
      modify fun acc => if acc.any (· == e) then acc else acc.push e
  | .lam _ t b _ | .forallE _ t b _ => collectOutputs t; collectOutputs b
  | .letE _ t v b _ => collectOutputs t; collectOutputs v; collectOutputs b
  | .proj _ _ b => collectOutputs b
  | .mdata _ b => collectOutputs b
  | _ => pure ()

/-- All canonical outputs across goal + non-implementation hyps, innermost-first, deduped. Two
occurrences of the SAME child output can be collected in different implicit-instance spellings (the
goal's vs a hypothesis's), which are `==`-distinct but reducibly defeq; a second `reducible`-defeq
dedup pass merges them (keeping the first, innermost-first spelling) so we mint ONE local per output
rather than an aliased chain `x_gen_out_i = x_gen_out_j`. `.reducible` never unfolds a composed
`.output`, and distinct children (different child/offset) are not defeq, so genuinely distinct
outputs stay separate. -/
def collectAllOutputs : TacticM (Array Expr) := withMainContext do
  let mut acc : Array Expr := #[]
  let (_, acc1) ← (collectOutputs (← instantiateMVars (← getMainTarget))).run acc
  acc := acc1
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let (_, acc2) ← (collectOutputs (← instantiateMVars decl.type)).run acc
    acc := acc2
  -- reducible-defeq dedup (preserves innermost-first order)
  let mut deduped : Array Expr := #[]
  for e in acc do
    let mut dup := false
    for k in deduped do
      if ← withTransparency .reducible <| isDefEq k e then dup := true; break
    unless dup do deduped := deduped.push e
  return deduped

/-! ## The abstraction

For the collected outputs `es` (innermost-first), abstract each to a fresh opaque local `o_i` and
leave the equation `h_out_i : eᵢ = o_i` in context. We do this whole-context (revert every
non-implementation hypothesis into the goal, abstract in the combined goal, re-intro) — the same
shape as `SubcircuitRw.runSoundness`'s deep-input abstraction, generalized to all hypotheses so an
output shared between a hypothesis and the goal is abstracted to ONE local everywhere.

`abstractInExpr` (reused) does the non-forcing `kabstract` at `.reducible` and skips the
`isTypeCorrect` re-check, so a deep composed `.output` never unfolds. -/

/-- Abstract the outputs `es` (innermost-first) in `target`, threading the substitution so nested
outputs (guise 4) still match after their inner output has been abstracted. Returns
`(target', wrap)` where `target' = ∀ x₀ (h₀ : e₀ = x₀) x₁ (h₁ : e₁' = x₁) …, target[eᵢ := xᵢ]` (with
`eᵢ'` = `eᵢ` with each earlier `eⱼ` replaced by `xⱼ`), and `wrap : target' → target` supplies each
`xᵢ := eᵢ`, `hᵢ := rfl`.

Unlike `SubcircuitRw.abstractInExpr`, after abstracting `eᵢ ↦ xᵢ` in the body we ALSO rewrite the
remaining targets `eⱼ` (j>i) by `eᵢ ↦ xᵢ`, so an outer output whose input embedded the inner output
matches the (now inner-abstracted) occurrence in the body. Non-forcing `kabstract` at `.reducible`;
no `isTypeCorrect` re-check (a deep composed `.output` never unfolds). `wrap`'s `rfl` proofs
typecheck because each `xᵢ := eᵢ` and, by the `eⱼ' = eⱼ[eⱼ's earlier ⱼ := xⱼ]` construction with
`xⱼ := eⱼ`, `eⱼ'[x := e]` is defeq to `eⱼ`. -/
def abstractOutputsInExpr (target : Expr) (es : Array Expr) :
    MetaM (Expr × (Expr → Expr)) := do
  let n := es.size
  let body ← instantiateMVars target
  let mut tys : Array Expr := #[]
  let mut lvls : Array Level := #[]
  for e in es do
    let ty ← inferType e
    tys := tys.push ty
    lvls := lvls.push (← getLevel ty)
  let xNames := (Array.range n).map fun i => Name.mkSimple s!"x_gen_out_{i}"
  let hNames := (Array.range n).map fun i => Name.mkSimple s!"h_gen_out_{i}"
  withLocalDeclsD (xNames.mapIdx fun i nm => (nm, fun _ => pure tys[i]!)) fun xs => do
    let mut b := body
    -- the running substitution image of each target (updated as earlier ones are abstracted)
    let mut cur := es
    let mut eqLHS : Array Expr := #[]   -- the LHS spelled in each hᵢ (after earlier substitutions)
    for i in [0:n] do
      let ei := cur[i]!
      eqLHS := eqLHS.push ei
      -- abstract `ei` in the body
      let abs ← withTransparency .reducible <| kabstract b ei
      trace[Halo2.abstract_outputs] "kabstract target {i}: matched={abs.hasLooseBVars}"
      b := abs.instantiate1 xs[i]!
      -- thread the substitution into the remaining targets so nested outputs still match
      for j in [i+1:n] do
        let absj ← withTransparency .reducible <| kabstract cur[j]! ei
        cur := cur.set! j (absj.instantiate1 xs[i]!)
    -- build `∀ x₀ h₀ x₁ h₁ …, b` with hᵢ : eqLHS[i] = xᵢ
    let mut result := b
    for i in (List.range n).reverse do
      let eqTy ← mkEq eqLHS[i]! xs[i]!
      result ← mkForallFVars #[xs[i]!] (Expr.forallE hNames[i]! eqTy result .default)
    let esC := es; let tysC := tys; let lvlsC := lvls
    let wrap := fun (f : Expr) =>
      Id.run do
        let mut acc := f
        for i in [0:n] do
          acc := mkApp acc esC[i]!
          acc := mkApp acc (mkApp2 (.const ``Eq.refl [lvlsC[i]!]) tysC[i]! esC[i]!)
        pure acc
    return (result, wrap)

/-- The set of fvars an output term (transitively) depends on — the circuit parameters (`cfg`,
`offset`, `acc`, `self`, …). These MUST stay in the local context during the revert-and-abstract,
so the output terms remain closed and `kabstract` (over closed terms) matches occurrences inside
the reverted hypotheses. -/
def outputDeps (outs : Array Expr) : MetaM (Std.HashSet FVarId) := do
  let mut deps : Std.HashSet FVarId := {}
  for e in outs do
    for fv in (← getFVarsInExpr e) do
      deps := deps.insert fv
  return deps
where
  getFVarsInExpr (e : Expr) : MetaM (Array FVarId) := do
    let fvs := (Lean.collectFVars {} e).fvarIds
    return fvs

/-! ## The runner -/

/-- Abstract each collected output to a fresh `x_gen_out_<i>` local with an equation
`h_gen_out_<i> : eᵢ = x_gen_out_<i>` in context, replacing every occurrence in the goal AND every
non-implementation hypothesis by the local.

Whole-goal design: revert every non-implementation hypothesis EXCEPT those the outputs depend on
(the circuit parameters — reverting them would turn the outputs' atoms into bvars and defeat
`kabstract`), abstract all outputs in the combined goal (via `abstractOutputsInExpr`, non-forcing
kabstract at `.reducible`, no `isTypeCorrect` re-check ⇒ a deep composed `.output` never unfolds),
then re-intro the abstraction binders + equations + the reverted hyps. Outputs are innermost-first,
so a nested output is abstracted before the enclosing one (whose input is then already the opaque
local).

Engine cooperation is now one-directional: `abstract_outputs` runs FIRST, leaving the `h_gen_out_i`
equations, and `subcircuit_rw` emits its `h_spec_i`/soundness consequences OVER those locals (via
`SubcircuitRw.abstractOutputsIn`, keyed on the same equations). So the engine never re-materializes
a concrete output, and no post-hoc reuse/re-substitution pass is needed here — a single fresh-mint
pass suffices. -/
def runAbstractOutputs : TacticM Unit := withMainContext do
  -- 0. canonicalize call forms to output form (to a fixpoint — nested forms need repeats)
  let mut guard := 0
  while (← canonicalizePass) > 0 && guard < 8 do
    guard := guard + 1
  withMainContext do
  -- 1. collect the outputs to abstract (innermost-first, canonical form)
  let outs ← collectAllOutputs
  trace[Halo2.abstract_outputs] "collected {outs.size} output(s) to abstract"
  if outs.isEmpty then
    trace[Halo2.abstract_outputs] "no subcircuit-call outputs found — no-op"
    return
  -- 2. revert every non-implementation hyp EXCEPT the outputs' dependencies (circuit params).
  let deps ← outputDeps outs
  let hyps := (← getLCtx).foldl (init := #[]) fun acc decl =>
    if decl.isImplementationDetail || deps.contains decl.fvarId then acc else acc.push decl.fvarId
  -- `revert` also pulls in any hyp that depends on a reverted one; `deps` stay put because the
  -- reverted set excludes them and Lean keeps a hyp iff nothing reverted mentions it — but a
  -- reverted Spec hyp does not appear in the type of a `deps` param, so the split is clean.
  let (reverted, g) ← (← getMainGoal).revert hyps true
  -- 3. abstract the outputs in the combined goal (non-forcing kabstract at reducible), threading
  --    the substitution: after abstracting `eᵢ ↦ xᵢ`, later targets `eⱼ` (j>i) that embed `eᵢ`
  --    (guise 4, nested output-in-output) are updated to reference `xᵢ`, so they still match the
  --    now-rewritten occurrences. Innermost-first collection guarantees `eᵢ ⊑ eⱼ` for `i<j`.
  let gTy ← instantiateMVars (← g.getType)
  let (gTy', wrap) ← abstractOutputsInExpr gTy outs
  let m ← mkFreshExprSyntheticOpaqueMVar gTy' (tag := ← g.getTag)
  g.assign (wrap m)
  -- 4. re-intro: the `2 * outs.size` abstraction binders (x_gen_out_i, h_gen_out_i), then the hyps.
  let (_absVars, g2) ← m.mvarId!.introNP (2 * outs.size)
  let (_reIntros, g3) ← g2.introNP reverted.size
  replaceMainGoal [g3]

end AbstractOutputs

/-- `abstract_outputs` — replace every subcircuit-call output in the proof state by an opaque local.

Canonicalizes call-form outputs (`(child.call …).output self`) to output form
(`child.output … self`), then abstracts every distinct child output to a fresh `o_out_<i>` local,
leaving `h_out_<i> : <output> = o_out_<i>` in context. Every occurrence — inside later inputs, under
`eval`, under projections, in hypotheses and the goal — is replaced by the local. Innermost-first,
so nested composed outputs abstract bottom-up. Silent no-op when no child output is present (leaf
gadgets). `set_option trace.Halo2.abstract_outputs true` to debug. -/
syntax (name := abstractOutputs) "abstract_outputs" : tactic

@[tactic abstractOutputs]
def evalAbstractOutputs : Tactic := fun _ => AbstractOutputs.runAbstractOutputs

end Halo2
