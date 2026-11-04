module

public meta import Lean.Elab.Tactic
public meta import Lean.Elab.Tactic.Omega
public meta import Clean.Circuit.Explicit
public meta import Clean.Utils.Tactics.ProvableStructNaming
-- also non-meta: the pass runs `circuit_norm` with these simprocs wherever the tactic is used
public import Clean.Circuit.StructEvalSimprocs

/-!
# `computable_witnesses`

Automation for `FormalCircuitBase.ComputableWitnesses`: every witness generator of a circuit, every
subcircuit input and the circuit's output evaluate equally under two prover environments `env` and
`env'` that agree below the respective offset (`ProverEnvironment.AgreesBelow`), given that the
circuit input evaluates equally.

Each of these obligations has the form `T env = T env'`. The tactic proves them all with one
contextual `simp` pass over `circuit_norm` and the `@[computable_witnesses_law]` lemmas, which
*transport* evaluation from `env` to `env'` atom by atom:

* cells, hints and prover data (`ProverEnvironment.AgreesBelow.get_congr` and friends);
* the circuit input, through the input-equality premise, which the contextual pass uses as a
  rewrite rule;
* child outputs, through the child's output congruence (children are never unfolded);
* child obligations, through the subcircuit composition laws.

Once every `env` atom on the left is transported, both sides of an obligation coincide and `simp`
closes it. The laws' side conditions are agreement facts and offset arithmetic, closed by
`discharge`.
-/

public meta section

open Lean Meta Elab Tactic

namespace ComputableWitnesses

/-- Close the goal `g` with `omega` over the local hypotheses and the bounds of the `Fin` indices
in context (loop indices), splitting the `if`s in it (a length can be `if 0 < size M then …`). -/
partial def omegaGoal (g : MVarId) : MetaM Unit := do
  if let some (pos, neg) ← splitIfTarget? g then
    omegaGoal pos.mvarId
    omegaGoal neg.mvarId
    return
  let some g' ← g.falseOrByContra | return
  g'.withContext do
    let mut facts := (← getLocalHyps).toList
    for x in ← getLocalHyps do
      if (← whnfR (← inferType x)).isAppOfArity ``Fin 1 then
        facts := (← mkAppM ``Fin.isLt #[x]) :: facts
    Elab.Tactic.Omega.omega facts g'

/-- Close a natural-number (in)equality with `omegaGoal`. -/
def omega? (e : Expr) : MetaM (Option Expr) := do
  let s ← saveState
  try
    let g ← mkFreshExprSyntheticOpaqueMVar e
    omegaGoal g.mvarId!
    return some (← instantiateMVars g)
  catch _ =>
    s.restore
    return none

/-- Whether `e` is an (in)equality between natural numbers. -/
def isNatArith (e : Expr) : Bool :=
  match_expr e with
  | LT.lt t _ _ _ => t.isConstOf ``Nat
  | LE.le t _ _ _ => t.isConstOf ``Nat
  | Eq t _ _ => t.isConstOf ``Nat
  | _ => false

/-- A proof of `env.AgreesBelow b env'` weakened from an agreement hypothesis
`env.AgreesBelow k env'` with `b ≤ k`. `env'` may be a metavariable, which the hypothesis then
determines: this is how the transport laws, whose right-hand side mentions `env'`, get
instantiated. -/
def weakenAgreement? (b env env' : Expr) : MetaM (Option Expr) := do
  for decl in (← getLCtx).decls.toArray.reverse do
    let some decl := decl | continue
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    unless ty.isAppOf ``ProverEnvironment.AgreesBelow do continue
    let hargs := ty.getAppArgs
    let s ← saveState
    if (← isDefEq env hargs[hargs.size - 2]!) && (← isDefEq env' hargs[hargs.size - 1]!) then
      if let some le ← omega? (← mkAppM ``LE.le #[b, hargs[hargs.size - 3]!]) then
        return some (← mkAppM ``ProverEnvironment.AgreesBelow.of_le #[decl.toExpr, le])
    s.restore
  return none

/-- Close `env.AgreesBelow b env'` by `weakenAgreement?`, after normalizing the bound so that
child `localLength` metadata reaches `omega` as arithmetic. -/
def agreement? (e : Expr) : SimpM (Option Expr) := do
  unless e.isAppOf ``ProverEnvironment.AgreesBelow do return none
  let args := e.getAppArgs
  let b ← Simp.simp args[args.size - 3]!
  let some h ← weakenAgreement? b.expr args[args.size - 2]! args[args.size - 1]! | return none
  -- the normalized bound may differ from the original one only definitionally: state the
  -- proof at the original type, which simp checks the assignment against at reducible
  -- transparency
  let h ← match b.proof? with
    | some p => mkAppM ``ProverEnvironment.AgreesBelow.of_le #[h, ← mkAppM ``Nat.le_of_eq #[p]]
    | none => pure h
  return some (← mkExpectedTypeHint h (← instantiateMVars e))

/-- The discharger of the transport pass: agreement goals by weakening, arithmetic by `omega`,
anything else by simp's default discharger, which simps the side condition with the same laws
(so the input premise of a child's output congruence is itself transported). -/
def discharge : Simp.Discharge := fun e => do
  let e ← instantiateMVars e
  if let some p ← agreement? e then return some p
  if isNatArith e then
    -- normalized first, so that metadata (`localLength`) reaches `omega` as arithmetic
    let r ← Simp.simp e
    if r.expr.isTrue then return some (← mkOfEqTrue (← r.getProof))
    let some p ← omega? r.expr | return none
    return some (← mkExpectedTypeHint (← mkEqMPR (← r.getProof) p) e)
  Simp.dischargeDefault? e

/-- Definitional reduction of a bundle's `localLength` metadata to its explicit form (a numeral,
or arithmetic in the circuit's parameters), so that offset side conditions reach `omega` as
arithmetic. A child is never unfolded otherwise. -/
def reduceLocalLengthCore : Simp.DSimproc := fun e => do
  let .const name _ := e.getAppFn | return .continue
  unless name == `FormalCircuitBase.localLength || name == ``ElaboratedCircuit.localLength do
    return .continue
  if e.hasLooseBVars || e.hasMVar then return .continue
  let w := (← withDefault <| whnf e).headBeta
  let stuck := w.find? fun sub =>
    sub.isConstOf `FormalCircuitBase.localLength || sub.isConstOf ``ElaboratedCircuit.localLength ||
      sub.isConstOf ``Operations.localLength || sub.isConstOf ``Circuit
  if w == e || stuck.isSome then return .continue
  return .visit w

dsimproc_decl reduceLocalLength (_) := reduceLocalLengthCore

/-- Rewrite `e` with the equation or equivalence `thm`, instantiated by matching its left-hand side
against `e`. -/
def rewriteWith? (thm : Name) (e : Expr) : MetaM (Option Simp.Result) := do
  let c ← mkConstWithFreshMVarLevels thm
  let (args, _, type) ← forallMetaTelescopeReducing (← inferType c)
  let (source, target, isIff) ← match type.eq?, type.iff? with
    | some (_, l, r), _ => pure (l, r, false)
    | _, some (l, r) => pure (l, r, true)
    | _, _ => return none
  unless ← isDefEq source e do return none
  let proof ← instantiateMVars (mkAppN c args)
  let proof ← if isIff then mkPropExt proof else pure proof
  return some { expr := ← instantiateMVars target, proof? := proof }

/-- An equation between applications of one constructor splits into equations between its
arguments, by the constructor's `injEq` theorem: premises then become rewrite rules on atoms. -/
def ctorEqSplitCore : Simp.Simproc := fun e => do
  let_expr Eq _ lhs rhs := e | return .continue
  let env ← getEnv
  let ctorApp? (e : Expr) : Option ConstructorVal := do
    let .ctorInfo ctor ← env.find? (← e.getAppFn.constName?) | none
    guard (e.getAppNumArgs == ctor.numParams + ctor.numFields)
    return ctor
  let some ctor := ctorApp? lhs | return .continue
  unless (ctorApp? rhs).any (·.name == ctor.name) do return .continue
  let some r ← rewriteWith? (mkInjectiveEqTheoremNameFor ctor.name) e | return .continue
  return .visit r

simproc_decl ctorEqSplit (_ = _) := ctorEqSplitCore

/-- The evaluation of a value the obligation treats as a black box: an input variable, a child
output or a loop accumulator. Its whole-vector equation is a rewrite rule (or a law) as it
stands, and rewrites element access as well, so it is not decomposed. -/
def isAtomEval (e : Expr) : Bool :=
  e.isAppOf ``Eval.eval && e.getAppNumArgs ≥ 1 &&
    (e.appArg!.isFVar || e.appArg!.isAppOfArity `FormalCircuitBase.output 9 ||
      e.appArg!.isAppOfArity ``Fin.foldl 4)

/-- An equation between computed vectors is decided elementwise (`Vector.ext_iff`), where element
access reduces through the getElem lemmas of `circuit_norm`. Equations between vector literals
are left to `ctorEqSplit` (element access into a literal at a symbolic index is stuck), and
equations between evaluations of black-box values stay whole (`isAtomEval`). -/
def vectorExtCore : Simp.Simproc := fun e => do
  let_expr Eq type lhs rhs := e | return .continue
  unless (← whnfR type).isAppOfArity ``Vector 2 do return .continue
  if lhs.isAppOf ``Vector.mk && rhs.isAppOf ``Vector.mk then return .continue
  if isAtomEval lhs then return .continue
  let some r ← rewriteWith? ``Vector.ext_iff e | return .continue
  return .visit r

simproc_decl vectorExt (_ = _) := vectorExtCore

/-- An equation between computed Booleans is decided as an equivalence of propositions
(`Bool.eq_iff_iff`, then `Bool.and_eq_true`, `decide_eq_true_eq`, ...): a transported `decide`
keeps the `Decidable` instance of its original proposition, so its two sides never become
syntactically equal, while the propositions do. -/
def boolEqSplitCore : Simp.Simproc := fun e => do
  let_expr Eq type lhs rhs := e | return .continue
  unless type.isConstOf ``Bool do return .continue
  if lhs.isConstOf ``true || lhs.isConstOf ``false || rhs.isConstOf ``true ||
    rhs.isConstOf ``false then return .continue
  let some r ← rewriteWith? ``Bool.eq_iff_iff e | return .continue
  return .visit r

simproc_decl boolEqSplit (_ = _) := boolEqSplitCore

/-- `decide p` whose `Decidable` instance is typed by `p` before a definitional unfolding (simp
does not rewrite inside instance arguments) gets its instance annotated with `Decidable p`, so
that lemmas about `decide p` match it at reducible transparency. -/
def refreshDecideCore : Simp.DSimproc := fun e => do
  let_expr decide p inst := e | return .continue
  let instType ← instantiateMVars (← inferType inst)
  if instType.isAppOf ``Decidable && instType.appArg! == p then return .continue
  let inst ← mkExpectedTypeHint inst (mkApp (mkConst ``Decidable) p)
  return .done (mkApp2 (mkConst ``decide) p inst)

dsimproc_decl refreshDecide (decide _) := refreshDecideCore

/-- Add one hint to the pass: a simp set contributes all its lemmas, a simproc runs in the pass,
a theorem is a rewrite rule, a definition is unfolded, and any other term (local hypotheses
included) is elaborated as a rewrite rule. -/
def addHint (thms : SimpTheorems) (sets : Array SimpTheorems) (procs : Array Name)
    (t : Term) : TacticM (SimpTheorems × Array SimpTheorems × Array Name) := do
  if let `($id:ident) := t then
    if let some ext ← getSimpExtension? id.getId then
      return (thms, sets.push (← ext.getTheorems), procs)
    if let some declName ← observing? (realizeGlobalConstNoOverloadWithInfo id) then
      if ← Simp.isSimproc declName then
        return (thms, sets, procs.push declName)
      if ← isProp (← getConstInfo declName).type then
        return (← thms.addConst declName, sets, procs)
      return (← thms.addDeclToUnfold declName, sets, procs)
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if let .fvar fvarId := e then
    return (← thms.add (.fvar fvarId) #[] e, sets, procs)
  return (← thms.add (.other (← mkFreshUserName `hint)) #[] e, sets, procs)

/-- A law (`@[computable_witnesses_law]`) instantiated at the environments `env` and `env'` of the
obligation, which a law states as its first two `ProverEnvironment` binders. Instantiated, the
law rewrites only `env`-atoms, into `env'`-atoms. -/
def instantiateLaw (law : Name) (env env' : Expr) : MetaM Expr := do
  let thm ← mkConstWithFreshMVarLevels law
  let (args, binders, _) ← forallMetaTelescope (← inferType thm)
  let mut envs := [env, env']
  for arg in args do
    let some e := envs.head? | break
    if (← instantiateMVars (← inferType arg)).isAppOf ``ProverEnvironment then
      unless ← isDefEq arg e do throwError "computable_witnesses: law {law} does not apply"
      envs := envs.tail
  for arg in args, bi in binders do
    if bi.isInstImplicit && !(← arg.mvarId!.isAssigned) then
      let type ← instantiateMVars (← inferType arg)
      unless type.hasMVar do
        if let some inst ← synthInstance? type then arg.mvarId!.assign inst
  return (← abstractMVars (← instantiateMVars (mkAppN thm args))).expr

/-- The plain `Circuit` definitions reachable from `e`: the circuit's own `main` and the helpers it
is written with. Only bundles (`FormalCircuit` and its variants) are proof boundaries, so these
are inlined, by the rule `elaborate_circuit` uses (`isUnfoldableCircuitDecl`, which keeps the
library's combinators folded). -/
def plainCircuitDefs (e : Expr) : MetaM (Array Name) := do
  let noUnfold ← labelled `explicit_circuit_no_unfold
  let unfoldType ← labelled `explicit_circuit_unfold_type
  let mut found := #[]
  let mut todo := e.getUsedConstants
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if found.contains c then continue
    let some (.defnInfo info) := (← getEnv).find? c | continue
    unless resultTypeHead? info.type == some ``Circuit do continue
    unless ← isUnfoldableCircuitDecl c (some noUnfold) (some unfoldType) do continue
    found := found.push c
    todo := todo ++ info.value.getUsedConstants
  return found

/-- What the pass adds to `circuit_norm`, besides the laws. -/
def passLemmas : List Name := [
  -- equations between values are taken apart down to atoms
  ``ProvableType.toElements_inj_iff, ``ProvableType.fromElements_inj_iff,
  -- witness programs that compute a provable value evaluate to the value's elements, so that
  -- they are compared as values (and split by constructor), not elementwise
  ``Witgen.WitgenIR.eval_ofCompositeFExpr, ``Witgen.M.eval_toIRLiteral,
  ``Witgen.WitgenIR.eval_nativeValue,
  -- evaluation and element access through constructions that `circuit_norm` keeps folded
  ``ProvableType.toElements_fields, ``ProvableType.eval_fromElements, ``Vector.get_eq_getElem,
  ``Vector.append_eq_hAppend, ``List.getElem_singleton,
  ``Vector.getElem_mapIdx, ``Vector.getElem_zip, ``eval_ite, ``eval_dite, ``eval_vector_sum,
  ``eval_foldl_add, ``eval_foldl_mul, ``eval_foldl,
  -- Boolean equations, decided as propositions (`boolEqSplit`)
  ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true', ``decide_eq_true_eq]

/-- Congruence for index binders with the bound in context, so that the cells an index
addresses are transported. -/
def passCongr : List Name := [``Vector.mapRange_congr, ``Vector.ofFn_congr,
  ``Vector.mapFinRange_congr, ``Vector.mapIdx_congr, ``Fin.foldl_congr_lt]

/-- The transport pass: `circuit_norm`, `passLemmas` and the laws at `env`, `env'`, with the plain
circuit definitions of the goal unfolded and the hints added. Contextual, so that premises of
the laws' side conditions are rewrite rules too, with `discharge` for side conditions. Equations
are taken apart down to atoms (`passLemmas`, `ctorEqSplit`, `boolEqSplit`, and `vectorExt` in
the leaf pass), so that premises are rewrite rules on atoms and conclusions compare atoms. -/
def transportContext (hints : Array Term) (env env' : Expr) :
    TacticM (Simp.Context × Simp.SimprocsArray) := withMainContext do
  let mut thms ← simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  thms ← thms.addDeclToUnfold ``ProverEnvironment.OnlyAccessedBelow
  -- a loop's accumulator is a fold of the steps' outputs, transported by `foldl_congr`
  -- (the loop library is downstream of this tactic)
  if (← getEnv).contains `Circuit.FoldlM.foldlAcc then
    thms ← thms.addDeclToUnfold `Circuit.FoldlM.foldlAcc
  for thm in passLemmas do
    thms ← thms.addConst thm
  for c in ← plainCircuitDefs (← instantiateMVars (← getMainTarget)) do
    thms ← thms.addDeclToUnfold c
  for law in ← labelled `computable_witnesses_law do
    thms ← thms.add (.decl law) #[] (← instantiateLaw law env env')
  let mut sets := #[]
  let mut procNames := #[]
  for t in hints do
    (thms, sets, procNames) ← addHint thms sets procNames t
  let some normExt ← getSimpExtension? `circuit_norm | throwError "unknown simp set circuit_norm"
  let some normProcs ← Simp.getSimprocExtension? `circuit_norm
    | throwError "unknown simproc set circuit_norm"
  let mut procs : Simp.SimprocsArray := #[← normProcs.getSimprocs]
  for p in procNames ++ #[``reduceLocalLength, ``refreshDecide, ``ctorEqSplit, ``boolEqSplit] do
    procs ← procs.add p (post := true)
  let mut congr ← getSimpCongrTheorems
  for c in passCongr do
    congr := addSimpCongrTheoremEntry congr (← mkSimpCongrTheorem c (eval_prio default))
  let ctx ← Simp.mkContext { contextual := true, maxDischargeDepth := 64, failIfUnchanged := false }
    (simpTheorems := #[thms, ← normExt.getTheorems] ++ sets) congr
  return (ctx, procs)

/-- Run `simp` with `ctx` on the main goal, rewriting with the given hypotheses as well. -/
def simpWith (ctx : Simp.Context) (procs : Simp.SimprocsArray) (hyps : Array FVarId := #[]) :
    TacticM Unit := withMainContext do
  let mut thms := ctx.simpTheorems
  if let some first := thms[0]? then
    let mut first := first
    for h in hyps do
      first ← first.add (.fvar h) #[] (mkFVar h)
    thms := thms.set! 0 first
  let ctx := ctx.setSimpTheorems thms
  match (← simpGoal (← getMainGoal) ctx procs (discharge? := discharge)).1 with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]

/-- The free variables that `e` takes apart: bases of structure projections and discriminants of
`match`es. -/
def takenApart (e : Expr) : MetaM (Array FVarId) := do
  let found ← IO.mkRef (#[] : Array FVarId)
  let add (x : Expr) : MetaM Unit := do
    let .fvar x := x | return
    unless (← found.get).contains x do found.modify (·.push x)
  e.forEach' fun sub => do
    if let .proj _ _ base := sub then add base
    if let .const c _ := sub.getAppFn then
      if let some info ← getProjectionFnInfo? c then
        if let some base := sub.getAppArgs[info.numParams]? then add base
    if let some m ← matchMatcherApp? sub then
      for discr in m.discrs do add discr
    return true
  found.get

/-- Destructure `x` into fields named after it, if it has a structure type other than `Vector`.
Returns the new goal and the fields. -/
def destructure (g : MVarId) (x : FVarId) : MetaM (MVarId × Array FVarId) := g.withContext do
  let type ← withTransparency .instances <| whnf (← x.getType)
  let .const name _ := type.getAppFn | return (g, #[])
  unless isStructure (← getEnv) name && name != ``Vector do return (g, #[])
  let names ← ProvableStructNaming.generateStructFieldNames x
  let #[sub] ← g.cases x #[names] | return (g, #[])
  return (sub.mvarId, sub.fields.filterMap (·.fvarId?))

/-- Split a normalized obligation into its leaves: conjunctions are split, and binders and
premises are introduced, the agreement premise as `h_agrees` and other premises as `h`. Returns
the leaves with the premises each one introduced. -/
partial def splitLeaves (g : MVarId) (hyps : Array FVarId := #[]) :
    MetaM (Array (MVarId × Array FVarId)) := do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  if t.isAppOfArity ``And 2 then
    let [l, r] ← g.apply (mkConst ``And.intro) | return #[(g, hyps)]
    return (← splitLeaves l hyps) ++ (← splitLeaves r hyps)
  if t.isForall then
    let name := if t.bindingDomain!.isAppOf ``ProverEnvironment.AgreesBelow then `h_agrees
      else if t.bindingName!.hasMacroScopes then `h else t.bindingName!
    let (h, g) ← g.intro name
    let isPremise ← g.withContext do isProp (← h.getType)
    return ← splitLeaves g (if isPremise then hyps.push h else hyps)
  return #[(g, hyps)]

/-- The wrapper chain of a circuit: `main`, and while its body is an application of a plain
circuit definition, that definition. Recursive definitions and class methods end the chain: their
compiled value is not the body as written. -/
partial def wrapperChain (c : Name) : MetaM (Array Name) := do
  let some (.defnInfo info) := (← getEnv).find? c | return #[]
  unless resultTypeHead? info.type == some ``Circuit do return #[]
  if (← isRecursiveDefinition c) || (← isProjectionFn c) then return #[]
  let next ← lambdaTelescope info.value fun _ body => pure body.getAppFn.constName?
  let rest ← match next with
    | some d => if ← isUnfoldableCircuitDecl d then wrapperChain d else pure #[]
    | none => pure #[]
  return #[c] ++ rest

/-- Unfold the obligation, introduce `n input env env'` and normalize, destructuring the input
where the obligation takes it apart. Then every leaf is closed by the contextual transport pass,
with its premises as rewrite rules. -/
def run (hints : Array Term) : TacticM Unit := do
  liftMetaTactic fun g => do
    let t ← instantiateMVars (← g.getType)
    -- the circuit's own `main` (through its wrapper chain) is expanded before simp runs, as
    -- `circuit_proof_start` does: the `↓` lemmas of the outermost combinator (loops) then see it
    -- before its body unfolds
    let chain ← match t.appArg!.getAppFn.constName? with
      | some main => wrapperChain main
      | none => pure #[]
    let t ← deltaExpand t fun c => c == `FormalCircuitBase.ComputableWitnesses || chain.contains c
    let g ← g.change (← Core.betaReduce t)
    return [(← g.introN 4 [`n, `input, `env, `env']).2]
  -- the pass at the environments of the main goal, its last two `ProverEnvironment`s
  -- (destructuring reintroduces them)
  let context : TacticM (Simp.Context × Simp.SimprocsArray) := withMainContext do
    let envs := (← getLCtx).foldl (init := #[]) fun envs decl =>
      if decl.type.isAppOf ``ProverEnvironment then envs.push decl.toExpr else envs
    let #[env, env'] := envs.extract (envs.size - 2) envs.size
      | throwError "computable_witnesses: the obligation has no environments"
    transportContext hints env env'
  let input ← withMainContext do
    let some input := (← getLCtx).findFromUserName? `input
      | throwError "computable_witnesses: no input"
    pure input.fvarId
  let (ctx, procs) ← context
  simpWith (← ctx.setConfig { ctx.config with contextual := false }) procs
  -- the input is destructured where the obligation takes it apart (its projections then reduce,
  -- a `match` on it is no longer stuck, and the input premise splits accordingly)
  let mut (ctx, procs) := (ctx, procs)
  let mut parts := #[input]
  for _ in [0:8] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let mut g' := g
    let xs ← g.withContext do takenApart (← instantiateMVars (← g.getType))
    for x in xs do
      if parts.contains x then
        let (g'', fields) ← destructure g' x
        g' := g''
        parts := parts ++ fields
    if g' == g then break
    replaceMainGoal [g']
    (ctx, procs) ← context
    simpWith (← ctx.setConfig { ctx.config with contextual := false }) procs
  if (← getGoals).isEmpty then return
  let leaves ← splitLeaves (← getMainGoal)
  let mut remaining := #[]
  -- vector equations are decided elementwise only where the leaf's premises do not transport
  -- them whole: simp reaches an equation after its sides
  procs ← procs.add ``vectorExt (post := true)
  for (leaf, hyps) in leaves do
    setGoals [leaf]
    simpWith ctx procs hyps
    remaining := remaining ++ (← getGoals)
  setGoals remaining.toList

end ComputableWitnesses

/-- Prove `FormalCircuitBase.ComputableWitnesses`, the default tactic of the `computableWitnesses`
field. Hints are added to the pass: lemmas, definitions to unfold, simp sets, simprocs or terms.
On failure, the obligations that remain after the pass are reported. -/
syntax "computable_witnesses" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses $[[$hints,*]]?) => do
    ComputableWitnesses.run (hints.map (·.getElems) |>.getD #[])
    let goals ← getGoals
    unless goals.isEmpty do
      throwError "computable_witnesses: could not close\n{goalsToMessageData goals}"
