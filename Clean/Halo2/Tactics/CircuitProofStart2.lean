import Lean.Elab.Tactic
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Halo2.Tactics.CircuitProofStart
import Clean.Halo2.Tactics.AbstractOutputs

/-!
# `circuit_proof_start2` — the atomic-binds proof prefix (CPS v2)

Implements `Clean/Halo2/atomic-binds-design.md`: the peel instantiates every used bind's
continuation at a **do-binder-named atom**, so the proof state mirrors the do-block and
concrete output terms never propagate. Distilled from the v2-manual exemplars
(`Action/{SpendAuthority,AddressIntegrity,ValueCommit}.lean`, commits 378ec475 →
59452517) — the tactic emits exactly those proofs' framework blocks:

- **(a)** intro the config (destructured through products, binder names recovered from
  the `synthesize` pattern-match), enter the `soundness_iff`/`completeness_iff` form
  with the house binder names, split the placed env into `place`/`env`;
- **(b)** `dsimp only [] at *` (iota-reduces the destructured-config matches), then land
  `h_output` on the raw do-block output via `ElaboratedCircuit.output_eq`;
- **(c)** per bind, one block: single `operations_bind` peel (`constraints_append` at
  `hC`, plus `extendsWitnesses_append` at `hW` and the goal's constraints side in the
  completeness direction), `output_bind` at `h_output`, split off the chunk as
  `h_call_<name>` (call binds) / `h_region_<k>` (raw binds, immediately
  `circuit_norm`-opened), canonicalize the output spelling (`output_call'`), then mint
  the atom by `generalize h_<name> : <canonical output> = <name>` under a
  `revert hC h_output` — BEFORE the continuation's occurrences diverge — and fold the
  offsets (`nextRegionIndex_call` + the `foldCallRegionCount` simproc);
- **(d)** terminal `pure`: close the op list, land `h_output` on the final atom;
- **(e)** `subcircuit_rw` — per chunk hypothesis (soundness) / goal-mode once
  (completeness, emitting `h_spec_<k>` over the atoms);
- **(f)** value landing: destructure `input_var`/`input` into per-field components
  (names from the `Input` structure: `input_var_<f>` / `input_<f>`), one
  `circuit_norm` pass over the state (evals of ATOMS stay whole — no
  `explicit_provable_type`), split `h_input` into `h_input_<f>` component equations,
  and value-replace them forward into every other hypothesis and the goal.

Known gaps (carried by the exemplars as marked manual blocks, to be absorbed here):
copy-equation landing at value level (`constrainEqual` facts) and the prover/verifier
whole-eval coincidence law for hint-free vars. Raw binds whose value IS used mint no
atom yet (none in the sample).
-/

open Lean Elab Tactic Meta

namespace Halo2

initialize registerTraceClass `Halo2.circuit_proof_start2

namespace CircuitProofStart2

open CircuitProofStart (bestEffort)

/-- Run a tactic given by syntax, best-effort; degraded steps are traced
(`set_option trace.Halo2.circuit_proof_start2 true`). -/
def run? (stx : TSyntax `tactic) : TacticM Unit := do
  let s ← saveState
  try evalTactic stx
  catch e =>
    trace[Halo2.circuit_proof_start2] "step degraded: {stx}\n{e.toMessageData}"
    s.restore

/-- The current type of the hypothesis named `n` (instantiated), or `none`. -/
def hypType? (n : Name) : TacticM (Option Expr) := withMainContext do
  let some decl := (← getLCtx).findFromUserName? n | return none
  instantiateMVars decl.type

/-- From a `Constraints place env ((body).operations i) i` /
`ExtendsWitnesses place env ((body).operations i) i` type, the `body` circuit term. -/
def bodyOfChunkType? (ty : Expr) : Option Expr := do
  -- Constraints/ExtendsWitnesses: (place) (env) (ops) (i) — ops = Circuit.operations … body i
  let args := ty.getAppArgs
  guard (args.size ≥ 2)
  let ops := args[args.size - 2]!
  guard (ops.isAppOfArity ``Halo2.Circuit.operations 5)
  return ops.getArg! 3

/-- Decompose a monadic bind application: `(x >>= f)` → `(x, f)`. -/
def bindParts? (body : Expr) : Option (Expr × Expr) :=
  if body.isAppOf ``Bind.bind then
    let args := body.getAppArgs
    if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none
  else none

/-- The do-binder name of the bind's continuation lambda (`x` fallback). -/
def binderNameOf (f : Expr) : Name :=
  match f with
  | .lam n .. => if n.isInternal then `x else n
  | _ => `x

/-- Whether the continuation actually uses its binder. -/
def binderUsed (f : Expr) : Bool :=
  match f with
  | .lam _ _ b _ => b.hasLooseBVar 0
  | _ => true

/-- Collect the closed canonical-output subterms of `e` not already equal to a local
atom (reuses the AbstractOutputs collector, filtered to `FormalCircuit.output` /
`FormalRegionCircuit.output` heads). -/
def newCanonicalOutputs (e : Expr) : TacticM (Array Expr) := withMainContext do
  let (_, outs) ← (AbstractOutputs.collectOutputs e).run #[]
  let mut fresh := #[]
  for o in outs do
    if AbstractOutputs.isCanonicalOutput o then
      -- skip if some hypothesis already defines this output as an atom
      if (← SubcircuitRw.findOutputLocal? o).isNone then
        fresh := fresh.push o
  return fresh

/-- Mint atoms for `outs` (innermost-first) with base name `n` (numbered `n`, `n_2`, …
on collisions/multiples): revert `hyps`, generalize, re-intro `hyps` in the SAME order.
The defining equations are named `h_<atom>`. -/
def mintAtoms (outs : Array Expr) (n : Name) (hyps : Array Name) : TacticM Unit := do
  if outs.isEmpty then return
  -- revert the carrier hypotheses (they hold the occurrences); reverse order so the
  -- FIRST listed hyp ends up outermost, matching the re-intro order below
  for h in hyps.reverse do
    run? (← `(tactic| revert $(mkIdent h):ident))
  withMainContext do
    let mut args : Array GeneralizeArg := #[]
    let lctx ← getLCtx
    let mut k := 0
    for o in outs do
      let base := if k == 0 then n else Name.mkSimple s!"{n}_{k+1}"
      let xn := if lctx.findFromUserName? base |>.isSome then
        Name.mkSimple s!"{base}'" else base
      args := args.push { expr := o, xName? := xn,
                          hName? := Name.mkSimple s!"h_{xn}" }
      k := k + 1
    let g ← getMainGoal
    let (_, g') ← g.generalize args
    replaceMainGoal [g']
  -- re-intro in list order (first listed = outermost binder)
  for h in hyps do
    run? (← `(tactic| intro $(mkIdent h):ident))

/-- One per-bind block. `sound := true` for the soundness direction. Returns `false`
when the chunk hypothesis no longer holds a bind (terminal reached). -/
def peelOneBind (sound : Bool) (chunkHyp : Name) (regionIdx : Nat) :
    TacticM (Option (Name × Bool)) := do
  let ty? ← hypType? chunkHyp
  let some ty := ty? | do
    trace[Halo2.circuit_proof_start2] "peel stop: no hyp {chunkHyp}"
    return none
  let some body := bodyOfChunkType? ty | do
    let opsHead := if _h : ty.getAppArgs.size ≥ 2 then
      toString (ty.getAppArgs[ty.getAppArgs.size-2]!.getAppFn.constName?) else "-"
    trace[Halo2.circuit_proof_start2]
      "peel stop: head={ty.getAppFn}, nargs={ty.getAppArgs.size}, opsHead={opsHead}"
    return none
  let some (x, f) := bindParts? body | do
    trace[Halo2.circuit_proof_start2] "peel stop: not a bind {body.getAppFn}"
    return none
  let nm := binderNameOf f
  let isCall := x.isAppOf ``Halo2.FormalCircuit.call
  let chunkName := if isCall then Name.mkSimple s!"h_call_{nm}"
    else Name.mkSimple s!"h_region_{regionIdx}"
  -- peel the constraint/witness/goal sides + the output side
  if sound then
    run? (← `(tactic| rw [Circuit.operations_bind, constraints_append]
      at $(mkIdent chunkHyp):ident))
  else
    run? (← `(tactic| rw [Circuit.operations_bind, extendsWitnesses_append]
      at $(mkIdent chunkHyp):ident))
    run? (← `(tactic| rw [Circuit.operations_bind, constraints_append]))
  run? (← `(tactic| rw [Circuit.output_bind] at $(mkIdent `h_output):ident))
  run? (← `(tactic| obtain ⟨$(mkIdent chunkName):ident, $(mkIdent chunkHyp):ident⟩
    := $(mkIdent chunkHyp):ident))
  -- canonicalize output spellings, then mint the atom for a used binder
  if sound then
    run? (← `(tactic| simp only [FormalCircuit.output_call']
      at $(mkIdent chunkHyp):ident $(mkIdent `h_output):ident))
  else
    run? (← `(tactic| simp only [FormalCircuit.output_call']
      at $(mkIdent chunkHyp):ident $(mkIdent `h_output):ident ⊢))
  if isCall && binderUsed f then
    let some ty' ← hypType? chunkHyp | return some (chunkName, isCall)
    let outs ← newCanonicalOutputs ty'
    mintAtoms outs nm #[chunkHyp, `h_output]
  -- fold the offsets
  if sound then
    run? (← `(tactic| simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount]
      at $(mkIdent chunkHyp):ident $(mkIdent `h_output):ident))
  else
    run? (← `(tactic| simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount]
      at $(mkIdent chunkHyp):ident $(mkIdent `h_output):ident ⊢))
  -- raw (non-call) chunks open immediately
  unless isCall do
    run? (← `(tactic| simp only [circuit_norm] at $(mkIdent chunkName):ident))
  return some (chunkName, isCall)

/-- The `Input` structure's field names, read off `input_var`'s type (default-
transparency whnf: the reducible `Var` alias and the `CircuitTypeOver.Var` projection
must both unfold to reach the structure head). -/
def inputFieldNames : TacticM (Array Name) := withMainContext do
  let some decl := (← getLCtx).findFromUserName? `input_var | return #[]
  let ty ← withTransparency .default <| whnf (← instantiateMVars decl.type)
  let .const structName _ := ty.getAppFn | return #[]
  unless isStructure (← getEnv) structName do return #[]
  return (getStructureFields (← getEnv) structName)

/-- Destructure the single-constructor value `nm` into components named
`<prefix>_<field>` (cases API — no rcases quotation). -/
def destructureInto (nm : Name) (pre : String) (fields : Array Name) : TacticM Unit := do
  if fields.isEmpty then return
  let names := fields.toList.map fun f => Name.mkSimple s!"{pre}_{f.getString!}"
  let s ← saveState
  try
    withMainContext do
      let some decl := (← getLCtx).findFromUserName? nm | failure
      -- expose the structure head definitionally so `cases` finds the inductive
      let ty ← withTransparency .default <| whnf (← instantiateMVars decl.type)
      liftMetaTactic fun g => do
        let g ← g.changeLocalDecl decl.fvarId ty
        pure [g]
      withMainContext do
        let some decl := (← getLCtx).findFromUserName? nm | failure
        liftMetaTactic fun g => do
          let subgoals ← g.cases decl.fvarId #[⟨true, names⟩]
          pure (subgoals.map (·.mvarId)).toList
  catch e =>
    trace[Halo2.circuit_proof_start2] "destructure {nm} failed: {e.toMessageData}"
    s.restore

/-- Split the (right-nested) conjunction `nm` into `n` components with the given names
(pairwise And-cases; the final residue takes the last name). -/
def splitConjInto (nm : Name) (names : Array Name) : TacticM Unit := do
  if names.isEmpty then return
  for i in [0:names.size - 1] do
    bestEffort <| withMainContext do
      let some decl := (← getLCtx).findFromUserName? nm | failure
      liftMetaTactic fun g => do
        let subgoals ← g.cases decl.fvarId #[⟨true, [names[i]!, nm]⟩]
        pure (subgoals.map (·.mvarId)).toList
  bestEffort <| withMainContext do
    let some decl := (← getLCtx).findFromUserName? nm | failure
    liftMetaTactic fun g => do
      pure [← g.rename decl.fvarId names.back!]

/-- The names of engine-emitted `h_spec_<k>` hypotheses currently in context. -/
def specHyps : TacticM (Array Name) := withMainContext do
  let mut out := #[]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && decl.userName.getString!.startsWith "h_spec_" then
      out := out.push decl.userName
  return out

/-- The v2 runner. -/
def run (sound : Bool) : TacticM Unit := do
  -- ── (a) intro the config through products; binder names come out of the pattern
  -- matches via the dsimp in (b), so positional names suffice here ──
  let mut guard := 0
  while guard < 8 do
    let ty ← withMainContext do instantiateMVars (← getMainTarget)
    if ty.isAppOf ``FormalCircuit.Soundness || ty.isAppOf ``FormalCircuit.Completeness then
      break
    unless ty.isForall do break
    run? (← `(tactic| intro $(mkIdent `cfg):ident))
    -- destructure through PRODUCTS only (a config tuple); never into structures
    let mut inner := 0
    while inner < 8 do
      let done ← withMainContext do
        let some decl := (← getLCtx).findFromUserName? `cfg | return true
        let cty ← whnfR (← instantiateMVars decl.type)
        if cty.isAppOf ``Prod then
          bestEffort <| liftMetaTactic fun g => do
            let subgoals ← g.cases decl.fvarId
              #[⟨true, [Name.mkSimple s!"cfg_{inner+1}", `cfg]⟩]
            pure (subgoals.map (·.mvarId)).toList
          return false
        return true
      if done then break
      inner := inner + 1
    guard := guard + 1
  if sound then
    run? (← `(tactic| rw [FormalCircuit.soundness_iff]))
    run? (← `(tactic| intro $(mkIdent `i₀):ident $(mkIdent `env):ident
      $(mkIdent `input_var):ident $(mkIdent `input):ident $(mkIdent `output):ident
      $(mkIdent `h_input):ident $(mkIdent `h_output):ident $(mkIdent `hE):ident
      $(mkIdent `hA):ident $(mkIdent `hC):ident))
  else
    run? (← `(tactic| rw [FormalCircuit.completeness_iff]))
    run? (← `(tactic| intro $(mkIdent `i₀):ident $(mkIdent `env):ident
      $(mkIdent `input_var):ident $(mkIdent `input):ident $(mkIdent `output):ident
      $(mkIdent `h_input):ident $(mkIdent `h_output):ident $(mkIdent `hW):ident
      $(mkIdent `hE):ident $(mkIdent `hA):ident $(mkIdent `hPA):ident))
  run? (← `(tactic| obtain ⟨$(mkIdent `place):ident, $(mkIdent `env):ident⟩
    := $(mkIdent `env):ident))
  -- ── (b) definitional cleanup + output landing ──
  run? (← `(tactic| dsimp only [] at *))
  run? (← `(tactic| simp only [ElaboratedCircuit.output_eq] at $(mkIdent `h_output):ident))
  -- ── (c) the bind loop ──
  let chunkHyp := if sound then `hC else `hW
  let mut callChunks : Array Name := #[]
  let mut regionIdx := 0
  for _ in [0:32] do
    match ← peelOneBind sound chunkHyp regionIdx with
    | some (nm, isCall) =>
      if isCall then callChunks := callChunks.push nm else regionIdx := regionIdx + 1
    | none => break
  -- ── (d) terminal pure ──
  if sound then
    run? (← `(tactic| rw [Circuit.operations_pure, constraints_nil]
      at $(mkIdent `hC):ident))
  else
    run? (← `(tactic| rw [Circuit.operations_pure, constraints_nil]))
  run? (← `(tactic| rw [Circuit.output_pure] at $(mkIdent `h_output):ident))
  run? (← `(tactic| clear $(mkIdent chunkHyp):ident))
  -- ── (e) engine ──
  if sound then
    for c in callChunks do
      run? (← `(tactic| subcircuit_rw at $(mkIdent c):ident))
  else
    run? (← `(tactic| subcircuit_rw))
  -- ── (f) value landing ──
  let fields ← inputFieldNames
  destructureInto `input_var "input_var" fields
  destructureInto `input "input" fields
  run? (← `(tactic| simp only [circuit_norm] at *))
  splitConjInto `h_input (fields.map fun f => Name.mkSimple s!"h_input_{f.getString!}")
  -- value replacement: land every input-var eval on its value name, at every
  -- hypothesis EXCEPT the component equations themselves (self-rewriting would
  -- collapse them to True) and the goal
  let compNames := fields.map fun f => Name.mkSimple s!"h_input_{f.getString!}"
  let comps ← compNames.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  let targets ← withMainContext do
    let mut ts : Array Ident := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless (decl.userName.isInternal || compNames.contains decl.userName) do
        if (← inferType (← instantiateMVars decl.type)).isProp then
          ts := ts.push (mkIdent decl.userName)
    pure ts
  run? (← `(tactic| simp only [$comps,*] at $[$targets:ident]* ⊢))

end CircuitProofStart2

/-- `circuit_proof_start2` — the atomic-binds (CPS v2) proof prefix. See the module
docstring and `Clean/Halo2/atomic-binds-design.md`. Direction auto-detected from the
goal head. Adopted per proof; the v1 `circuit_proof_start` is untouched. -/
syntax (name := circuitProofStart2) "circuit_proof_start2" : tactic

/-- Strip leading ∀ binders. -/
private partial def stripForalls (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => stripForalls b
  | e => e

@[tactic circuitProofStart2]
def evalCircuitProofStart2 : Tactic := fun _ => do
  -- detect the direction from the (possibly ∀-wrapped) goal head
  let ty ← withMainContext do instantiateMVars (← getMainTarget)
  let sound := !(stripForalls ty).isAppOf ``FormalCircuit.Completeness
  CircuitProofStart2.run sound

end Halo2
