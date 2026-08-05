import Clean.Circuit.Explicit

/-!
# `computable_witnesses`

Automation for the common `FormalCircuitBase.ComputableWitnesses` proof shape.

The tactic uses controlled simp sets and unfolds only a `main` declaration in the current
scope; child subcircuit constants remain opaque, and their obligations are discharged
through the composition lemmas and `grind` rules in `Clean.Circuit.Subcircuit`.
-/

open Lean Meta Simp Elab Tactic

/-- Unfold circuit-valued wrapper definitions while respecting explicit-circuit boundaries. -/
elab "unfold_formal_circuit_consts" : tactic => do
  withMainContext do
    let noUnfold ← labelled `explicit_circuit_no_unfold
    let unfoldTypes ← labelled `explicit_circuit_unfold_type
    let names ← collectUnfoldableCircuitDecls (← getMainTarget) #[]
      (some noUnfold) (some unfoldTypes)
    for name in names do
      try
        evalTactic (← `(tactic| unfold $(mkIdent name)))
      catch _ =>
        pure ()

namespace ComputableWitnesses

/--
Split equalities between applications of the same structure constructor using the
constructor's generated `injEq` theorem. This is supplied only to the controlled simp
passes in `computable_witnesses`; it does not affect the global simp set.
-/
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
  try
    let params := lhs.getAppArgs[:info.numParams].toArray.map some
    let lhsFields := lhs.getAppArgs[info.numParams:].toArray.map some
    let rhsFields := rhs.getAppArgs[info.numParams:].toArray.map some
    let proof ← withTransparency .default <|
      mkAppOptM injEqName (params ++ lhsFields ++ rhsFields)
    let some (_, _, conjunction) := (← inferType proof).eq? | return .continue
    return .visit { expr := conjunction, proof? := some proof }
  catch _ =>
    return .continue

simproc structEqSplit (_ = _) := structEqSplitProc

/-- Heads under which concrete circuits' `localLength` metadata appears in
computable-witness goals. -/
private def localLengthHeads : List Name :=
  [`FormalCircuitBase.localLength, `ElaboratedCircuit.localLength,
   `Subcircuit.localLength, `Operations.localLength]

/-- Evaluate a closed ℕ-expression to a literal by whnf plus folding of `+`/`*`
(the shape `elaborate_circuit` leaves `localLength` metadata in). -/
private partial def natValOf (e : Expr) : MetaM (Option Nat) := do
  let e ← try whnf e catch _ => return none
  if let some k := e.rawNatLit? then return some k
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x + y)
  | HMul.hMul _ _ _ _ a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x * y)
  | Nat.add a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x + y)
  | Nat.mul a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x * y)
  | OfNat.ofNat _ k _ => natValOf k
  | _ => return none

/-- Assert `localLength = <numeral>` equations (definitional, by `rfl`) for every closed
`localLength` application in the goal. `Subcircuit`'s offset index makes these terms
unrewritable by `simp` in dependent positions; as hypotheses, `grind`'s arithmetic and
`omega` can bridge the offset spellings instead. -/
elab "assert_local_lengths" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let seen ← IO.mkRef ((∅ : Std.HashSet Expr))
  let eqs ← IO.mkRef (#[] : Array (Expr × Nat))
  tgt.forEach fun e => do
    let .const name _ := e.getAppFn | return ()
    unless localLengthHeads.contains name do return ()
    if e.hasLooseBVars || e.hasMVar then return ()
    if (← seen.get).contains e then return ()
    seen.modify (·.insert e)
    let some k ← try natValOf e catch _ => return () | return ()
    eqs.modify (·.push (e, k))
  let mut i := 0
  for (e, k) in (← eqs.get) do
    let eqType ← mkEq e (mkNatLit k)
    let proof ← mkExpectedTypeHint (← mkEqRefl e) eqType
    liftMetaTactic fun goal => do
      let goal ← goal.assert (Name.mkSimple s!"h_ll_{i}") eqType proof
      let (_, goal) ← goal.intro1P
      return [goal]
    i := i + 1

/-- Find a local variable of `ProvableStruct` type (e.g. an opaque circuit input) that can be
destructured: `simp`/`grind` do not iota-reduce the `match` coming from `main`'s destructuring
`let` against an opaque variable, so the tactic case-splits such variables up front. -/
private def findProvableStructVar : TacticM (Option FVarId) :=
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      -- `.instances` whnf, not `.reducible`: inputs are typed through the `Var M F` class
      -- projection, which does not reduce at reducible transparency
      let ty ← withTransparency .instances <| whnf (← instantiateMVars decl.type)
      let .const tyName _ := ty.getAppFn | continue
      unless isStructure (← getEnv) tyName do continue
      let args := ty.getAppArgs
      unless args.size ≥ 1 do continue
      let M := mkAppN ty.getAppFn args.pop
      let inst ← try? do
        synthInstance (← mkAppM ``ProvableStruct #[M])
      if inst.isSome then
        return some decl.fvarId
    return none

/-- Destructure all `ProvableStruct`-typed local variables (fixpoint, bounded). -/
private def destructureProvableStructVars : TacticM Unit := do
  for _ in [0:8] do
    if (← getGoals).isEmpty then return
    let some fvarId ← findProvableStructVar | return
    liftMetaTactic fun goal => do
      let subgoals ← goal.cases fvarId
      return subgoals.map (·.mvarId) |>.toList

private def runComputableWitnesses (extraTerms : Array (TSyntax `term)) : TacticM Unit := do
  let lemmasArray ← extraTerms.mapM fun term =>
    `(Lean.Parser.Tactic.simpLemma| $term:term)
  let simpPass : TacticM Unit := do
    unless (← getGoals).isEmpty do
      try
        evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
          ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      catch _ =>
        pure ()
  simpPass
  unless (← getGoals).isEmpty do
    try
      evalTactic (← `(tactic| unfold $(mkIdent `main):ident))
    catch _ =>
      pure ()
    simpPass
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| intros))
  destructureProvableStructVars
  simpPass
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| assert_local_lengths))
    -- Per-obligation closing ladder. The alternatives cover, in order: plain closes;
    -- subcircuit obligations via the offset-bridging composition rule (with child-output
    -- inputs assembled by `grind` from the tagged composition rules and `eval_mk` lemmas,
    -- elementwise vector reasoning as fallback); direct output-composition goals; and
    -- output metadata spelled as `varFromOffset` witness windows.
    let ofsEqId : Ident := mkIdent
      `FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
    let outEqId : Ident := mkIdent `FormalCircuit.output_of_input_eq
    let agLeId : Ident := mkIdent `ProverEnvironment.agreesBelow_of_le
    let gevId : Ident := mkIdent `getElem_eval_vector
    let evId : Ident := mkIdent `eval_vector
    let evfoId : Ident := mkIdent `ProvableType.eval_varFromOffset
    let ladder ← `(tactic|
      first
        | (simp_all; done)
        | grind
        | (intros
           refine $ofsEqId _
             (by first | rfl | omega | (assert_local_lengths; omega)) fun h_agrees => ?_
           simp_all only [circuit_norm, $lemmasArray,*]
           first
             | grind
             | (refine Vector.ext fun j hj => ?_
                simp only [$gevId:ident, Vector.getElem_map, Vector.getElem_append,
                  Vector.getElem_mapFinRange, Vector.getElem_ofFn]
                (try split_ifs) <;> grind [Vector.getElem_map, $gevId:ident])
             | grind [Vector.getElem_append, Vector.getElem_mapFinRange, Vector.getElem_map,
                 $gevId:ident]
             | refine $outEqId _ (by assumption)
                 ($agLeId (by assumption)
                   (by first | omega | (assert_local_lengths; omega))))
        | (intros
           refine $outEqId _ (by assumption) ?_
           first
             | assumption
             | exact $agLeId (by assumption)
                 (by first | omega | (assert_local_lengths; omega)))
        | (intros
           simp_all only [circuit_norm, $evId:ident, Vector.map_mk, List.map_toArray,
             List.map_cons, List.map_nil, $evfoId:ident, Vector.mapRange_succ,
             Vector.mapRange_zero, Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true,
             Vector.map_ofFn, Vector.ext_iff, Vector.getElem_ofFn, Function.comp_def,
             $lemmasArray,*]
           (try and_intros) <;> grind))
    withMainContext do
      -- syntactic head check: `whnf` on post-simp targets can blow the heartbeat budget
      -- (the And is exposed by the simp pass whenever it is going to be)
      let target := (← instantiateMVars (← getMainTarget)).consumeMData
      let closeTwo ← `(tacticSeq|
        refine ⟨?_, ?_⟩
        · intros
          (try and_intros) <;> $ladder:tactic
        · $ladder:tactic)
      if target.isAppOfArity ``And 2 then
        evalTacticSeq closeTwo
      else
        -- the ops/output conjunction can hide behind a definitionally-unfolding head;
        -- try the two-branch split first, fall back to the single ladder
        let s ← Tactic.saveState
        try
          evalTacticSeq closeTwo
        catch _ =>
          s.restore
          evalTactic ladder

/--
Prove the standard computable-witness obligation using a controlled normalization pass,
unfolding of the current `main` declaration (child subcircuit constants remain opaque),
structural splitting of the operations/output conjunction, and `grind`.

Extra simp lemmas may be supplied as `computable_witnesses [lemma₁, lemma₂]` — e.g. a child
bundle name to reduce its `output`/`localLength` metadata when witness expressions embed the
child's output under a binder, where `grind`'s E-matching cannot reach it.
-/
syntax "computable_witnesses" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses $[[$terms:term,*]]?) =>
      runComputableWitnesses (terms.map (fun terms => terms.getElems) |>.getD #[])

/-- Diagnostic variant of `computable_witnesses` without the `simp_all` fallback, so
`grind`'s failure state is visible. Not for committed proofs. -/
syntax "computable_witnesses_probe" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses_probe $[[$terms:term,*]]?) => do
      let lemmasArray ← (terms.map (fun terms => terms.getElems) |>.getD #[]).mapM fun term =>
        `(Lean.Parser.Tactic.simpLemma| $term:term)
      evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
        ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      try evalTactic (← `(tactic| unfold $(mkIdent `main):ident)) catch _ => pure ()
      evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
        ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      evalTactic (← `(tactic| intros))
      destructureProvableStructVars
      evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
        ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      evalTacticSeq (← `(tacticSeq|
        apply And.intro
        · intros
          (try and_intros) <;> grind
        · grind))

end ComputableWitnesses
