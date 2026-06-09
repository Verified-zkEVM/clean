import Clean.Circuit.Explicit

open Lean Meta Elab Command

namespace Circuit.Witness

attribute [explicit_circuit_norm] Expression.eval

structure CompileState where
  offset : Expr
  env : Expr
  witnesses : Expr
  nextWitness : Nat := 0

def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | e => e

def mkWitnessGet (F : Expr) (state : CompileState) (idx : Expr) : MetaM Expr := do
  let zero ← mkAppOptM ``Zero.zero #[some F, none]
  mkAppM ``Array.getD #[state.witnesses, idx, zero]

def isStateEnvironment (state : CompileState) (env : Expr) : MetaM Bool := do
  if (← isDefEq env state.env) then
    return true
  let proverEnv ← mkAppM ``ProverEnvironment.toEnvironment #[state.env]
  isDefEq env proverEnv

partial def compileExpr (F : Expr) (state : CompileState) (e : Expr) : MetaM Expr := do
  let e := stripMData e
  if e.getAppFn.isConstOf ``Environment.get then
    let args := e.getAppArgs
    if args.size >= 3 then
      let env := args[1]!
      let idx := args[2]!
      if (← isStateEnvironment state env) then
        return ← mkWitnessGet F state idx
  match e with
  | .app f a =>
      return mkApp (← compileExpr F state f) (← compileExpr F state a)
  | .lam n t b bi =>
      withLocalDecl n bi (← compileExpr F state t) fun x => do
        let b := b.instantiate1 x
        mkLambdaFVars #[x] (← compileExpr F state b)
  | .forallE n t b bi =>
      withLocalDecl n bi (← compileExpr F state t) fun x => do
        let b := b.instantiate1 x
        mkForallFVars #[x] (← compileExpr F state b)
  | .letE n t v b nondep =>
      let t ← compileExpr F state t
      let v ← compileExpr F state v
      withLetDecl n t v fun x => do
        let b := b.instantiate1 x
        mkLetFVars #[x] (← compileExpr F state b) (usedLetOnly := nondep)
  | .mdata md b =>
      return .mdata md (← compileExpr F state b)
  | .proj n i b =>
      return .proj n i (← compileExpr F state b)
  | e => return e

def inlineWitnessCallback (F callback : Expr) (m : Expr) (state : CompileState) :
    MetaM (Expr × CompileState) := do
  let applied := mkApp callback state.env
  let body ← normalizeExplicitCircuitExpr applied
  let body ← compileExpr F state body
  let mVal? ← getNatValue? m
  let nextWitness := state.nextWitness + mVal?.getD 0
  return (body, { state with nextWitness })

partial def compileOperations (F ops : Expr) (state : CompileState) :
    MetaM (Array MessageData × CompileState) := do
  let ops ← whnf ops
  let ops := stripMData ops
  if ops.isAppOfArity ``List.nil 1 then
    return (#[], state)
  if ops.getAppFn.isConstOf ``List.cons then
    let args := ops.getAppArgs
    if args.size != 3 then
      throwError "unexpected List.cons shape:{indentExpr ops}"
    let op := args[1]!
    let tail := args[2]!
    let (msgs, state) ← compileOperation F op state
    let (tailMsgs, state) ← compileOperations F tail state
    return (msgs ++ tailMsgs, state)
  if ops.getAppFn.isConstOf ``List.append then
    let args := ops.getAppArgs
    if args.size != 3 then
      throwError "unexpected List.append shape:{indentExpr ops}"
    let (leftMsgs, state) ← compileOperations F args[1]! state
    let (rightMsgs, state) ← compileOperations F args[2]! state
    return (leftMsgs ++ rightMsgs, state)
  throwError "witness compiler does not yet understand operations expression:{indentExpr ops}"

where
  compileOperation (F op : Expr) (state : CompileState) :
      MetaM (Array MessageData × CompileState) := do
    let op ← whnf op
    let op := stripMData op
    if op.getAppFn.isConstOf ``Operation.witness then
      let args := op.getAppArgs
      let m := args[2]!
      let callback := args[3]!
      let start := state.nextWitness
      let (body, state) ← inlineWitnessCallback F callback m state
      return (#[m!"witness {start}: {body}"], state)
    if op.getAppFn.isConstOf ``Operation.assert ||
        op.getAppFn.isConstOf ``Operation.lookup ||
        op.getAppFn.isConstOf ``Operation.interact then
      return (#[], state)
    if op.getAppFn.isConstOf ``Operation.subcircuit then
      throwError "subcircuit witness compilation is not implemented yet:{indentExpr op}"
    throwError "witness compiler does not yet understand operation:{indentExpr op}"

def explicitOperationsOf (circuit offset : Expr) : TermElabM (Expr × Expr) := do
  let explicitType ← mkAppM ``ExplicitCircuit #[circuit]
  let explicit ← Lean.Elab.Term.elabTerm (← `(by infer_explicit_circuit)) (some explicitType)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let explicit ← instantiateMVars explicit
  let decls ← collectUnfoldableCircuitDecls explicit (← collectUnfoldableCircuitDecls circuit)
  let dsimpCtx ← mkExplicitCircuitDsimpContext decls
  let explicitMetadata := (← dsimp explicit dsimpCtx).1
  let ops ← mkAppOptM ``ExplicitCircuit.operations #[none, none, none, circuit, explicitMetadata, offset]
  let ops ← normalizeExplicitCircuitExpr ops decls
  return (ops, explicitMetadata)

syntax "#compile_witness " term : command

elab_rules : command
  | `(#compile_witness $circuitStx:term) => runTermElabM fun _ => do
      let circuit ← Lean.Elab.Term.elabTerm circuitStx none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let circuit ← instantiateMVars circuit
      let circuitType ← inferType circuit
      let some F := circuitType.getAppArgs[0]?
        | throwError "expected a Circuit term, got type:{indentExpr circuitType}"
      withLocalDeclD `offset (mkConst ``Nat) fun offset => do
        let (ops, _) ← explicitOperationsOf circuit offset
        withLocalDeclD `env (← mkAppM ``ProverEnvironment #[F]) fun env => do
        withLocalDeclD `witnesses (← mkAppM ``Array #[F]) fun witnesses => do
          let state : CompileState := { offset, env, witnesses }
          let (msgs, _) ← compileOperations F ops state
          logInfo m!"normalized operations:{indentExpr ops}"
          if msgs.isEmpty then
            logInfo "no witness operations found"
          else
            for msg in msgs do
              logInfo msg

end Circuit.Witness
