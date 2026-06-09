import Clean.Circuit.Extensions

register_option debug.compileWitness : Bool := {
  defValue := false
  descr := "print normalized operations and generated declarations from compile_witness"
}

@[circuit_norm]
def FormalCircuitBase.instantiate {F : Type} [Field F] {Input Output : TypeMap}
    [ProvableType Input] [CircuitType Output]
    (circuit : FormalCircuitBase F Input Output) : Circuit F Unit := do
  let input ← witnessAny Input
  let _ ← circuit.main input
  return ()

open Lean Meta Elab Command

namespace Circuit.Witness

attribute [explicit_circuit_norm] Expression.eval
attribute [explicit_circuit_norm] CircuitType.eval_expr CircuitType.eval_expr_prover
attribute [explicit_circuit_norm] CircuitType.eval_var_field CircuitType.eval_var_field_prover
attribute [explicit_circuit_norm] CircuitType.eval_fields_dispatch CircuitType.eval_fields_dispatch_prover
attribute [explicit_circuit_norm] ProvableType.eval_fieldPair ProvableType.eval_fieldPair_prover
attribute [explicit_circuit_norm] ProvableStruct.eval_eq_eval ProvableStruct.eval_eq_eval_prover
attribute [explicit_circuit_norm] valueFromOffset ProvableType.varFromOffset
attribute [explicit_circuit_norm] Function.comp_apply
attribute [explicit_circuit_norm] ProvableType.toElements_fromElements ProvableType.fromElements_toElements
attribute [explicit_circuit_norm] ProvableStruct.components ProvableStruct.combinedSize
  ProvableStruct.combinedSize'
attribute [explicit_circuit_norm] List.map_cons List.map_nil List.sum_cons List.sum_nil
attribute [explicit_circuit_norm] Array.emptyWithCapacity Array.toList_empty Array.toList_push
  List.concat_eq_append List.nil_append List.append_nil List.cons_append
attribute [explicit_circuit_norm] Vector.getElem_map Vector.getElem_mapRange Vector.getElem_cast
  Vector.getElem_push Vector.getElem_set
attribute [explicit_circuit_norm] Nat.cast_zero Nat.cast_one
attribute [explicit_circuit_norm] add_zero zero_add
attribute [explicit_circuit_norm] Nat.succ_eq_add_one
attribute [explicit_circuit_norm] Circuit.localLength Operation.localLength Operations.localLength

@[explicit_circuit_norm]
theorem toElements_fields {F : Type} {n : ℕ} (x : fields n F) :
    @toElements (fields n) (inferInstance : ProvableType (fields n)) F x = x := rfl

@[explicit_circuit_norm]
theorem fromElements_fields {F : Type} {n : ℕ} (x : Vector F n) :
    @fromElements (fields n) (inferInstance : ProvableType (fields n)) F x = x := rfl

@[explicit_circuit_norm]
lemma field_fromElements_mapRange_one {F : Type} (f : ℕ → F) :
    (fromElements (M:=field) (Vector.mapRange 1 f) : F) = f 0 := by
  change (Vector.mapRange 1 f)[0] = f 0
  rw [Vector.getElem_mapRange]

@[explicit_circuit_norm]
lemma vector_mapRange_one_field_match {F : Type} (f : ℕ → F) :
    (match Vector.mapRange 1 f with
     | Vector.mk { toList := [x] } _ => x) = f 0 := by
  change (Vector.mapRange 1 f)[0] = f 0
  rw [Vector.getElem_mapRange]

@[explicit_circuit_norm]
lemma fieldPair_fromElements_mapRange_one {F : Type} (f : ℕ → F) :
    (fromElements (M:=fieldPair) (Vector.mapRange 2 f) : F × F).1 = f 0 := by
  change (Vector.mapRange 2 f)[0] = f 0
  rw [Vector.getElem_mapRange]

@[explicit_circuit_norm]
lemma fieldPair_fromElements_mapRange_two {F : Type} (f : ℕ → F) :
    (fromElements (M:=fieldPair) (Vector.mapRange 2 f) : F × F).2 = f 1 := by
  change (Vector.mapRange 2 f)[1] = f 1
  rw [Vector.getElem_mapRange]

@[explicit_circuit_norm]
lemma fieldTriple_fromElements_mapRange_one {F : Type} (f : ℕ → F) :
    (fromElements (M:=fieldTriple) (Vector.mapRange 3 f) : F × F × F).1 = f 0 := by
  change (Vector.mapRange 3 f)[0] = f 0
  rw [Vector.getElem_mapRange]

@[explicit_circuit_norm]
lemma fieldTriple_fromElements_mapRange_two {F : Type} (f : ℕ → F) :
    (fromElements (M:=fieldTriple) (Vector.mapRange 3 f) : F × F × F).2.1 = f 1 := by
  change (Vector.mapRange 3 f)[1] = f 1
  rw [Vector.getElem_mapRange]

@[explicit_circuit_norm]
lemma fieldTriple_fromElements_mapRange_three {F : Type} (f : ℕ → F) :
    (fromElements (M:=fieldTriple) (Vector.mapRange 3 f) : F × F × F).2.2 = f 2 := by
  change (Vector.mapRange 3 f)[2] = f 2
  rw [Vector.getElem_mapRange]

@[explicit_circuit_constructor]
instance ExplicitCircuit.from_getOffset {F : Type} [Field F] : ExplicitCircuit (getOffset (F:=F)) where
  output n := n
  localLength _ := 0
  operations _ := []
  channelsWithGuarantees _ := []
  channelsWithRequirements _ := []

@[explicit_circuit_constructor]
instance ExplicitCircuit.from_witnessAny {F : Type} [Field F] {M : TypeMap} [ProvableType M] :
    ExplicitCircuit (witnessAny (F:=F) M) where
  output n := varFromOffset M n
  localLength _ := size M
  operations n := [.witness (size M) (fun env => toElements (valueFromOffset M n env))]
  channelsWithGuarantees _ := []
  channelsWithRequirements _ := []
  output_eq n := by simp only [witnessAny_output]
  localLength_eq n := by
    simp [Circuit.localLength, Circuit.bind_def, witnessAny, getOffset,
      ProvableType.witness, Operations.localLength]
  operations_eq n := by
    simp [Circuit.operations, Circuit.bind_def, witnessAny, getOffset, ProvableType.witness]

structure CompileState where
  offset : Expr
  env : Expr
  witnesses : Expr
  localLength? : Option Expr := none
  bound? : Option Expr := none
  nextWitness : Nat := 0

def stripMData : Expr → Expr
  | .mdata _ e => stripMData e
  | e => e

def mkArraySize (xs : Expr) : MetaM Expr :=
  mkAppM ``Array.size #[xs]

def mkBoundType (offset localLength witnesses : Expr) : MetaM Expr := do
  let endIdx ← mkAppM ``HAdd.hAdd #[offset, localLength]
  let size ← mkArraySize witnesses
  mkAppM ``LT.lt #[endIdx, size]

def mkGetElemProof (idx witnesses : Expr) : TermElabM Expr := do
  let size ← mkArraySize witnesses
  let expected ← mkAppM ``LT.lt #[idx, size]
  let mkProof (stx : Term) : TermElabM Expr := do
    let proof ← Lean.Elab.Term.elabTerm stx (some expected)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars proof
  try
    mkProof (← `(by get_elem_tactic))
  catch _ =>
    mkProof (← `(by omega))

def mkWitnessGet (F : Expr) (state : CompileState) (idx : Expr) : TermElabM Expr := do
  if state.bound?.isSome then
    let proof ← mkGetElemProof idx state.witnesses
    let arrayF ← mkAppM ``Array #[F]
    let valid ←
      withLocalDeclD `xs arrayF fun xs => do
      withLocalDeclD `i (mkConst ``Nat) fun i => do
        let size ← mkArraySize xs
        let body ← mkAppM ``LT.lt #[i, size]
        mkLambdaFVars #[xs, i] body
    let value ← mkAppOptM ``GetElem.getElem
      #[some arrayF, some (mkConst ``Nat), some F, some valid, none,
        some state.witnesses, some idx, some proof]
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  else
    let zero ← mkAppOptM ``OfNat.ofNat #[some F, some (mkRawNatLit 0), none]
    mkAppM ``Array.getD #[state.witnesses, idx, zero]

partial def normalizeNatIndex (idx : Expr) : MetaM Expr := do
  let idx ← withTransparency .all <| whnf idx
  let idx ← normalizeExplicitCircuitExpr idx
  let idx ← withTransparency .all <| whnf idx
  let idx := stripMData idx
  if idx.getAppFn.isConstOf ``Nat.succ then
    let args := idx.getAppArgs
    if args.size == 1 then
      return ← mkAppM ``HAdd.hAdd #[← normalizeNatIndex args[0]!, mkNatLit 1]
  if idx.getAppFn.isConstOf ``Nat.add then
    let args := idx.getAppArgs
    if args.size == 2 then
      let lhs ← normalizeNatIndex args[0]!
      let rhs ← normalizeNatIndex args[1]!
      if let some 0 ← getNatValue? rhs then
        return lhs
      if let some 0 ← getNatValue? lhs then
        return rhs
      return ← mkAppM ``HAdd.hAdd #[lhs, rhs]
  return idx

def isStateEnvironment (state : CompileState) (env : Expr) : MetaM Bool := do
  if (← isDefEq env state.env) then
    return true
  let proverEnv ← mkAppM ``ProverEnvironment.toEnvironment #[state.env]
  isDefEq env proverEnv

mutual

partial def compileExpressionEval (F : Expr) (state : CompileState) (expr : Expr) : TermElabM Expr := do
  let expr ← withTransparency .all <| whnf expr
  let expr ← normalizeExplicitCircuitExpr expr
  let expr ← withTransparency .all <| whnf expr
  let expr := stripMData expr
  if expr.getAppFn.isConstOf ``Expression.var then
    let args := expr.getAppArgs
    if args.size >= 2 then
      let idx ← mkAppM ``Variable.index #[args[1]!]
      let idx ← normalizeNatIndex idx
      return ← mkWitnessGet F state idx
  if expr.getAppFn.isConstOf ``Expression.const then
    let args := expr.getAppArgs
    if args.size >= 2 then
      return ← compileExpr F state args[1]!
  if expr.getAppFn.isConstOf ``Expression.add then
    let args := expr.getAppArgs
    if args.size >= 3 then
      let lhs ← compileExpressionEval F state args[1]!
      let rhs ← compileExpressionEval F state args[2]!
      return ← mkAppM ``HAdd.hAdd #[lhs, rhs]
  if expr.getAppFn.isConstOf ``Expression.mul then
    let args := expr.getAppArgs
    if args.size >= 3 then
      let lhs ← compileExpressionEval F state args[1]!
      let rhs ← compileExpressionEval F state args[2]!
      return ← mkAppM ``HMul.hMul #[lhs, rhs]
  throwError "witness compiler cannot compile expression evaluation:{indentExpr expr}"

partial def compileExpr (F : Expr) (state : CompileState) (e : Expr) : TermElabM Expr := do
  let e := stripMData e
  if e.getAppFn.isConstOf ``Expression.eval then
    let args := e.getAppArgs
    if args.size >= 4 then
      let env := args[2]!
      let expr := args[3]!
      if (← isStateEnvironment state env) then
        return ← compileExpressionEval F state expr
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

end

def inlineWitnessCallbackBody (callback : Expr) (state : CompileState) : MetaM Expr := do
  normalizeExplicitCircuitExpr (mkApp callback state.env)

def inlineWitnessCallback (F callback : Expr) (m : Expr) (state : CompileState) :
    TermElabM (Expr × CompileState) := do
  let body ← inlineWitnessCallbackBody callback state
  let body ← compileExpr F state body
  let mVal? ← getNatValue? m
  let nextWitness := state.nextWitness + mVal?.getD 0
  return (body, { state with nextWitness })

def mkWriteIndex (offset : Expr) (cursor i : Nat) : MetaM Expr := do
  let k := cursor + i
  if k == 0 then
    return offset
  else
    mkAppM ``HAdd.hAdd #[offset, mkNatLit k]

def mkVectorGetD (F body : Expr) (i : Nat) : MetaM Expr := do
  let zero ← mkAppOptM ``OfNat.ofNat #[some F, some (mkRawNatLit 0), none]
  mkAppOptM ``Vector.getD #[some F, none, body, some (mkNatLit i), zero]

def mkVectorGet (F body m : Expr) (i : Nat) : TermElabM Expr := do
  let idx := mkNatLit i
  let expected ← mkAppM ``LT.lt #[idx, m]
  let proof ← Lean.Elab.Term.elabTerm (← `(by get_elem_tactic)) (some expected)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let vectorType ← inferType body
  let valid ←
    withLocalDeclD `xs vectorType fun xs => do
    withLocalDeclD `i (mkConst ``Nat) fun i => do
      let body ← mkAppM ``LT.lt #[i, m]
      mkLambdaFVars #[xs, i] body
  let value ← mkAppOptM ``GetElem.getElem
    #[some vectorType, some (mkConst ``Nat), some F, some valid, none,
      some body, some idx, some proof]
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

def mkVectorGetElem (elemType body m : Expr) (i : Nat) : TermElabM Expr := do
  let idx := mkNatLit i
  let expected ← mkAppM ``LT.lt #[idx, m]
  let proof ← Lean.Elab.Term.elabTerm (← `(by get_elem_tactic)) (some expected)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let proof ← instantiateMVars proof
  let vectorType ← inferType body
  let valid ←
    withLocalDeclD `xs vectorType fun xs => do
    withLocalDeclD `i (mkConst ``Nat) fun i => do
      let body ← mkAppM ``LT.lt #[i, m]
      mkLambdaFVars #[xs, i] body
  let value ← mkAppOptM ``GetElem.getElem
    #[some vectorType, some (mkConst ``Nat), some elemType, some valid, none,
      some body, some idx, some proof]
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

mutual

partial def listLength? (xs : Expr) : MetaM (Option Nat) := do
  let xs ← whnf xs
  let xs := stripMData xs
  if xs.isAppOfArity ``List.nil 1 then
    return some 0
  else if xs.getAppFn.isConstOf ``List.cons then
    let args := xs.getAppArgs
    if args.size == 3 then
      return (· + 1) <$> (← listLength? args[2]!)
    else
      return none
  else if xs.getAppFn.isConstOf ``List.concat then
    let args := xs.getAppArgs
    if args.size == 3 then
      return (· + 1) <$> (← listLength? args[1]!)
    else
      return none
  else if xs.getAppFn.isConstOf ``List.append then
    let args := xs.getAppArgs
    if args.size == 3 then
      match ← listLength? args[1]!, ← listLength? args[2]! with
      | some left, some right => return some (left + right)
      | _, _ => return none
    else
      return none
  else if xs.getAppFn.isConstOf ``Array.toList then
    let args := xs.getAppArgs
    if args.size == 2 then
      let array ← whnf args[1]!
      let array := stripMData array
      if array.getAppFn.isConstOf ``Array.emptyWithCapacity then
        return some 0
    return none
  else
    return none

partial def nthListElement? (xs : Expr) (i : Nat) : MetaM (Option Expr) := do
  let xs ← whnf xs
  let xs := stripMData xs
  if xs.getAppFn.isConstOf ``List.cons then
    let args := xs.getAppArgs
    if args.size == 3 then
      if i == 0 then
        return some args[1]!
      else
        nthListElement? args[2]! (i - 1)
    else
      return none
  else if xs.getAppFn.isConstOf ``List.concat then
    let args := xs.getAppArgs
    if args.size == 3 then
      match ← listLength? args[1]! with
      | some prefixLen =>
          if i < prefixLen then
            nthListElement? args[1]! i
          else if i == prefixLen then
            return some args[2]!
          else
            return none
      | none => return none
    else
      return none
  else if xs.getAppFn.isConstOf ``List.append then
    let args := xs.getAppArgs
    if args.size == 3 then
      match ← listLength? args[1]! with
      | some prefixLen =>
          if i < prefixLen then
            nthListElement? args[1]! i
          else
            nthListElement? args[2]! (i - prefixLen)
      | none => return none
    else
      return none
  else
    return none

end

def nthArrayLiteralElement? (xs : Expr) (i : Nat) : MetaM (Option Expr) := do
  let xs ← whnf xs
  let xs ← normalizeExplicitCircuitExpr xs
  let xs ← whnf xs
  let xs := stripMData xs
  if xs.getAppFn.isConstOf ``Array.mk then
    let args := xs.getAppArgs
    if args.size == 2 then
      nthListElement? args[1]! i
    else
      return none
  else if xs.getAppFn.isConstOf ``List.toArray then
    let args := xs.getAppArgs
    if args.size == 2 then
      nthListElement? args[1]! i
    else
      return none
  else
    return none

partial def compileVectorElement (F body : Expr) (i : Nat) : TermElabM Expr := do
  let raw := stripMData body
  if raw.getAppFn.isConstOf ``Vector.mapRange then
    let args := raw.getAppArgs
    if args.size == 3 then
      return ← normalizeExplicitCircuitExpr (mkApp args[2]! (mkNatLit i))
  if raw.getAppFn.isConstOf ``Vector.map then
    let args := raw.getAppArgs
    if args.size == 5 then
      let elem ← compileVectorElement args[0]! args[4]! i
      return ← normalizeExplicitCircuitExpr (mkApp args[3]! elem)
  let body ← withTransparency .all <| whnf body
  let body ← normalizeExplicitCircuitExpr body
  let body ← withTransparency .all <| whnf body
  let body := stripMData body
  if body.getAppFn.isConstOf ``Vector.mk then
    let args := body.getAppArgs
    if args.size == 4 then
      if let some elem ← nthArrayLiteralElement? args[2]! i then
        return elem
      let array ← withTransparency .all <| whnf args[2]!
      let array := stripMData array
      if array.getAppFn.isConstOf ``Array.map then
        let mapArgs := array.getAppArgs
        if mapArgs.size == 4 then
          let source ← withTransparency .all <| whnf mapArgs[3]!
          let source := stripMData source
          if source.getAppFn.isConstOf ``Vector.toArray then
            let sourceArgs := source.getAppArgs
            if sourceArgs.size == 3 then
              let elem ← compileVectorElement mapArgs[0]! sourceArgs[2]! i
              return ← normalizeExplicitCircuitExpr (mkApp mapArgs[2]! elem)
      return ← mkVectorGetElem args[0]! body args[1]! i
  if body.getAppFn.isConstOf ``Vector.mapRange then
    let args := body.getAppArgs
    if args.size == 3 then
      return ← normalizeExplicitCircuitExpr (mkApp args[2]! (mkNatLit i))
  if body.getAppFn.isConstOf ``Vector.map then
    let args := body.getAppArgs
    if args.size == 5 then
      let elem ← mkVectorGetElem args[0]! args[4]! args[2]! i
      return ← normalizeExplicitCircuitExpr (mkApp args[3]! elem)
  mkVectorGetD F body i

partial def canCompileVectorElementsDirect (body : Expr) (_len : Nat) : MetaM Bool := do
  let body ← withTransparency .all <| whnf body
  let body ← normalizeExplicitCircuitExpr body
  let body ← withTransparency .all <| whnf body
  let body := stripMData body
  if body.getAppFn.isConstOf ``Vector.mapRange then
    return true
  if body.getAppFn.isConstOf ``Vector.map then
    return true
  if body.getAppFn.isConstOf ``Vector.mk then
    let args := body.getAppArgs
    if args.size == 4 then
      return true
  return false

def mkCheckedArraySet (state : CompileState) (current idx value : Expr) : TermElabM (Expr × Option Expr) := do
  if state.bound?.isSome then
    let proof ← mkGetElemProof idx current
    let assigned ← mkAppM ``Array.set #[current, idx, value, proof]
    return (assigned, some proof)
  else
    return (← mkAppM ``Array.set! #[current, idx, value], none)

def mkUpdatedBoundProof (endIdx current idx value _next setProof oldProof : Expr) : MetaM Expr := do
  let valueType ← inferType value
  let sizeEq ← mkAppOptM ``Array.size_set
    #[some valueType, some current, some idx, some value, some setProof]
  let motive ←
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      let body ← mkAppM ``LT.lt #[endIdx, n]
      mkLambdaFVars #[n] body
  let propEq ← mkAppM ``congrArg #[motive, sizeEq]
  mkEqMPR propEq oldProof

partial def compileWitnessSetters (F callback m : Expr) (state : CompileState) (current : Expr)
    (k : Expr → CompileState → TermElabM Expr) : TermElabM Expr := do
  let m ← normalizeExplicitCircuitExpr m
  let some len ← getNatValue? m
    | throwError "witness compiler cannot generate setters for non-static witness length:{indentExpr m}"
  let readState := { state with witnesses := current }
  let body ← inlineWitnessCallbackBody callback readState
  let direct ← canCompileVectorElementsDirect body len
  let rec loop (body : Expr) (readState : CompileState) (i : Nat) (state : CompileState)
      (current : Expr) : TermElabM Expr := do
    if i == len then
      k current state
    else
      let value ← compileVectorElement F body i
      let value ← normalizeExplicitCircuitExpr value
      let value ← compileExpr F readState value
      let value ← normalizeExplicitCircuitExpr value
      let idx ← mkWriteIndex state.offset state.nextWitness 0
      let (assigned, setProof?) ← mkCheckedArraySet state current idx value
      withLetDecl `witnesses (← inferType assigned) assigned fun next => do
        match state.localLength?, state.bound?, setProof? with
        | some localLength, some oldBound, some setProof =>
            let boundType ← mkBoundType state.offset localLength next
            let endIdx ← mkAppM ``HAdd.hAdd #[state.offset, localLength]
            let boundProof ← mkUpdatedBoundProof endIdx current idx value next setProof oldBound
            withLetDecl `h boundType boundProof fun h => do
              let body ← loop body readState (i + 1)
                { state with witnesses := next, bound? := some h, nextWitness := state.nextWitness + 1 } next
              mkLetFVars #[next, h] body
        | _, _, _ =>
            let body ← loop body readState (i + 1)
              { state with witnesses := next, nextWitness := state.nextWitness + 1 } next
            mkLetFVars #[next] body
  if direct then
    loop body readState 0 state current
  else
    let body ← compileExpr F readState body
    let body ← normalizeExplicitCircuitExpr body
    withLetDecl `witnessValues (← inferType body) body fun witnessValues => do
      let rec loopBound (i : Nat) (state : CompileState) (current : Expr) : TermElabM Expr := do
        if i == len then
          k current state
        else
          let value ← mkVectorGet F witnessValues m i
          let idx ← mkWriteIndex state.offset state.nextWitness 0
          let (assigned, setProof?) ← mkCheckedArraySet state current idx value
          withLetDecl `witnesses (← inferType assigned) assigned fun next => do
            match state.localLength?, state.bound?, setProof? with
            | some localLength, some oldBound, some setProof =>
                let boundType ← mkBoundType state.offset localLength next
                let endIdx ← mkAppM ``HAdd.hAdd #[state.offset, localLength]
                let boundProof ← mkUpdatedBoundProof endIdx current idx value next setProof oldBound
                withLetDecl `h boundType boundProof fun h => do
                  let body ← loopBound (i + 1)
                    { state with witnesses := next, bound? := some h, nextWitness := state.nextWitness + 1 } next
                  mkLetFVars #[next, h] body
            | _, _, _ =>
                let body ← loopBound (i + 1)
                  { state with witnesses := next, nextWitness := state.nextWitness + 1 } next
                mkLetFVars #[next] body
      let result ← loopBound 0 state current
      mkLetFVars #[witnessValues] result

def explicitCircuitDataOf (circuit offset : Expr) : TermElabM (Expr × Expr × Expr) := do
  let explicitType ← mkAppM ``ExplicitCircuit #[circuit]
  let explicit ← Lean.Elab.Term.elabTerm (← `(by infer_explicit_circuit)) (some explicitType)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let explicit ← instantiateMVars explicit
  let decls ← collectUnfoldableCircuitDecls explicit (← collectUnfoldableCircuitDecls circuit)
  let dsimpCtx ← mkExplicitCircuitDsimpContext decls
  let explicitMetadata := (← dsimp explicit dsimpCtx).1
  let localLength ← mkAppOptM ``ExplicitCircuit.localLength #[none, none, none, circuit, explicitMetadata, offset]
  let localLength ← normalizeExplicitCircuitExpr localLength decls
  let ops ← mkAppOptM ``ExplicitCircuit.operations #[none, none, none, circuit, explicitMetadata, offset]
  let ops ← normalizeExplicitCircuitExpr ops decls
  return (ops, explicitMetadata, localLength)

def explicitOperationsOf (circuit offset : Expr) : TermElabM (Expr × Expr) := do
  let (ops, metadata, _) ← explicitCircuitDataOf circuit offset
  return (ops, metadata)

structure WitnessTarget where
  F : Expr
  dataOf : Expr → TermElabM (Expr × Expr)

def circuitWitnessTarget (circuit F : Expr) : WitnessTarget where
  F := F
  dataOf offset := do
    let (ops, _, localLength) ← explicitCircuitDataOf circuit offset
    return (ops, localLength)

def normalizedCircuitOperationsOf (circuit offset : Expr) (extraDeclSeed? : Option Expr := none) : TermElabM Expr := do
  let ops ← mkAppOptM ``Circuit.operations #[none, none, none, circuit, offset]
  let ops ← withTransparency .all <| whnf ops
  let decls ←
    match extraDeclSeed? with
    | some seed => collectUnfoldableCircuitDecls circuit (← collectUnfoldableCircuitDecls seed)
    | none => collectUnfoldableCircuitDecls circuit
  let decls ← collectUnfoldableCircuitDecls ops decls
  normalizeExplicitCircuitExpr ops decls

def normalizedCircuitLocalLengthOf (circuit offset : Expr) (extraDeclSeed? : Option Expr := none) :
    TermElabM Expr := do
  let localLength ← mkAppOptM ``Circuit.localLength #[none, none, none, circuit, offset]
  let localLength ← withTransparency .all <| whnf localLength
  let decls ←
    match extraDeclSeed? with
    | some seed => collectUnfoldableCircuitDecls circuit (← collectUnfoldableCircuitDecls seed)
    | none => collectUnfoldableCircuitDecls circuit
  let decls ← collectUnfoldableCircuitDecls localLength decls
  normalizeExplicitCircuitExpr localLength decls

def formalCircuitBaseOperations (base input offset : Expr) : TermElabM Expr := do
  let main ← mkAppM ``FormalCircuitBase.main #[base, input]
  normalizedCircuitOperationsOf main offset (some base)

def formalCircuitBaseLocalLength (base input offset : Expr) : TermElabM Expr := do
  let main ← mkAppM ``FormalCircuitBase.main #[base, input]
  normalizedCircuitLocalLengthOf main offset (some base)

def formalCircuitBaseWitnessTarget (base F Input : Expr) : WitnessTarget where
  F := F
  dataOf offset := do
    let inputCircuit ← mkAppOptM ``witnessAny #[some F, none, some Input, none]
    let (inputOps, _, inputLocalLength) ← explicitCircuitDataOf inputCircuit offset
    let inputVar ← mkAppOptM ``varFromOffset #[some F, some Input, none, some offset]
    let mainOffset ← mkAppM ``HAdd.hAdd #[offset, inputLocalLength]
    let mainOps ← formalCircuitBaseOperations base inputVar mainOffset
    let mainLocalLength ← formalCircuitBaseLocalLength base inputVar mainOffset
    let ops ← mkAppM ``List.append #[inputOps, mainOps]
    let ops ← normalizeExplicitCircuitExpr ops
    let localLength ← mkAppM ``HAdd.hAdd #[inputLocalLength, mainLocalLength]
    let localLength ← normalizeExplicitCircuitExpr localLength
    return (ops, localLength)

def subcircuitOperations (s : Expr) : TermElabM Expr := do
  let s := stripMData s
  let args := s.getAppArgs
  if args.size < 3 then
    throwError "unexpected subcircuit expression:{indentExpr s}"
  let circuit := args[args.size - 3]!
  let offset := args[args.size - 2]!
  let input := args[args.size - 1]!
  if s.getAppFn.isConstOf ``FormalCircuit.toSubcircuit then
    let base ← mkAppM ``FormalCircuit.base #[circuit]
    formalCircuitBaseOperations base input offset
  else if s.getAppFn.isConstOf ``FormalAssertion.toSubcircuit then
    let base ← mkAppM ``FormalAssertion.base #[circuit]
    formalCircuitBaseOperations base input offset
  else if s.getAppFn.isConstOf ``GeneralFormalCircuit.toSubcircuit then
    let base ← mkAppM ``GeneralFormalCircuit.base #[circuit]
    formalCircuitBaseOperations base input offset
  else if s.getAppFn.isConstOf ``GeneralFormalCircuit.WithHint.toSubcircuit then
    let base ← mkAppM ``GeneralFormalCircuit.WithHint.base #[circuit]
    formalCircuitBaseOperations base input offset
  else
    throwError "witness compiler only supports formal-circuit subcircuits, got:{indentExpr s}"

partial def compileOperations (F ops : Expr) (state : CompileState) :
    TermElabM (Array MessageData × CompileState) := do
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
      TermElabM (Array MessageData × CompileState) := do
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
      let args := op.getAppArgs
      let ops ← subcircuitOperations args[3]!
      return ← compileOperations F ops state
    throwError "witness compiler does not yet understand operation:{indentExpr op}"

partial def compileOperationsToArray (F ops : Expr) (state : CompileState) (current : Expr)
    (k : Expr → CompileState → TermElabM Expr) : TermElabM Expr := do
  let ops ← whnf ops
  let ops := stripMData ops
  if ops.isAppOfArity ``List.nil 1 then
    return ← k current state
  if ops.getAppFn.isConstOf ``List.cons then
    let args := ops.getAppArgs
    if args.size != 3 then
      throwError "unexpected List.cons shape:{indentExpr ops}"
    let op := args[1]!
    let tail := args[2]!
    return ← compileOperationToArray F op state current fun current state =>
      compileOperationsToArray F tail state current k
  else if ops.getAppFn.isConstOf ``List.append then
    let args := ops.getAppArgs
    if args.size != 3 then
      throwError "unexpected List.append shape:{indentExpr ops}"
    return ← compileOperationsToArray F args[1]! state current fun current state =>
      compileOperationsToArray F args[2]! state current k
  else
    throwError "witness compiler does not yet understand operations expression:{indentExpr ops}"

where
  compileOperationToArray (F op : Expr) (state : CompileState) (current : Expr)
      (k : Expr → CompileState → TermElabM Expr) : TermElabM Expr := do
    let op ← whnf op
    let op := stripMData op
    if op.getAppFn.isConstOf ``Operation.witness then
      let args := op.getAppArgs
      compileWitnessSetters F args[3]! args[2]! state current k
    else if op.getAppFn.isConstOf ``Operation.assert ||
        op.getAppFn.isConstOf ``Operation.lookup ||
        op.getAppFn.isConstOf ``Operation.interact then
      k current state
    else if op.getAppFn.isConstOf ``Operation.subcircuit then
      let args := op.getAppArgs
      let ops ← subcircuitOperations args[3]!
      compileOperationsToArray F ops state current k
    else
      throwError "witness compiler does not yet understand operation:{indentExpr op}"

def circuitField? (type : Expr) : MetaM (Option Expr) := do
  let type ← instantiateMVars type
  if type.getAppFn.isConstOf ``Circuit then
    return type.getAppArgs[0]?
  return none

def formalBaseInput? (base : Expr) : TermElabM (Option (Expr × Expr)) := do
  let baseType ← instantiateMVars (← inferType base)
  if baseType.getAppFn.isConstOf ``FormalCircuitBase then
    let args := baseType.getAppArgs
    if args.size >= 3 then
      return some (args[0]!, args[1]!)
  return none

def elabWitnessTarget (circuitStx : TSyntax `term) : TermElabM WitnessTarget := do
  let circuit ← Lean.Elab.Term.elabTerm circuitStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let circuit ← instantiateMVars circuit
  let circuitType ← inferType circuit
  if let some F ← circuitField? circuitType then
    return circuitWitnessTarget circuit F
  let circuitType ← instantiateMVars circuitType
  let typeFn := circuitType.getAppFn

  let base? ←
    if typeFn.isConstOf ``FormalCircuitBase then
      pure (some circuit)
    else if typeFn.isConstOf ``FormalCircuit then
      some <$> mkAppM ``FormalCircuit.base #[circuit]
    else if typeFn.isConstOf ``FormalAssertion then
      some <$> mkAppM ``FormalAssertion.base #[circuit]
    else if typeFn.isConstOf ``GeneralFormalCircuit then
      some <$> mkAppM ``GeneralFormalCircuit.base #[circuit]
    else if typeFn.isConstOf ``GeneralFormalCircuit.WithHint then
      some <$> mkAppM ``GeneralFormalCircuit.WithHint.base #[circuit]
    else
      pure none
  if let some base := base? then
    if let some (F, Input) ← formalBaseInput? base then
      return formalCircuitBaseWitnessTarget base F Input

  throwError "expected a Circuit term or supported formal circuit, got type:{indentExpr circuitType}"

syntax "#compile_witness " term : command
syntax "compile_witness " term " => " ident : command

elab_rules : command
  | `(#compile_witness $circuitStx:term) => runTermElabM fun _ => do
      let target ← elabWitnessTarget circuitStx
      withLocalDeclD `offset (mkConst ``Nat) fun offset => do
        let (ops, _) ← target.dataOf offset
        withLocalDeclD `env (← mkAppM ``ProverEnvironment #[target.F]) fun env => do
        withLocalDeclD `witnesses (← mkAppM ``Array #[target.F]) fun witnesses => do
          let state : CompileState := { offset, env, witnesses }
          let (msgs, _) ← compileOperations target.F ops state
          if (← getOptions).getBool `debug.compileWitness false then
            logInfo m!"normalized operations:{indentExpr ops}"
            if msgs.isEmpty then
              logInfo "no witness operations found"
            else
              for msg in msgs do
                logInfo msg

  | `(compile_witness $circuitStx:term => $declIdent:ident) => do
      let rawName := declIdent.getId.eraseMacroScopes
      let ns ← getCurrNamespace
      let declName :=
        match rawName with
        | .str .anonymous s => .str ns s
        | _ => rawName
      runTermElabM fun _ => do
        let target ← elabWitnessTarget circuitStx
        let arrType ← mkAppM ``Array #[target.F]
        let (type, value) ←
          withLocalDeclD `offset (mkConst ``Nat) fun offset => do
          withLocalDeclD `witnesses arrType fun witnesses => do
            let (ops, localLength) ← target.dataOf offset
            let boundType ← mkBoundType offset localLength witnesses
            withLocalDeclD `h boundType fun h => do
              let envType ← mkAppM ``ProverEnvironment #[target.F]
              withLocalDeclD `env envType fun env => do
                let state : CompileState := {
                  offset, env, witnesses, localLength? := some localLength, bound? := some h
                }
                let body ← compileOperationsToArray target.F ops state witnesses fun current _ =>
                  return current
                let value ← mkLambdaFVars #[offset, witnesses, h] body
                let type ← mkForallFVars #[offset, witnesses, h] arrType
                return (type, value)
        let type ← instantiateMVars type
        let value ← instantiateMVars value
        if (← getOptions).getBool `debug.compileWitness false then
          logInfo m!"generated witness declaration before checking:\n\ndef {declName} :{indentExpr type} :={indentExpr value}"
        if type.hasFVar || value.hasFVar then
          let typeFVar := type.find? (·.isFVar)
          let valueFVar := value.find? (·.isFVar)
          throwError "generated witness declaration still has free variables\n\ntype fvar:{indentD (toMessageData typeFVar)}\n\nvalue fvar:{indentD (toMessageData valueFVar)}\n\ntype:{indentExpr type}\n\nvalue:{indentExpr value}"
        let defVal ← mkDefinitionValInferringUnsafe declName [] type value .abbrev
        addDecl (.defnDecl defVal)

end Circuit.Witness
