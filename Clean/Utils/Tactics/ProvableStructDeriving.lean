import Lean
import Clean.Circuit.Provable

/-!
  # Deriving handler for ProvableStruct

  This macro generates `ProvableStruct` instances for structures where all fields
  are of the form `M F` where `M : TypeMap` (i.e., `M : Type → Type`), and each `M`
  must have a `ProvableType M` instance.

  ## Basic usage

  ```lean
  structure MyState (F : Type) where
    pc : F
    ap : F
    fp : F
  deriving ProvableStruct
  ```

  Generates:
  ```lean
  instance : ProvableStruct MyState where
    components := [field, field, field]
    toComponents := fun ⟨pc, ap, fp⟩ => .cons pc (.cons ap (.cons fp .nil))
    fromComponents := fun (.cons pc (.cons ap (.cons fp .nil))) => MyState.mk pc ap fp
  ```

  ## Extra type parameters

  Supports structures with additional parameters before `F`:

  ```lean
  structure Inputs (n : ℕ) (F : Type) where
    data : Vector F n
  deriving ProvableStruct
  -- Generates: instance {n : ℕ} : ProvableStruct (Inputs n)
  ```

  For `TypeMap` parameters, automatically adds `ProvableType` constraints:

  ```lean
  structure Inputs (M : TypeMap) (F : Type) where
    value : M F
  deriving ProvableStruct
  -- Generates: instance {M : TypeMap} [ProvableType M] : ProvableStruct (Inputs M)
  ```

  ## Vector field types

  - `Vector F n` → mapped to `fields n` (eval expands to element-wise map)
  - `Vector (M F) n` → mapped to `ProvableVector M n` (eval stays unexpanded)

  ```lean
  structure State (F : Type) where
    data : Vector F 8           -- becomes: fields 8
    words : Vector (U32 F) 16   -- becomes: ProvableVector U32 16
  deriving ProvableStruct
  ```

  ## Controlling eval expansion with type aliases

  For `Vector F n` fields, the derived instance uses `fields n`, which causes `eval`
  to expand to `Vector.map (Expression.eval env)` under `circuit_norm`. If you need
  `eval` to stay unexpanded (e.g., for certain proof patterns), define a type alias:

  ```lean
  @[reducible] def MyBuffer := ProvableVector field 64

  structure Inputs (F : Type) where
    buffer : MyBuffer F   -- eval stays unexpanded
  deriving ProvableStruct
  ```

  This pattern is used in the codebase for types like `BLAKE3State`, `KeccakState`, etc.
-/

open Lean Meta Elab Term Command Parser.Term

namespace ProvableStructDeriving

/-- Use a declaration name relative to the current namespace when generating commands. -/
def relativeToCurrentNamespace (name : Name) : CommandElabM Name := do
  let ns ← getCurrNamespace
  if ns != .anonymous && ns.isPrefixOf name then
    return name.replacePrefix ns .anonymous
  return name

/--
  Information about a structure parameter (other than the final F : Type parameter)
-/
inductive ParamInfo where
  | natural : Name → ParamInfo      -- (n : ℕ)
  | typeMap : Name → ParamInfo      -- (M : TypeMap) - needs [ProvableType M]
  | other : Name → Expr → ParamInfo -- other type parameter
deriving Inhabited

def ParamInfo.name : ParamInfo → Name
  | .natural n => n
  | .typeMap n => n
  | .other n _ => n

inductive CircuitFieldKind where
  | regular
  | unconstrained
deriving Inhabited, BEq

def fieldKindFor (fieldNames : Array Name) (fieldKinds : Array CircuitFieldKind) (name : Name) :
    CircuitFieldKind :=
  Id.run do
    for i in [:fieldNames.size] do
      if fieldNames[i]! == name then
        return fieldKinds[i]!
    return .regular

partial def eraseMacroScopesSyntax : Syntax → Syntax
  | .missing => .missing
  | .atom info val => .atom info val
  | .ident info rawVal val preresolved => .ident info rawVal val.eraseMacroScopes preresolved
  | .node info kind args => .node info kind (args.map eraseMacroScopesSyntax)

def eraseMacroScopesTerm (stx : TSyntax `term) : TSyntax `term :=
  ⟨eraseMacroScopesSyntax stx.raw⟩

def withLeadingFieldInstanceForallStripped {α : Type} (fieldParamFVar hintType : Expr)
    (k : Expr → MetaM α) : MetaM α :=
  match hintType with
  | .forallE name binderTy body .instImplicit =>
      let (fn, args) := binderTy.getAppFnArgs
      if fn == ``Field && args.size == 1 && args[0]! == fieldParamFVar then
        withLocalDecl name .instImplicit binderTy fun fvar =>
          k (body.instantiate1 fvar)
      else
        k hintType
  | _ => k hintType

def matchUnconstrainedField? (fieldType typeParamFVar : Expr) : Option Expr :=
  let (fn, args) := fieldType.getAppFnArgs
  if fn == ``Unconstrained && args.size == 2 && args[1]! == typeParamFVar then
    some args[0]!
  else
    none

def matchProofOnlyField? (fieldType typeParamFVar : Expr) : MetaM (Option Expr) := do
  match matchUnconstrainedField? fieldType typeParamFVar with
  | some hintType => return some hintType
  | none =>
      if ← isProp fieldType then
        return some fieldType
      else
        return none

def isRawPropField (fieldType typeParamFVar : Expr) : MetaM Bool := do
  if (matchUnconstrainedField? fieldType typeParamFVar).isSome then
    return false
  isProp fieldType

partial def containsProjectionFrom (structName : Name) (e : Expr) : Bool :=
  let (fn, _) := e.getAppFnArgs
  if structName.isPrefixOf fn then
    true
  else
    match e with
    | .app f a => containsProjectionFrom structName f || containsProjectionFrom structName a
    | .lam _ t b _ => containsProjectionFrom structName t || containsProjectionFrom structName b
    | .forallE _ t b _ => containsProjectionFrom structName t || containsProjectionFrom structName b
    | .letE _ t v b _ =>
        containsProjectionFrom structName t || containsProjectionFrom structName v ||
          containsProjectionFrom structName b
    | .mdata _ b => containsProjectionFrom structName b
    | .proj _ _ b => containsProjectionFrom structName b
    | _ => false

partial def containsAnyFVar (fvars : Array Expr) (e : Expr) : Bool :=
  if fvars.any (· == e) then
    true
  else
    match e with
    | .app f a => containsAnyFVar fvars f || containsAnyFVar fvars a
    | .lam _ t b _ => containsAnyFVar fvars t || containsAnyFVar fvars b
    | .forallE _ t b _ => containsAnyFVar fvars t || containsAnyFVar fvars b
    | .letE _ t v b _ =>
        containsAnyFVar fvars t || containsAnyFVar fvars v || containsAnyFVar fvars b
    | .mdata _ b => containsAnyFVar fvars b
    | .proj _ _ b => containsAnyFVar fvars b
    | _ => false

partial def dependentCircuitExprToSyntax (structName : Name) (typeParamFVar : Expr)
    (fieldNames : Array Name) (fieldKinds : Array CircuitFieldKind) (fieldTypes : Array Expr)
    (sourceFieldFVars : Array Expr) (fieldLimit : Nat) (mode : Name) (e : Expr) :
    MetaM (TSyntax `term) := do
  let proverEnvType := mkApp (mkConst ``ProverEnvironment) typeParamFVar
  let expressionType := mkApp (mkConst ``Expression) typeParamFVar

  let fieldViewType (idx : Nat) : MetaM Expr := do
    let fieldType := fieldTypes[idx]!
    match ← matchProofOnlyField? fieldType typeParamFVar with
    | some hintType =>
        if mode == `var then
          return ← mkArrow proverEnvType hintType
        else
          withLeadingFieldInstanceForallStripped typeParamFVar hintType pure
    | none =>
        if fieldType == typeParamFVar && mode == `var then
          return expressionType
        return fieldType

  let rec withFieldDecls {α : Type} (idx : Nat) (fieldFVars : Array Expr) (k : Array Expr → MetaM α) :
      MetaM α := do
    if idx < fieldLimit then
      let fieldName := fieldNames[idx]!
      let fieldType ← fieldViewType idx
      withLocalDecl fieldName .default fieldType fun fieldFVar =>
        withFieldDecls (idx + 1) (fieldFVars.push fieldFVar) k
    else
      k fieldFVars

  let delabTransformed (env? : Option Expr) (fieldFVars : Array Expr) : MetaM (TSyntax `term) := do
    let body ← transform env? fieldFVars e
    let stx ← PrettyPrinter.delab body
    return eraseMacroScopesTerm ⟨stx.raw⟩

  if mode == `var then
    let fieldInstType := mkApp (mkConst ``Field) typeParamFVar
    withLocalDecl `env .default proverEnvType fun envFVar =>
      withLocalDecl `inst .instImplicit fieldInstType fun instFVar =>
        withNewLocalInstances #[instFVar] 0 do
          withFieldDecls 0 #[] fun fieldFVars => do
            delabTransformed (some envFVar) fieldFVars
  else
    withFieldDecls 0 #[] fun fieldFVars =>
      delabTransformed none fieldFVars
where
  fieldIdentOfProjection? (e : Expr) : Option Name :=
    let (fn, _) := e.getAppFnArgs
    fieldNames.find? fun fieldName => fn == structName ++ fieldName

  fieldIdentOfSourceFVar? (e : Expr) : Option Name :=
    Id.run do
      for i in [:sourceFieldFVars.size] do
        if sourceFieldFVars[i]! == e then
          return some fieldNames[i]!
      return none

  fieldIdentOfReference? (e : Expr) : Option Name :=
    match fieldIdentOfProjection? e with
    | some fieldName => some fieldName
    | none => fieldIdentOfSourceFVar? e

  fieldIndex? (name : Name) : Option Nat :=
    Id.run do
      for i in [:fieldNames.size] do
        if fieldNames[i]! == name then
          return some i
      return none

  replaceField (env? : Option Expr) (fieldFVars : Array Expr) (fieldName : Name) :
      MetaM Expr := do
    let some idx := fieldIndex? fieldName
      | throwError "unknown dependent field {fieldName}"
    let fieldFVar := fieldFVars[idx]!
    if mode == `var then
      let some env := env?
        | throwError "missing prover environment while translating dependent Var field"
      let fieldType := fieldTypes[idx]!
      let valueType ←
        match ← matchProofOnlyField? fieldType typeParamFVar with
        | some hintType => pure hintType
        | none => pure fieldType
      if ← isRawPropField fieldType typeParamFVar then
        return mkApp fieldFVar env
      else
        let envType ← inferType env
        let varType ← inferType fieldFVar
        let evalInstType ← mkAppOptM ``Eval #[envType, varType, valueType]
        let evalInst ← mkFreshExprMVar (some evalInstType)
        mkAppOptM ``Eval.eval #[envType, varType, valueType, evalInst, env, fieldFVar]
    else
      return fieldFVar

  matchStructProjection? (env? : Option Expr) (fieldFVars : Array Expr) (e : Expr) :
      MetaM (Option Expr) := do
    let some fieldName := fieldIdentOfReference? e
      | return none
    return some (← replaceField env? fieldFVars fieldName)

  matchUnconstrainedValue? (env? : Option Expr) (fieldFVars : Array Expr) (e : Expr) :
      MetaM (Option Expr) := do
    let (fn, args) := e.getAppFnArgs
    unless fn == ``Unconstrained.value && args.size == 3 do
      return none
    let some fieldName := fieldIdentOfReference? args[2]!
      | return none
    unless fieldKindFor fieldNames fieldKinds fieldName == .unconstrained do
      return none
    return some (← replaceField env? fieldFVars fieldName)

  transform (env? : Option Expr) (fieldFVars : Array Expr) (e : Expr) : MetaM Expr := do
    if let some replacement ← matchUnconstrainedValue? env? fieldFVars e then
      return replacement
    if let some replacement ← matchStructProjection? env? fieldFVars e then
      return replacement
    match e with
    | .app f arg =>
        return mkApp (← transform env? fieldFVars f) (← transform env? fieldFVars arg)
    | .lam name type body binderInfo =>
        let type' ← transform env? fieldFVars type
        withLocalDecl name binderInfo type' fun fvar => do
          let body' ← transform env? fieldFVars (body.instantiate1 fvar)
          return .lam name type' (body'.abstract #[fvar]) binderInfo
    | .forallE name type body binderInfo =>
        let type' ← transform env? fieldFVars type
        withLocalDecl name binderInfo type' fun fvar => do
          let body' ← transform env? fieldFVars (body.instantiate1 fvar)
          return .forallE name type' (body'.abstract #[fvar]) binderInfo
    | .letE name type value body nondep =>
        let type' ← transform env? fieldFVars type
        let value' ← transform env? fieldFVars value
        withLocalDecl name .default type' fun fvar => do
          let body' ← transform env? fieldFVars (body.instantiate1 fvar)
          return .letE name type' value' (body'.abstract #[fvar]) nondep
    | .mdata data body => return .mdata data (← transform env? fieldFVars body)
    | .proj typeName idx struct => return .proj typeName idx (← transform env? fieldFVars struct)
    | _ => return e

/--
  Analyze a field type to determine its TypeMap.
  `numParams` is the total number of parameters (including F)
  `fieldType` is the type of the field (may contain bvars referring to params)

  The parameters are indexed as: param 0, param 1, ..., param (numParams-2), F (at numParams-1)
  In bvar representation (when abstracted), F is bvar 0, param (numParams-2) is bvar 1, etc.

  Actually, in forallTelescope the args are fvars, so we compare fvars directly by position.
-/
def analyzeFieldType (numParams : Nat) (paramFVars : Array Expr) (fieldType : Expr) : MetaM (TSyntax `term) := do
  -- The type param F is at index (numParams - 1) in paramFVars
  let typeParamIdx := numParams - 1
  let typeParamFVar := paramFVars[typeParamIdx]!
  let otherParamFVars := paramFVars[:typeParamIdx]

  -- Check if the field type is exactly the type parameter F
  if fieldType == typeParamFVar then
    `(field)
  else
    -- Check if it's an application
    match fieldType with
    | .app f arg =>
      -- Check if it's Vector applied to something
      match f with
      | .app (.const ``Vector _) innerType =>
        -- This is `Vector innerType arg` where arg should be the size
        -- innerType could be F or (M F)
        let sizeSyntax ← exprToSyntax otherParamFVars arg

        if innerType == typeParamFVar then
          -- Vector F n -> fields n
          `(fields $sizeSyntax)
        else
          -- Check if innerType is (M F)
          match innerType with
          | .app m innerArg =>
            if innerArg == typeParamFVar then
              -- Vector (M F) n -> ProvableVector M n
              let mSyntax ← exprToSyntax otherParamFVars m
              `(ProvableVector $mSyntax $sizeSyntax)
            else
              throwError "unsupported Vector inner type: {innerType}. Expected F or M F."
          | _ =>
            throwError "unsupported Vector inner type: {innerType}. Expected F or M F."

      | _ =>
        -- Check if the argument is the type parameter (M F pattern)
        if arg == typeParamFVar then
          let fSyntax ← exprToSyntax otherParamFVars f
          return fSyntax
        else
          throwError "field type argument is not the type parameter: {fieldType}"
    | _ =>
      throwError "unsupported field type for ProvableStruct: {fieldType}. Expected either F, M F, Vector F n, or Vector (M F) n where F is the type parameter."
where
  /-- Convert an expression to syntax, handling fvars that reference other parameters -/
  exprToSyntax (paramFVars : Array Expr) (e : Expr) : MetaM (TSyntax `term) := do
    -- First, try to extract a natural number literal (handles elaborated OfNat.ofNat)
    if let some n := extractNatLit? e then
      let nLit := Syntax.mkNumLit (toString n)
      return ← `($nLit)

    match e with
    | .const name _ => return mkIdent name
    | .fvar fvarId =>
      -- Check if this fvar is one of our parameters
      for h : i in [:paramFVars.size] do
        if paramFVars[i] == e then
          let name ← fvarId.getUserName
          return mkIdent name
      throwError "unknown free variable in type: {e}"
    | .app f arg =>
      let fSyntax ← exprToSyntax paramFVars f
      let argSyntax ← exprToSyntax paramFVars arg
      `($fSyntax $argSyntax)
    | .lit (.natVal n) =>
      let nLit := Syntax.mkNumLit (toString n)
      `($nLit)
    | _ =>
      throwError "unsupported expression in field type: {e}"

  /-- Try to extract a natural number literal from an expression.
      Handles both raw literals and elaborated OfNat.ofNat expressions. -/
  extractNatLit? (e : Expr) : Option Nat :=
    match e with
    | .lit (.natVal n) => some n
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
    | _ => none

/--
  Analyze a parameter to determine its kind (natural number, TypeMap, or other)
-/
def analyzeParam (paramName : Name) (paramType : Expr) : MetaM ParamInfo := do
  -- Check if it's ℕ
  if paramType.isConstOf ``Nat then
    return .natural paramName
  -- Check if it's TypeMap
  if paramType.isConstOf ``TypeMap then
    return .typeMap paramName
  -- Otherwise, it's some other type
  return .other paramName paramType

/--
  Generate the ProvableStruct instance declaration using syntax quotations.
-/
def mkProvableStructInstance (structName : Name) : CommandElabM Unit := do
  let env ← getEnv

  -- Check that it's a structure
  unless isStructure env structName do
    throwError "{structName} is not a structure"

  -- Get structure info
  let some structInfo := getStructureInfo? env structName
    | throwError "failed to get structure info for {structName}"

  -- Get inductive info to check parameters
  let some (.inductInfo indInfo) := env.find? structName
    | throwError "{structName} not found in environment"

  let numParams := indInfo.numParams

  -- Check that the structure has at least one type parameter (F : Type)
  if numParams < 1 then
    throwError "ProvableStruct deriving requires at least one type parameter (F : Type), but {structName} has {numParams}"

  -- Get field names
  let fieldNames := structInfo.fieldNames

  if fieldNames.isEmpty then
    throwError "ProvableStruct deriving requires at least one field"

  -- Do all analysis within a single forallTelescope to keep fvars consistent
  let (paramInfos, componentSyntaxes) ← liftTermElabM do
    forallTelescope indInfo.type fun args _ => do
      -- args are the parameters: param_0, param_1, ..., param_(n-2), F
      -- We need info for all but the last one (F : Type)
      let mut infos : Array ParamInfo := #[]
      for i in [:numParams - 1] do
        let paramFVar := args[i]!
        let paramName ← paramFVar.fvarId!.getUserName
        let paramType ← inferType paramFVar
        let info ← analyzeParam paramName paramType
        infos := infos.push info

      -- Analyze each field to determine its TypeMap
      let mut components : Array (TSyntax `term) := #[]
      for fname in fieldNames do
        -- Get projection function info
        let projFnName := structName ++ fname
        let some (.defnInfo projInfo) := env.find? projFnName
          | throwError "projection {projFnName} not found"

        -- We need to extract the field type from the projection.
        -- The projection has type: ∀ (params...) (self : StructName params), FieldType
        -- We need to instantiate it with our fvars to get the field type
        let fieldType ← forallTelescope projInfo.type fun projArgs projBody => do
          -- projArgs = [param_0, ..., param_(n-1), self]
          -- projBody is the return type (field type)
          -- We need to substitute our args for the param fvars in projBody
          if projArgs.size != numParams + 1 then
            throwError "projection {projFnName} has unexpected arity: {projArgs.size} vs expected {numParams + 1}"

          -- Create substitution: projArgs[i] -> args[i] for i < numParams
          let mut result := projBody
          for i in [:numParams] do
            result := result.replaceFVar projArgs[i]! args[i]!
          return result

        let componentSyntax ← analyzeFieldType numParams args fieldType
        components := components.push componentSyntax

      return (infos, components)

  let fieldNameIdents : Array (TSyntax `ident) := fieldNames.map mkIdent

  -- Build the components list syntax: [M1, M2, M3, ...]
  let componentsListSyntax ← `([$[$componentSyntaxes],*])

  -- Build toComponents body: .cons f1 (.cons f2 (.cons f3 .nil))
  let mut toCompBody : TSyntax `term ← `(.nil)
  for i in [:fieldNameIdents.size] do
    let idx := fieldNameIdents.size - 1 - i
    let fname := fieldNameIdents[idx]!
    toCompBody ← `(.cons $fname $toCompBody)

  -- Build fromComponents pattern: (.cons f1 (.cons f2 (.cons f3 .nil)))
  let mut fromCompPat : TSyntax `term ← `(.nil)
  for i in [:fieldNameIdents.size] do
    let idx := fieldNameIdents.size - 1 - i
    let fname := fieldNameIdents[idx]!
    fromCompPat ← `(.cons $fname $fromCompPat)

  -- Build the struct literal with fields
  let structIdent := mkIdent structName

  -- For fromComponents, we build the struct constructor explicitly: StructName.mk f1 f2 f3
  let structMk := mkIdent (structName ++ `mk)
  let mkAppSyntax ← fieldNameIdents.foldlM (init := (structMk : TSyntax `term)) fun acc fname =>
    `($acc $fname)

  -- For toComponents, we use anonymous constructor pattern ⟨f1, f2, f3⟩
  -- Build it manually using proper syntax
  let structPatFields := fieldNameIdents.map (TSyntax.mk ·.raw)
  let structPat ← `(⟨$[$structPatFields],*⟩)

  -- Build the applied structure type if there are extra parameters
  -- e.g., Inputs n M for structure Inputs (n : ℕ) (M : TypeMap) (F : Type)
  let appliedStructType : TSyntax `term ←
    if paramInfos.isEmpty then
      `($structIdent)
    else
      let paramIdents := paramInfos.map (fun p => mkIdent p.name)
      paramIdents.foldlM (init := (structIdent : TSyntax `term)) fun acc paramIdent =>
        `($acc $paramIdent)

  -- Build the instance binders for extra parameters using bracketedBinderF
  -- e.g., {n : ℕ} {M : TypeMap} [ProvableType M]
  let mut binderSyntaxes : Array (TSyntax ``bracketedBinder) := #[]
  for info in paramInfos do
    match info with
    | .natural n =>
      let nIdent := mkIdent n
      let binder ← `(bracketedBinderF| {$nIdent : ℕ})
      binderSyntaxes := binderSyntaxes.push binder
    | .typeMap m =>
      let mIdent := mkIdent m
      let typeBinder ← `(bracketedBinderF| {$mIdent : TypeMap})
      let instBinder ← `(bracketedBinderF| [ProvableType $mIdent])
      binderSyntaxes := binderSyntaxes.push typeBinder
      binderSyntaxes := binderSyntaxes.push instBinder
    | .other n ty =>
      let nIdent := mkIdent n
      -- For other types, we need to convert the type expression to syntax
      let tySyntax ← liftTermElabM <| PrettyPrinter.delab ty
      let binder ← `(bracketedBinderF| {$nIdent : $tySyntax})
      binderSyntaxes := binderSyntaxes.push binder

  -- Build the full instance command
  let cmd ←
    if binderSyntaxes.isEmpty then
      `(
        instance : ProvableStruct $appliedStructType where
          components := $componentsListSyntax
          toComponents := fun $structPat => $toCompBody
          fromComponents := fun ($fromCompPat) => $mkAppSyntax
      )
    else
      `(
        instance $binderSyntaxes:bracketedBinder* : ProvableStruct $appliedStructType where
          components := $componentsListSyntax
          toComponents := fun $structPat => $toCompBody
          fromComponents := fun ($fromCompPat) => $mkAppSyntax
      )

  elabCommand cmd

/-- The deriving handler for ProvableStruct -/
def provableStructDerivingHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  let declName := declNames[0]!
  let env ← getEnv
  -- Check if it's a structure
  unless isStructure env declName do
    return false
  try
    mkProvableStructInstance declName
    return true
  catch e =>
    -- Log error and return false
    logError m!"Failed to derive ProvableStruct for {declName}: {e.toMessageData}"
    return false

-- Register the deriving handler
initialize registerDerivingHandler ``ProvableStruct provableStructDerivingHandler

/--
  Generate a companion structure for one of the `CircuitType` views of a
  derived `CircuitType`.
-/
def mkCircuitViewStruct (viewName : Name) (paramInfos : Array ParamInfo)
    (includeFieldBinder : Bool)
    (fieldNameIdents : Array (TSyntax `ident)) (fieldTypes : Array (TSyntax `term))
    (viewType : TSyntax `term → CommandElabM (TSyntax `term)) : CommandElabM Unit := do
  let mut binderSyntaxes : Array (TSyntax ``bracketedBinder) := #[]
  for info in paramInfos do
    match info with
    | .natural n =>
      let nIdent := mkIdent n
      let binder ← `(bracketedBinderF| ($nIdent : ℕ))
      binderSyntaxes := binderSyntaxes.push binder
    | .typeMap m =>
      let mIdent := mkIdent m
      let typeBinder ← `(bracketedBinderF| ($mIdent : TypeMap))
      let instBinder ← `(bracketedBinderF| [CircuitType $mIdent])
      binderSyntaxes := binderSyntaxes.push typeBinder
      binderSyntaxes := binderSyntaxes.push instBinder
    | .other n ty =>
      let nIdent := mkIdent n
      let tySyntax ← liftTermElabM <| PrettyPrinter.delab ty
      let binder ← `(bracketedBinderF| ($nIdent : $tySyntax))
      binderSyntaxes := binderSyntaxes.push binder

  let fIdent := mkIdent `F
  let fBinder ← `(bracketedBinderF| ($fIdent : Type))
  binderSyntaxes := binderSyntaxes.push fBinder
  if includeFieldBinder then
    let fieldBinder ← `(bracketedBinderF| [Field $fIdent])
    binderSyntaxes := binderSyntaxes.push fieldBinder

  let mut fieldSyntaxes : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder) := #[]
  for h : i in [:fieldNameIdents.size] do
    let fname := fieldNameIdents[i]
    let component := fieldTypes[i]!
    let ty ← viewType component
    let field ← `(Lean.Parser.Command.structSimpleBinder| $fname:ident : $ty)
    fieldSyntaxes := fieldSyntaxes.push field

  let viewIdent := mkIdent (← relativeToCurrentNamespace viewName)
  let cmd ← `(
    structure $viewIdent $binderSyntaxes:bracketedBinder* where
      $fieldSyntaxes:structSimpleBinder*
  )
  elabCommand cmd

def mkCircuitEvalForwardingInstances (paramInfos : Array ParamInfo) (circuitType : TSyntax `term)
    (varType valueType proverValueType : TSyntax `term) : CommandElabM Unit := do
  let mut binderSyntaxes : Array (TSyntax ``bracketedBinder) := #[]
  for info in paramInfos do
    match info with
    | .natural n =>
      let nIdent := mkIdent n
      let binder ← `(bracketedBinderF| {$nIdent : ℕ})
      binderSyntaxes := binderSyntaxes.push binder
    | .typeMap m =>
      let mIdent := mkIdent m
      let typeBinder ← `(bracketedBinderF| {$mIdent : TypeMap})
      let instBinder ← `(bracketedBinderF| [CircuitType $mIdent])
      binderSyntaxes := binderSyntaxes.push typeBinder
      binderSyntaxes := binderSyntaxes.push instBinder
    | .other n ty =>
      let nIdent := mkIdent n
      let tySyntax ← liftTermElabM <| PrettyPrinter.delab ty
      let binder ← `(bracketedBinderF| {$nIdent : $tySyntax})
      binderSyntaxes := binderSyntaxes.push binder

  let fIdent := mkIdent `F
  let fBinder ← `(bracketedBinderF| { $fIdent : Type })
  let fieldBinder ← `(bracketedBinderF| [Field $fIdent])
  binderSyntaxes := binderSyntaxes.push fBinder
  binderSyntaxes := binderSyntaxes.push fieldBinder

  let cmd ← `(
    instance $binderSyntaxes:bracketedBinder* : VerifierEval $fIdent ($varType $fIdent) ($valueType $fIdent) :=
      CircuitType.verifierEval $circuitType

    instance $binderSyntaxes:bracketedBinder* : ProverEval $fIdent ($varType $fIdent) ($proverValueType $fIdent) :=
      CircuitType.proverEval $circuitType
  )
  elabCommand cmd

def mkDependentCircuitTypeInstance? (structName : Name) : CommandElabM Bool := do
  let env ← getEnv
  let some structInfo := getStructureInfo? env structName
    | throwError "failed to get structure info for {structName}"
  let some (.inductInfo indInfo) := env.find? structName
    | throwError "{structName} not found in environment"
  let ctorName ←
    match indInfo.ctors with
    | [ctorName] => pure ctorName
    | _ => throwError "{structName} should have exactly one constructor"
  let some (.ctorInfo ctorInfo) := env.find? ctorName
    | throwError "constructor {ctorName} not found"
  let numParams := indInfo.numParams
  if numParams != 1 then
    return false

  let fieldNames := structInfo.fieldNames
  if fieldNames.isEmpty then
    return false

  let resultOpt ← liftTermElabM do
    forallTelescope ctorInfo.type fun args _ => do
      if args.size < numParams + fieldNames.size then
        throwError "constructor {ctorName} has unexpected arity: {args.size}"
      let typeParamFVar := args[0]!
      let sourceFieldFVars : Array Expr :=
        Id.run do
          let mut result := #[]
          for i in [:fieldNames.size] do
            result := result.push args[numParams + i]!
          return result
      let mut fieldTypes : Array Expr := #[]
      let mut fieldKinds : Array CircuitFieldKind := #[]
      let mut hasDependentProofOnly := false

      for i in [:fieldNames.size] do
        let fieldType ← inferType sourceFieldFVars[i]!
        fieldTypes := fieldTypes.push fieldType
        match ← matchProofOnlyField? fieldType typeParamFVar with
        | some hintType =>
            fieldKinds := fieldKinds.push .unconstrained
            if ← isRawPropField fieldType typeParamFVar then
              hasDependentProofOnly := true
            if containsProjectionFrom structName hintType || containsAnyFVar sourceFieldFVars hintType then
              hasDependentProofOnly := true
        | none =>
            fieldKinds := fieldKinds.push .regular

      unless hasDependentProofOnly do
        return none

      let mut varFieldTypes : Array (TSyntax `term) := #[]
      let mut valueFieldTypes : Array (TSyntax `term) := #[]
      let mut proverFieldTypes : Array (TSyntax `term) := #[]
      let mut verifierArgs : Array (TSyntax `term) := #[]
      let mut proverArgs : Array (TSyntax `term) := #[]

      for i in [:fieldNames.size] do
        let fname := fieldNames[i]!
        let fieldIdent := mkIdent fname
        let fieldType := fieldTypes[i]!
        match ← matchProofOnlyField? fieldType typeParamFVar with
        | some hintType =>
            let isRawProp ← isRawPropField fieldType typeParamFVar
            if containsProjectionFrom structName hintType || containsAnyFVar sourceFieldFVars hintType then
              let hVar ← withLeadingFieldInstanceForallStripped typeParamFVar hintType fun hintType =>
                dependentCircuitExprToSyntax structName typeParamFVar fieldNames fieldKinds fieldTypes
                  sourceFieldFVars i
                  `var hintType
              let hProver ← withLeadingFieldInstanceForallStripped typeParamFVar hintType fun hintType =>
                dependentCircuitExprToSyntax structName typeParamFVar fieldNames fieldKinds fieldTypes
                  sourceFieldFVars i
                  `prover hintType
              let envIdent := mkIdent `env
              varFieldTypes := varFieldTypes.push (← `(∀ ($envIdent : ProverEnvironment F), $hVar))
              valueFieldTypes := valueFieldTypes.push (← `(Unit))
              proverFieldTypes := proverFieldTypes.push hProver
              verifierArgs := verifierArgs.push (← `(()))
              proverArgs := proverArgs.push (← `(input.$fieldIdent:ident env))
            else
              let hintTypeStx ← PrettyPrinter.delab hintType
              let hintTerm : TSyntax `term := ⟨hintTypeStx.raw⟩
              varFieldTypes := varFieldTypes.push (← `(ProverEnvironment F → $hintTerm))
              valueFieldTypes := valueFieldTypes.push (← `(Unit))
              proverFieldTypes := proverFieldTypes.push hintTerm
              verifierArgs := verifierArgs.push (← `(()))
              if isRawProp then
                proverArgs := proverArgs.push (← `(input.$fieldIdent:ident env))
              else
                proverArgs := proverArgs.push (← `(eval env input.$fieldIdent:ident))
        | none =>
            if fieldType == typeParamFVar then
              varFieldTypes := varFieldTypes.push (← `(Expression F))
              valueFieldTypes := valueFieldTypes.push (← `(F))
              proverFieldTypes := proverFieldTypes.push (← `(F))
            else
              let component ← analyzeFieldType numParams args fieldType
              varFieldTypes := varFieldTypes.push (← `(CircuitType.Var $component F))
              valueFieldTypes := valueFieldTypes.push (← `(CircuitType.Value $component F))
              proverFieldTypes := proverFieldTypes.push (← `(CircuitType.ProverValue $component F))
            verifierArgs := verifierArgs.push (← `(eval env input.$fieldIdent:ident))
            proverArgs := proverArgs.push (← `(eval env input.$fieldIdent:ident))

      return some (fieldKinds, varFieldTypes, valueFieldTypes, proverFieldTypes, verifierArgs, proverArgs)

  let some (_, varFieldTypes, valueFieldTypes, proverFieldTypes, verifierArgs, proverArgs) := resultOpt
    | return false
  let varFieldTypes := varFieldTypes.map eraseMacroScopesTerm
  let valueFieldTypes := valueFieldTypes.map eraseMacroScopesTerm
  let proverFieldTypes := proverFieldTypes.map eraseMacroScopesTerm
  let verifierArgs := verifierArgs.map eraseMacroScopesTerm
  let proverArgs := proverArgs.map eraseMacroScopesTerm
  let fieldNameIdents : Array (TSyntax `ident) := fieldNames.map mkIdent

  let varStructName := structName ++ `Var
  let valueStructName := structName ++ `Value
  let proverValueStructName := structName ++ `ProverValue

  let fIdent := mkIdent `F
  let fBinder ← `(bracketedBinderF| ($fIdent : Type))
  let fieldBinder ← `(bracketedBinderF| [Field $fIdent])

  let mkStruct (name : Name) (binders : Array (TSyntax ``bracketedBinder))
      (fieldTypes : Array (TSyntax `term)) : CommandElabM Unit := do
    let mut fieldSyntaxes : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder) := #[]
    for i in [:fieldNameIdents.size] do
      let fname := fieldNameIdents[i]!
      let ty := fieldTypes[i]!
      fieldSyntaxes := fieldSyntaxes.push (← `(Lean.Parser.Command.structSimpleBinder| $fname:ident : $ty))
    let nameIdent := mkIdent (← relativeToCurrentNamespace name)
    let cmd ← `(
      structure $nameIdent $binders:bracketedBinder* where
        $fieldSyntaxes:structSimpleBinder*
    )
    elabCommand cmd

  mkStruct varStructName #[fBinder, fieldBinder] varFieldTypes
  mkStruct valueStructName #[fBinder, fieldBinder] valueFieldTypes
  mkStruct proverValueStructName #[fBinder, fieldBinder] proverFieldTypes

  let structIdent := mkIdent structName
  let varIdent := mkIdent (← relativeToCurrentNamespace varStructName)
  let valueIdent := mkIdent (← relativeToCurrentNamespace valueStructName)
  let proverValueIdent := mkIdent (← relativeToCurrentNamespace proverValueStructName)
  let valueMk := mkIdent (← relativeToCurrentNamespace (valueStructName ++ `mk))
  let proverMk := mkIdent (← relativeToCurrentNamespace (proverValueStructName ++ `mk))

  let mut verifierBody : TSyntax `term := valueMk
  for arg in verifierArgs do
    verifierBody ← `($verifierBody $arg)
  let mut proverBody : TSyntax `term := proverMk
  for arg in proverArgs do
    proverBody ← `($proverBody $arg)

  let envIdent := mkIdent `env
  let inputIdent := mkIdent `input
  let instanceCmd ← `(
    instance : CircuitType $structIdent where
      Var := $varIdent
      Value := $valueIdent
      ProverValue := $proverValueIdent
      evalVerifier := fun $envIdent $inputIdent => $verifierBody
      evalProver := fun $envIdent $inputIdent => $proverBody
  )
  elabCommand instanceCmd
  mkCircuitEvalForwardingInstances #[] structIdent varIdent valueIdent proverValueIdent
  return true

/--
  Generate the CircuitType instance declaration.
-/
def mkCircuitTypeInstance (structName : Name) : CommandElabM Unit := do
  let env ← getEnv

  unless isStructure env structName do
    throwError "{structName} is not a structure"

  if (← mkDependentCircuitTypeInstance? structName) then
    return

  let some structInfo := getStructureInfo? env structName
    | throwError "failed to get structure info for {structName}"

  let some (.inductInfo indInfo) := env.find? structName
    | throwError "{structName} not found in environment"

  let numParams := indInfo.numParams

  if numParams < 1 then
    throwError "CircuitType deriving requires at least one type parameter (F : Type), but {structName} has {numParams}"

  let fieldNames := structInfo.fieldNames

  if fieldNames.isEmpty then
    throwError "CircuitType deriving requires at least one field"

  let (paramInfos, componentSyntaxes) ← liftTermElabM do
    forallTelescope indInfo.type fun args _ => do
      let mut infos : Array ParamInfo := #[]
      for i in [:numParams - 1] do
        let paramFVar := args[i]!
        let paramName ← paramFVar.fvarId!.getUserName
        let paramType ← inferType paramFVar
        let info ← analyzeParam paramName paramType
        infos := infos.push info

      let mut components : Array (TSyntax `term) := #[]
      for fname in fieldNames do
        let projFnName := structName ++ fname
        let some (.defnInfo projInfo) := env.find? projFnName
          | throwError "projection {projFnName} not found"

        let fieldType ← forallTelescope projInfo.type fun projArgs projBody => do
          if projArgs.size != numParams + 1 then
            throwError "projection {projFnName} has unexpected arity: {projArgs.size} vs expected {numParams + 1}"

          let mut result := projBody
          for i in [:numParams] do
            result := result.replaceFVar projArgs[i]! args[i]!
          return result

        let componentSyntax ← analyzeFieldType numParams args fieldType
        components := components.push componentSyntax

      return (infos, components)

  let fieldNameIdents : Array (TSyntax `ident) := fieldNames.map mkIdent

  let varStructName := structName ++ `Var
  let valueStructName := structName ++ `Value
  let proverValueStructName := structName ++ `ProverValue

  let fIdent := mkIdent `F
  mkCircuitViewStruct varStructName paramInfos true fieldNameIdents componentSyntaxes
    (fun component => `(CircuitType.Var $component $fIdent))
  mkCircuitViewStruct valueStructName paramInfos true fieldNameIdents componentSyntaxes
    (fun component => `(CircuitType.Value $component $fIdent))
  mkCircuitViewStruct proverValueStructName paramInfos true fieldNameIdents componentSyntaxes
    (fun component => `(CircuitType.ProverValue $component $fIdent))

  let structIdent := mkIdent structName
  let appliedStructType : TSyntax `term ←
    if paramInfos.isEmpty then
      `($structIdent)
    else
      let paramIdents := paramInfos.map (fun p => mkIdent p.name)
      paramIdents.foldlM (init := (structIdent : TSyntax `term)) fun acc paramIdent =>
        `($acc $paramIdent)

  let viewTypeApp (viewName : Name) : CommandElabM (TSyntax `term) := do
    let viewIdent := mkIdent (← relativeToCurrentNamespace viewName)
    if paramInfos.isEmpty then
      `($viewIdent)
    else
      let paramIdents := paramInfos.map (fun p => mkIdent p.name)
      paramIdents.foldlM (init := (viewIdent : TSyntax `term)) fun acc paramIdent =>
        `($acc $paramIdent)

  let varType ← viewTypeApp varStructName
  let valueType ← viewTypeApp valueStructName
  let proverValueType ← viewTypeApp proverValueStructName

  let mut instanceBinders : Array (TSyntax ``bracketedBinder) := #[]
  for info in paramInfos do
    match info with
    | .natural n =>
      let nIdent := mkIdent n
      let binder ← `(bracketedBinderF| {$nIdent : ℕ})
      instanceBinders := instanceBinders.push binder
    | .typeMap m =>
      let mIdent := mkIdent m
      let typeBinder ← `(bracketedBinderF| {$mIdent : TypeMap})
      let instBinder ← `(bracketedBinderF| [CircuitType $mIdent])
      instanceBinders := instanceBinders.push typeBinder
      instanceBinders := instanceBinders.push instBinder
    | .other n ty =>
      let nIdent := mkIdent n
      let tySyntax ← liftTermElabM <| PrettyPrinter.delab ty
      let binder ← `(bracketedBinderF| {$nIdent : $tySyntax})
      instanceBinders := instanceBinders.push binder

  let inputIdent := mkIdent `input
  let envIdent := mkIdent `env
  let valueMk := mkIdent (← relativeToCurrentNamespace (valueStructName ++ `mk))
  let proverValueMk := mkIdent (← relativeToCurrentNamespace (proverValueStructName ++ `mk))

  let mut verifierBody : TSyntax `term := valueMk
  let mut proverBody : TSyntax `term := proverValueMk
  for fname in fieldNameIdents do
    let verifierField ← `($inputIdent.$fname:ident)
    let verifierEval ← `(Eval.eval $envIdent $verifierField)
    verifierBody ← `($verifierBody $verifierEval)

    let proverField ← `($inputIdent.$fname:ident)
    let proverEval ← `(Eval.eval $envIdent $proverField)
    proverBody ← `($proverBody $proverEval)

  let cmd ←
    if instanceBinders.isEmpty then
      `(
        instance : CircuitType $appliedStructType where
          Var := $varType
          Value := $valueType
          ProverValue := $proverValueType
          evalVerifier := fun $envIdent $inputIdent => $verifierBody
          evalProver := fun $envIdent $inputIdent => $proverBody
      )
    else
      `(
        instance $instanceBinders:bracketedBinder* : CircuitType $appliedStructType where
          Var := $varType
          Value := $valueType
          ProverValue := $proverValueType
          evalVerifier := fun $envIdent $inputIdent => $verifierBody
          evalProver := fun $envIdent $inputIdent => $proverBody
      )

  elabCommand cmd
  mkCircuitEvalForwardingInstances paramInfos appliedStructType varType valueType proverValueType

/-- The deriving handler for record-shaped `CircuitType`s. -/
def circuitTypeDerivingHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false
  let declName := declNames[0]!
  let env ← getEnv
  unless isStructure env declName do
    return false
  try
    mkCircuitTypeInstance declName
    return true
  catch e =>
    logError m!"Failed to derive CircuitType for {declName}: {e.toMessageData}"
    return false

initialize registerDerivingHandler ``CircuitType circuitTypeDerivingHandler

end ProvableStructDeriving
