/-
  Deriving handler for ProvableStruct.

  This macro generates `ProvableStruct` instances for structures where:
  - All fields are of the form `M F` where `M : TypeMap` (i.e., `M : Type → Type`)
  - Each `M` must have a `ProvableType M` or `ProvableStruct M` instance

  Example:
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
    toComponents := fun { pc, ap, fp } => .cons pc (.cons ap (.cons fp .nil))
    fromComponents := fun (.cons pc (.cons ap (.cons fp .nil))) => { pc, ap, fp }
  ```

  Also supports extra type parameters:
  ```lean
  structure Inputs (n : ℕ) (F : Type) where
    data : Vector F n
  deriving ProvableStruct
  ```

  Generates:
  ```lean
  instance {n : ℕ} : ProvableStruct (Inputs n) where
    components := [fields n]
    ...
  ```

  And TypeMap parameters with instance constraints:
  ```lean
  structure Inputs (M : TypeMap) (F : Type) where
    value : M F
  deriving ProvableStruct
  ```

  Generates:
  ```lean
  instance {M : TypeMap} [ProvableType M] : ProvableStruct (Inputs M) where
    components := [M]
    ...
  ```

  Also supports `Vector (M F) n` field types:
  ```lean
  structure State (F : Type) where
    message : Vector (U32 F) 16
  deriving ProvableStruct
  ```

  Generates:
  ```lean
  instance : ProvableStruct State where
    components := [ProvableVector U32 16]
    ...
  ```
-/
import Lean
import Clean.Circuit.Provable

open Lean Meta Elab Term Command Parser.Term

namespace ProvableStructDeriving

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

/--
  Check if an expression is a bound variable at a specific index.
  In forallTelescope, the first parameter is bvar 0 (after abstracting),
  but in the args array, it's at index 0.
-/
def isBVarAt (e : Expr) (idx : Nat) : Bool :=
  match e with
  | .bvar i => i == idx
  | _ => false

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

end ProvableStructDeriving
