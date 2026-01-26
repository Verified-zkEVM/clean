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
-/
import Lean
import Clean.Circuit.Provable

open Lean Meta Elab Term Command

namespace ProvableStructDeriving

/--
  Analyze a field type to determine its TypeMap.
  Given the type parameter fvar and the field type, determines if it's:
  - `F` (the type param) -> returns `field`
  - `M F` for some type map M -> returns the identifier for M
-/
def analyzeFieldType (typeParamFVar : Expr) (fieldType : Expr) : MetaM (TSyntax `term) := do
  -- Check if the field type is exactly the type parameter
  if fieldType == typeParamFVar then
    `(field)
  else
    -- Check if it's an application M F
    match fieldType with
    | .app f arg =>
      -- Check if the argument is the type parameter
      if arg == typeParamFVar then
        match f with
        | .const name _ =>
          -- Simple case: M is a constant like `State`
          return mkIdent name
        | _ =>
          throwError "unsupported type map expression: {f}"
      else
        throwError "field type argument is not the type parameter: {fieldType}"
    | _ =>
      throwError "unsupported field type for ProvableStruct: {fieldType}. Expected either F or M F where F is the type parameter."

/--
  Get the return type of a projection function along with the type parameter fvar.
  The projection has type `{F : Type} → StructName F → FieldType`
  Returns (typeParamFVar, FieldType).
-/
def getProjectionInfo (projType : Expr) : MetaM (Expr × Expr) := do
  forallTelescope projType fun args body => do
    -- The first argument is the type parameter F
    if args.size < 2 then
      throwError "projection has unexpected type: {projType}"
    let typeParamFVar := args[0]!
    pure (typeParamFVar, body)

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

  -- Check that the structure has exactly one type parameter
  if indInfo.numParams != 1 then
    throwError "ProvableStruct deriving currently only supports structures with exactly one type parameter, but {structName} has {indInfo.numParams}"

  -- Get field names
  let fieldNames := structInfo.fieldNames

  if fieldNames.isEmpty then
    throwError "ProvableStruct deriving requires at least one field"

  -- Analyze each field to determine its TypeMap
  let mut componentSyntaxes : Array (TSyntax `term) := #[]
  let mut fieldNameIdents : Array (TSyntax `ident) := #[]

  for fname in fieldNames do
    fieldNameIdents := fieldNameIdents.push (mkIdent fname)

    -- Get projection function info
    let projFnName := structName ++ fname
    let some (.defnInfo projInfo) := env.find? projFnName
      | throwError "projection {projFnName} not found"

    -- Extract field type and type parameter from projection
    let (typeParamFVar, fieldType) ← liftCoreM <| MetaM.run' <| getProjectionInfo projInfo.type

    -- Analyze field type to get the TypeMap syntax
    let componentSyntax ← liftCoreM <| MetaM.run' <| analyzeFieldType typeParamFVar fieldType
    componentSyntaxes := componentSyntaxes.push componentSyntax

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

  -- Build the full instance command
  let cmd ← `(
    instance : ProvableStruct $structIdent where
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
