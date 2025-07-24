import Lean.Elab.Tactic
import Lean.Meta
import Lean.Structure

open Lean Meta

namespace ProvableStructNaming

/--
  Get field names from a structure type
-/
def getStructureFieldNames (structName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  match getStructureInfo? env structName with
  | some _ => 
    -- Get the field names from the structure
    return getStructureFields env structName
  | none => throwError "Not a structure: {structName}"

/--
  Generate field-based variable names from original variable name and field names
  For example: input with fields [x, y, z] → [input_x, input_y, input_z]
-/
def generateFieldBasedNames (baseName : Name) (fieldNames : Array Name) : Array Name :=
  fieldNames.map fun fieldName => baseName.appendAfter s!"_{fieldName}"

/--
  Generate custom field-based names for a structure variable.
  Returns the AltVarNames structure needed for MVarId.cases.
-/
def generateStructFieldNames (fvarId : FVarId) : MetaM AltVarNames := do
  let localDecl ← fvarId.getDecl
  let userName := localDecl.userName
  
  -- Get the type of the variable to extract structure name
  let varType ← inferType (.fvar fvarId)
  let varType' ← whnf varType
  
  -- Extract the structure name
  let structName ← match varType' with
  | .app (.const name _) _ => pure name
  | .const name _ => pure name
  | _ => throwError "Cannot extract structure name from type: {varType'}"
  
  -- Get field names for the structure
  let fieldNames ← getStructureFieldNames structName
  
  -- Generate field-based names
  let customNames := generateFieldBasedNames userName fieldNames
  
  -- Create AltVarNames for the single constructor case
  return { varNames := customNames.toList }

end ProvableStructNaming