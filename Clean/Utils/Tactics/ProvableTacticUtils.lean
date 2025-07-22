import Lean
import Clean.Circuit.Provable

open Lean Meta Elab Tactic

namespace ProvenZK

/-- Check if an expression is a constructor application (ends with .mk) -/
def isMkConstructor (e : Expr) : MetaM Bool := do
  let e' ← withTransparency .all (whnf e)
  match e'.getAppFn with
  | .const name _ =>
    -- Check if it's a constructor (ends with .mk)
    return name.components.getLast? == some `mk
  | _ => return false

/-- Check if an expression is specifically a Prod.mk application -/
def isProdMkApp (e : Expr) : MetaM Bool := do
  let e' ← withTransparency .all (whnf e)
  match e'.getAppFn with
  | .const name _ =>
    return name == ``Prod.mk
  | _ => return false

/-- Extract all equalities from an expression (including inside conjunctions) -/
partial def extractEqualities (e : Expr) : MetaM (List (Expr × Expr × Expr)) := do
  -- Returns list of (equality_expr, lhs, rhs) triples
  match e with
  | .app (.app (.const ``And _) left) right =>
    -- Handle conjunction
    let leftEqs ← extractEqualities left
    let rightEqs ← extractEqualities right
    return leftEqs ++ rightEqs
  | _ =>
    -- Check if it's an equality
    if e.isAppOf `Eq then
      if let (some lhs, some rhs) := (e.getArg? 1, e.getArg? 2) then
        return [(e, lhs, rhs)]
    return []

/-- Check if a type has a ProvableStruct instance, handling parameterized types -/
def hasProvableStructInstance (type : Expr) : MetaM Bool := do
  let type' ← withTransparency .reducible (whnf type)
  -- For types like MyStruct n (F p), check ProvableStruct (MyStruct n)
  match type' with
  | .app typeCtor _ =>
    try
      let instType ← mkAppM ``ProvableStruct #[typeCtor]
      match ← trySynthInstance instType with
      | .some _ => return true
      | _ => return false
    catch _ => return false
  | _ => return false


/-- Check if expression contains eval pattern (ProvableType.eval, Expression.eval, or ProvableStruct.eval) -/
def hasEvalPattern (e : Expr) : Bool :=
  e.isAppOf ``ProvableType.eval || e.isAppOf ``Expression.eval || e.isAppOf ``ProvableStruct.eval

/-- Extract type map candidates from a type for ProvableType/ProvableStruct checking -/
def extractTypeMapCandidates (type : Expr) : MetaM (List Expr) := do
  -- If type looks like `SomeType F` where F might be a field,
  -- return [SomeType] as a candidate TypeMap
  match type with
  | .app f _ => return [f]
  | _ => return []

/-- Check if a type is an Expression type with Field instance -/
def isExpressionType (type : Expr) : MetaM Bool := do
  match type with
  | .app (.const ``Expression _) fieldType =>
    -- Expression F requires Field F
    let fieldClass ← mkAppM ``Field #[fieldType]
    match ← trySynthInstance fieldClass with
    | .some _ => return true
    | _ => return false
  | _ => return false

/-- Check if a type has Field instance -/
def hasFieldInstance (type : Expr) : MetaM Bool := do
  let fieldClass ← mkAppM ``Field #[type]
  match ← trySynthInstance fieldClass with
  | .some _ => return true
  | _ => return false

/-- Generate component names for a decomposed variable -/
def generateComponentNames (baseName : Name) (numComponents : Nat) : List Name :=
  match numComponents with
  | 2 => [
      Name.mkSimple (baseName.toString ++ "_fst"),
      Name.mkSimple (baseName.toString ++ "_snd")
    ]
  | 3 => [
      Name.mkSimple (baseName.toString ++ "_fst"),
      Name.mkSimple (baseName.toString ++ "_snd"),
      Name.mkSimple (baseName.toString ++ "_thd")
    ]
  | _ => List.range numComponents |>.map fun i =>
      Name.mkSimple (baseName.toString ++ "_" ++ toString (i + 1))

end ProvenZK
