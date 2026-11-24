import Midnight.Math.Witness.DependencySnapshot
import Lean
/-! Materialize candidate snapshot data with shared constructor nodes.
Each consumer retains its kernel-checked equality against the source transition.
The persistent cache only reuses safe data definitions across imported modules. -/
namespace Midnight.Math.Witness.DependencySnapshot
open Lean Elab Term Meta
/-- Structural identity includes both child declarations and all stored metadata. -/
private structure NodeKey where
  size : Nat
  address : Key
  left : Name
  right : Name
  deriving BEq, Hashable
private abbrev Entry := NodeKey × Name
private initialize nodeCache : SimplePersistentEnvExtension Entry (Std.HashMap NodeKey Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.1 entry.2
    addImportedFn := fun entries => entries.foldl
      (fun state group => group.foldl (fun state entry => state.insert entry.1 entry.2) state) {} }
private def leafData : Raw := .leaf
private def materialize : Raw → TermElabM Name
  | .leaf => pure ``leafData
  | .inner size address _ left right => do
    let left ← materialize left
    let right ← materialize right
    let key := NodeKey.mk size address left right
    if let some name := (nodeCache.getState (← getEnv))[key]? then return name
    let name ← mkAuxName `snapshotNode
    let domain := Lean.mkConst ``Key
    let value := mkAppN (Lean.mkConst ``Std.DTreeMap.Internal.Impl.inner [0, 0])
      #[domain, mkLambda `key .default domain (Lean.mkConst ``Unit),
        toExpr size, toExpr address, Lean.mkConst ``Unit.unit,
        Lean.mkConst left, Lean.mkConst right]
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := Lean.mkConst ``Raw, value,
      hints := .regular 0, safety := .safe }
    modifyEnv fun env => nodeCache.addEntry env (key, name)
    return name
/-- Native evaluation supplies candidate data only. The caller's existing
`equal_eq_true` proof checks its relation to the actual source transition. -/
elab "dependency_snapshot% " value:term : term => do
  let type := Lean.mkConst ``Raw
  let expression ← elabTermAndSynthesize value (some type)
  let data ← unsafe evalExpr Raw type expression
  return Lean.mkConst (← materialize data)
/-- `dependency_snapshot_step x tree from prev` certifies chunk `xPhysical` run
after `prev`: it materializes `tree`, proves `xAdvanced` by kernel equality,
defines `xAfter` from it and proves `xAfter_eq` by `restore_eq`. -/
elab "dependency_snapshot_step " base:ident tree:ident " from " prev:term:max : command => do
  let .str .anonymous stem := base.getId | throwError "expected an unqualified chunk name"
  let name (suffix : String) := mkIdentFrom base (.str .anonymous (stem ++ suffix))
  let physical := name "Physical"
  let advanced := name "Advanced"
  let after := name "After"
  let afterEq := name "After_eq"
  Command.elabCommand (← `(def $tree : Midnight.Math.Witness.DependencySnapshot.Raw :=
    dependency_snapshot% Midnight.Math.Witness.DependencySnapshot.raw
      (Midnight.Math.Witness.DependencyPlan.advance $prev $physical)))
  Command.elabCommand (← `(theorem $advanced : Midnight.Math.Witness.DependencySnapshot.raw
      (Midnight.Math.Witness.DependencyPlan.advance $prev $physical) = $tree := by
    apply (Midnight.Math.Witness.DependencySnapshot.equal_eq_true _ _).mp
    decide +kernel))
  -- `restore` inlined: `cbv` order checks would otherwise evaluate its state argument.
  Command.elabCommand (← `(def $after : Midnight.Math.Witness.DependencySnapshot.State :=
    ⟨⟨⟨$tree, $advanced ▸
      (Midnight.Math.Witness.DependencyPlan.advance $prev $physical).inner.inner.wf⟩⟩⟩))
  Command.elabCommand (← `(theorem $afterEq :
      Midnight.Math.Witness.DependencyPlan.advance $prev $physical = $after :=
    (Midnight.Math.Witness.DependencySnapshot.restore_eq _ _ $advanced).symm))
end Midnight.Math.Witness.DependencySnapshot
