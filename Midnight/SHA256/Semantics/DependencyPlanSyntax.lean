import Midnight.Field
import Midnight.Math.Witness.CompactPlan
import Lean

/-! Source-derived dependency-plan data. The evaluator returns constructor data;
its result supplies no proof and adds no native-computation proof axiom. -/
namespace Midnight.SHA256.Semantics.DependencyPlanSyntax
open Lean Elab Term Meta Halo2 Midnight.Math.Witness
private instance : ToExpr AnyColumn where
  toTypeExpr := Lean.mkConst ``AnyColumn
  toExpr column := mkApp2 (Lean.mkConst ``AnyColumn.mk)
    (Lean.mkConst (match column.kind with
      | .advice => ``ColumnKind.advice | .fixed => ``ColumnKind.fixed
      | .instance => ``ColumnKind.instance)) (toExpr column.index)

private instance : ToExpr (AssignedCell F) where
  toTypeExpr := mkApp (Lean.mkConst ``AssignedCell) (Lean.mkConst ``F)
  toExpr assigned := mkApp2 (Lean.mkConst ``AssignedCell.mk) (Lean.mkConst ``F)
    (mkApp3 (Lean.mkConst ``Cell.mk) (toExpr assigned.cell.regionIndex)
      (toExpr assigned.cell.rowOffset) (toExpr assigned.cell.column))

private instance : ToExpr (RegionPlan.RelativeAssignment F) where
  toTypeExpr := mkApp (Lean.mkConst ``RegionPlan.RelativeAssignment) (Lean.mkConst ``F)
  toExpr assignment := mkApp4 (Lean.mkConst ``RegionPlan.RelativeAssignment.mk)
    (Lean.mkConst ``F) (toExpr assignment.column) (toExpr assignment.row) (toExpr assignment.reads)

/-- Construct candidate coordinate data. Consumers still prove exact agreement
with the source observation and all ordering requirements in the kernel. -/
elab "dependency_plan% " value:term : term => do
  let type := toTypeExpr (List (List (RegionPlan.RelativeAssignment F)))
  let expression ← elabTermAndSynthesize value (some type)
  let plan ← unsafe evalExpr (List (List (RegionPlan.RelativeAssignment F))) type expression
  return toExpr plan

end Midnight.SHA256.Semantics.DependencyPlanSyntax
