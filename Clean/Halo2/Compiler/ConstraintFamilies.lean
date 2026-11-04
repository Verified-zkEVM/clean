import Clean.Halo2.Operations
import Mathlib.Tactic.Tauto

/-!
# Full Halo2 circuit satisfaction, split by constraint family

The SNARK constraint polynomial separates custom gates, the permutation argument, and lookup
arguments.  Clean's operation semantics, however, exposes one authoritative
`Halo2.Constraints` predicate.  This file gives that predicate a lossless family decomposition:

* `gate` — enabled custom-gate polynomials;
* `copy` — equality, constant, and instance copies;
* `lookup` — enabled lookup membership;
* `fixed` — fixed assignments and loaded-table contents.

Witness-only advice assignments belong to no family because their constraint is `True`.  The
decomposition does not weaken or replace Clean semantics:
`CircuitConstraintFamily.operations_constraints_iff` proves exact equivalence.
-/

namespace Halo2

/-- The four semantic families carried by a complete circuit-satisfaction result. -/
inductive CircuitConstraintFamily where
  | gate
  | copy
  | lookup
  | fixed
deriving DecidableEq, Repr

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- One region operation's contribution to a selected constraint family. -/
def regionConstraint (family : CircuitConstraintFamily)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperation F → Prop
  | op@(.enableGate _ _) =>
      if family = .gate then op.Constraints place self env else True
  | op@(.constrainEqual _ _) =>
      if family = .copy then op.Constraints place self env else True
  | op@(.constrainConstant _ _) =>
      if family = .copy then op.Constraints place self env else True
  | op@(.constrainInstance _ _ _) =>
      if family = .copy then op.Constraints place self env else True
  | op@(.enableLookup _ _ _) =>
      if family = .lookup then op.Constraints place self env else True
  | op@(.assignFixed _ _ _) =>
      if family = .fixed then op.Constraints place self env else True
  | .assignAdvice _ _ _ => True

/-- A region operation satisfies all four family projections exactly when it satisfies Clean's
authoritative operation constraint. -/
theorem regionOperation_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (op : RegionOperation F) :
    op.Constraints place self env ↔
      regionConstraint .gate place self env op ∧
      regionConstraint .copy place self env op ∧
      regionConstraint .lookup place self env op ∧
      regionConstraint .fixed place self env op := by
  cases op <;> simp [regionConstraint, RegionOperation.Constraints]

/-- One family over a complete region-operation list. -/
def regionConstraints (family : CircuitConstraintFamily)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F) :
    RegionOperations F → Prop
  | [] => True
  | op :: rest =>
      regionConstraint family place self env op ∧
        regionConstraints family place self env rest

/-- Splitting a complete region by family loses no constraints. -/
theorem regionOperations_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    RegionOperations.Constraints place self env ops ↔
      regionConstraints .gate place self env ops ∧
      regionConstraints .copy place self env ops ∧
      regionConstraints .lookup place self env ops ∧
      regionConstraints .fixed place self env ops := by
  induction ops with
  | nil => simp [RegionOperations.Constraints, regionConstraints]
  | cons op rest ih =>
      rw [RegionOperations.Constraints, ih]
      rw [regionOperation_constraints_iff]
      simp only [regionConstraints]
      tauto

/-- One family over the complete layouter operation stream, with the same region-index threading as
`Halo2.Constraints`. -/
def constraints (family : CircuitConstraintFamily)
    (place : RegionIndex → ℕ) (env : Environment F) :
    Operations F → RegionIndex → Prop
  | [], _ => True
  | .region _ body :: rest, i =>
      regionConstraints family place i env body ∧
        constraints family place env rest (i + 1)
  | op@(.constrainInstance _ _ _) :: rest, i =>
      (if family = .copy then
        match op with
        | .constrainInstance cell col row =>
            cell.eval place env = env.get col row
        | _ => True
       else True) ∧ constraints family place env rest i
  | .loadTable table values :: rest, i =>
      (if family = .fixed then
        (∀ r : ℕ, r < values.length →
          env.fixed table.inner (r : ℤ) = values[r]!) ∧
        (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
          env.fixed table.inner (r : ℤ) = values[0]!)
       else True) ∧ constraints family place env rest i

/-- The four layouter-level family projections are exactly `Halo2.Constraints`. -/
theorem operations_constraints_iff
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    Halo2.Constraints place env ops i ↔
      constraints .gate place env ops i ∧
      constraints .copy place env ops i ∧
      constraints .lookup place env ops i ∧
      constraints .fixed place env ops i := by
  induction ops generalizing i with
  | nil => simp [Halo2.Constraints, constraints]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [Halo2.Constraints, ih, regionOperations_constraints_iff]
          simp [constraints]
          tauto
      | constrainInstance cell col row =>
          rw [Halo2.Constraints, ih]
          simp [constraints]
          tauto
      | loadTable table values =>
          rw [Halo2.Constraints, ih]
          simp [constraints]
          tauto

end CircuitConstraintFamily

end Halo2
