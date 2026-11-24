import Midnight.Math.Witness.Execute
import Clean.Halo2.Operations
import Clean.Halo2.Operations.FixedWrites

/-! Relate sequential scalar assignments back to the original Halo2 operation
semantics. Table equations are kept explicit because table loading occurs at
absolute rows and includes default filling. -/
namespace Midnight.Math.Witness.Operations
open Halo2 Execute
variable {F : Type} [FiniteField F]

def regionAssignments (place : RegionIndex → Nat) (self : RegionIndex) :
    RegionOperations F → List (Assignment F)
  | [] => []
  | .assignAdvice column row program :: rest =>
    ⟨(column, (place self + row : Nat)), program⟩ :: regionAssignments place self rest
  | .assignFixed column row value :: rest =>
    ⟨(column, (place self + row : Nat)), .ofFExpr (.const value)⟩ :: regionAssignments place self rest
  | _ :: rest => regionAssignments place self rest

def assignments (place : RegionIndex → Nat) : Operations F → RegionIndex → List (Assignment F)
  | [], _ => []
  | .region _ body :: rest, self => regionAssignments place self body ++ assignments place rest (self+1)
  | _ :: rest, self => assignments place rest self

def tables (env : Environment F) : Operations F → Prop
  | [] => True
  | .loadTable table values :: rest => TableLoaded env table values ∧ tables env rest
  | _ :: rest => tables env rest

theorem satisfies_cons (place : RegionIndex → Nat) (env : ProverEnvironment F)
    (assignment : Assignment F) (rest : List (Assignment F)) :
    Satisfies place env (assignment :: rest) ↔
      read env assignment.destination = (assignment.program.eval ⟨place,env⟩)[0] ∧ Satisfies place env rest := by
  simp [Satisfies, List.mem_cons, forall_eq_or_imp]

theorem satisfies_append (place : RegionIndex → Nat) (env : ProverEnvironment F)
    (first second : List (Assignment F)) :
    Satisfies place env (first ++ second) ↔ Satisfies place env first ∧ Satisfies place env second := by
  simp only [Satisfies, List.mem_append, or_imp, forall_and]

theorem region_satisfies_iff (place : RegionIndex → Nat) (self : RegionIndex)
    (env : ProverEnvironment F) (ops : RegionOperations F) :
    Satisfies place env (regionAssignments place self ops) ↔
      RegionOperations.ExtendsWitnesses place self env ops := by
  induction ops with
  | nil => simp [Satisfies, regionAssignments, RegionOperations.ExtendsWitnesses]
  | cons op rest ih =>
    cases op <;> simp only [regionAssignments, RegionOperations.ExtendsWitnesses,
      RegionOperation.ExtendsWitness, satisfies_cons, Execute.read, Halo2.eval_ofFExpr_zero,
      Witgen.FExprOver.eval, true_and, ih]

/-- All advice and fixed-cell witness equations are exactly the flattened scalar
assignment equations. Table equations remain separately visible. -/
theorem extendsWitnesses_iff (place : RegionIndex → Nat) (self : RegionIndex)
    (env : ProverEnvironment F) (ops : Operations F) :
    ExtendsWitnesses place env ops self ↔
      Satisfies place env (assignments place ops self) ∧ tables env.toEnvironment ops := by
  induction ops generalizing self with
  | nil => simp [ExtendsWitnesses, Satisfies, assignments, tables]
  | cons op rest ih =>
    cases op with
    | region name body =>
      simp only [ExtendsWitnesses, assignments, tables, satisfies_append,
        region_satisfies_iff, ih, and_assoc]
    | constrainInstance _ _ _ =>
      exact ih self
    | loadTable table values =>
      simp only [ExtendsWitnesses, assignments, tables, TableLoaded, ih]
      tauto

theorem tables_congr (left right : Environment F) (ops : Operations F)
    (rows : left.usableRows = right.usableRows)
    (columns : ∀ column ∈ ops.loadedTableColumns.map Column.toAny, ∀ row : Int,
      left.get column row = right.get column row) :
    tables left ops ↔ tables right ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | region _ _ => exact ih columns
    | constrainInstance _ _ _ => exact ih columns
    | loadTable table values =>
      have tail := ih fun col member => columns col (by
        rw [Operations.loadedTableColumns_loadTable_cons, List.map_append]
        exact List.mem_append_right _ member)
      by_cases empty : values = []
      · subst empty
        simp [tables, TableLoaded, tail]
      · have column := columns table.inner.toAny (by
          simp [Operations.loadedTableColumns_loadTable_cons, empty])
        simp only [tables, TableLoaded, Environment.fixed, column, rows, tail]

/-- Construct an extending environment for the original operations from the
syntactic dependency check and initially loaded fixed tables. Columns with a
nonempty table load must be disjoint from the scalar assignment write set. -/
theorem run_extendsWitnesses (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : Operations F) (known : List Address)
    (valid : ordered place known (assignments place ops self) = true)
    (initial : ProverEnvironment F) (loaded : tables initial.toEnvironment ops)
    (separate : ∀ assignment ∈ assignments place ops self,
      assignment.destination.1 ∉ ops.loadedTableColumns.map Column.toAny) :
    ExtendsWitnesses place (run place (assignments place ops self) initial) ops self := by
  apply (extendsWitnesses_iff place self _ ops).mpr
  refine ⟨run_satisfies place _ known valid initial, ?_⟩
  apply (tables_congr (run place (assignments place ops self) initial).toEnvironment
    initial.toEnvironment ops (run_usableRows place _ initial) ?_).mpr loaded
  intro column member row
  have preserved := run_preserves_unwritten place (assignments place ops self) initial (column,row) ?_
  · exact preserved
  · intro assignment present same
    have colEq := congrArg Prod.fst same
    exact separate assignment present (colEq ▸ member)

end Midnight.Math.Witness.Operations
