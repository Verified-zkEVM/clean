import Clean.Halo2.Keygen.FloorPlanner.Simple
import Std.Data.HashMap.Lemmas

/-! Kernel-reducible execution of the existing Simple floor planner. The finite
association list is related to its HashMap by every observable getD lookup;
region order, maximum start, and first-empty-row updates are unchanged. -/
namespace Midnight.Math.FloorPlanner.SimplePlacement
open Halo2 Halo2.FloorPlanner

abbrev Bounds := List (RegionColumn × Nat)

def lookup : Bounds → RegionColumn → Nat
  | [], _ => 0
  | (column,value) :: rest, query => if column == query then value else lookup rest query

def write : Bounds → RegionColumn → Nat → Bounds
  | [], column, value => [(column,value)]
  | (old,prior) :: rest, column, value =>
      if old == column then (column,value) :: rest else (old,prior) :: write rest column value

theorem lookup_write (bounds : Bounds) (column : RegionColumn) (value : Nat) (query : RegionColumn) :
    lookup (write bounds column value) query =
      if column == query then value else lookup bounds query := by
  induction bounds with
  | nil => simp [write, lookup]
  | cons entry rest ih =>
    obtain ⟨old,prior⟩ := entry
    by_cases h₁ : old = column <;> by_cases h₂ : column = query <;> by_cases h₃ : old = query <;>
      simp_all [write, lookup]

def Related (hash : Std.HashMap RegionColumn Nat) (bounds : Bounds) : Prop :=
  ∀ column, hash.getD column 0 = lookup bounds column

theorem related_empty : Related (∅ : Std.HashMap RegionColumn Nat) [] := by
  intro column
  simp [lookup]

theorem related_insert {hash : Std.HashMap RegionColumn Nat} {bounds : Bounds}
    (related : Related hash bounds) (column : RegionColumn) (value : Nat) :
    Related (hash.insert column value) (write bounds column value) := by
  intro query
  rw [Std.HashMap.getD_insert, lookup_write, related query]

def modelStep (state : (Bounds × List Nat)) (shape : RegionShape) : (Bounds × List Nat) :=
  let start := shape.columns.foldl (fun row column => max row (lookup state.1 column)) 0
  ⟨shape.columns.foldl (fun bounds column => write bounds column (start + shape.rowCount)) state.1,
    state.2 ++ [start]⟩

def hashStep (state : (Std.HashMap RegionColumn Nat × List Nat)) (shape : RegionShape) :
    (Std.HashMap RegionColumn Nat × List Nat) :=
  let start := shape.columns.foldl (fun row column => max row (state.1.getD column 0)) 0
  ⟨shape.columns.foldl (fun hash column => hash.insert column (start + shape.rowCount)) state.1,
    state.2 ++ [start]⟩

def starts {F : Type} (ops : Operations F) : List Nat :=
  ((measureRegions ops).foldl modelStep ⟨[],[]⟩).2

private theorem writes_related (columns : List RegionColumn) (value : Nat)
    (hash : Std.HashMap RegionColumn Nat) (bounds : Bounds) (related : Related hash bounds) :
    Related (columns.foldl (fun hash column => hash.insert column value) hash)
      (columns.foldl (fun bounds column => write bounds column value) bounds) := by
  induction columns generalizing hash bounds with
  | nil => exact related
  | cons column rest ih =>
    exact ih _ _ (related_insert related column value)

private theorem step_related (hash : Std.HashMap RegionColumn Nat) (bounds : Bounds)
    (out : List Nat) (shape : RegionShape) (related : Related hash bounds) :
    Related (hashStep ⟨hash,out⟩ shape).1 (modelStep ⟨bounds,out⟩ shape).1 ∧
      (hashStep ⟨hash,out⟩ shape).2 = (modelStep ⟨bounds,out⟩ shape).2 := by
  have starts_eq : shape.columns.foldl (fun row column => max row (hash.getD column 0)) 0 =
      shape.columns.foldl (fun row column => max row (lookup bounds column)) 0 := by
    have r : ∀ column, hash.getD column 0 = lookup bounds column := related
    simp only [r]
  simp only [hashStep, modelStep, starts_eq]
  exact ⟨writes_related shape.columns _ hash bounds related, trivial⟩

private theorem fold_related (shapes : List RegionShape) (hash : Std.HashMap RegionColumn Nat)
    (bounds : Bounds) (out : List Nat) (related : Related hash bounds) :
    (shapes.foldl hashStep ⟨hash,out⟩).2 = (shapes.foldl modelStep ⟨bounds,out⟩).2 := by
  induction shapes generalizing hash bounds out with
  | nil => rfl
  | cons shape rest ih =>
    have h := step_related hash bounds out shape related
    simp only [List.foldl_cons]
    change (rest.foldl hashStep ⟨(hashStep ⟨hash,out⟩ shape).1,
      (hashStep ⟨hash,out⟩ shape).2⟩).2 = _
    rw [h.2]
    exact ih (hashStep ⟨hash,out⟩ shape).1 (modelStep ⟨bounds,out⟩ shape).1
      (modelStep ⟨bounds,out⟩ shape).2 h.1

private theorem native_fold {F : Type} (ops : Operations F) :
    SimpleFloorPlanner.starts ops = ((measureRegions ops).foldl hashStep ⟨∅,[]⟩).2 := by
  unfold SimpleFloorPlanner.starts
  simp only [pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure]
  simp only [measureRegions, List.foldl_map, hashStep]

/-- Exact agreement with Clean's original HashMap SimpleFloorPlanner for every
operation stream, not merely a bound or agreement on one pinned example. -/
theorem starts_eq_native {F : Type} (ops : Operations F) :
    starts ops = SimpleFloorPlanner.starts ops := by
  rw [native_fold]
  exact (fold_related (measureRegions ops) ∅ [] [] related_empty).symm

end Midnight.Math.FloorPlanner.SimplePlacement
