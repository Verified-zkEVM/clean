import Midnight.Math.FloorPlanner.SimpleShapes

/-! Exact chunking law for the Simple placement computation. A chunk carries only
the current per-column first-free rows; already emitted starts are appended by
proof, so closed checks do not repeatedly normalize the entire output prefix. -/
namespace Midnight.Math.FloorPlanner.SimpleChunks
open Halo2 Halo2.FloorPlanner SimplePlacement

abbrev State := Bounds × List Nat

def step (state : State) (shape : RegionShapeSummary) : State :=
  modelStep state (measureRegionSummary 0 shape)

def prependStarts (earlier : List Nat) (state : State) : State :=
  ⟨state.1, earlier ++ state.2⟩

theorem step_prefix (earlier : List Nat) (state : State) (shape : RegionShapeSummary) :
    step (prependStarts earlier state) shape = prependStarts earlier (step state shape) := by
  simp only [step, prependStarts, modelStep, List.append_assoc]

theorem fold_prefix (earlier : List Nat) (state : State) (shapes : List RegionShapeSummary) :
    shapes.foldl step (prependStarts earlier state) = prependStarts earlier (shapes.foldl step state) := by
  induction shapes generalizing state with
  | nil => rfl
  | cons shape rest ih => simp only [List.foldl_cons, step_prefix, ih]

def run (bounds : Bounds) (shapes : List RegionShapeSummary) : State :=
  shapes.foldl step ⟨bounds, []⟩

theorem indexed_fold (shapes : List RegionShapeSummary) (index : Nat) (state : State) :
    (indexRegionSummaries index shapes).foldl modelStep state = shapes.foldl step state := by
  induction shapes generalizing index state with
  | nil => rfl
  | cons shape rest ih =>
      simp only [indexRegionSummaries, List.foldl_cons, ih]
      rfl

theorem starts_eq (shapes : List RegionShapeSummary) :
    SimpleShapes.starts shapes = (run [] shapes).2 := by
  unfold SimpleShapes.starts run
  rw [indexed_fold]

theorem run_append (bounds : Bounds) (left right : List RegionShapeSummary) :
    run bounds (left ++ right) = prependStarts (run bounds left).2 (run (run bounds left).1 right) := by
  unfold run
  rw [List.foldl_append]
  have hp : left.foldl step ⟨bounds, []⟩ = prependStarts (left.foldl step ⟨bounds, []⟩).2
      ⟨(left.foldl step ⟨bounds, []⟩).1, []⟩ := by simp [prependStarts]
  conv_lhs => rw [hp]
  exact fold_prefix _ _ _

theorem run_append_of (bounds next final : Bounds) (left right : List RegionShapeSummary)
    (leftStarts rightStarts : List Nat)
    (hl : run bounds left = ⟨next, leftStarts⟩)
    (hr : run next right = ⟨final, rightStarts⟩) :
    run bounds (left ++ right) = ⟨final, leftStarts ++ rightStarts⟩ := by
  rw [run_append, hl]
  change prependStarts leftStarts (run next right) = _
  rw [hr]
  rfl

end Midnight.Math.FloorPlanner.SimpleChunks
