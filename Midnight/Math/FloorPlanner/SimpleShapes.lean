import Midnight.Math.FloorPlanner.SimplePlacement

/-! Compact shape observation for the exact Simple floor planner. Only touched
physical/selector columns and row extents survive the observation; witness
programs, fixed values, gate polynomials and lookup expressions are discarded.
Every region contributes one shape, even when empty. Table loads and public
instance constraints do not consume a region or affect its placement. -/
namespace Midnight.Math.FloorPlanner.SimpleShapes
open Halo2 Halo2.FloorPlanner
variable {F G : Type}

/-- The two placement-relevant fields of the actual region summary. -/
def region : RegionOperations F → RegionShapeSummary
  | [] => ⟨[],0⟩
  | operation :: rest =>
      let tail := region rest
      ⟨unionColumns (unionColumns [] (regionOperationShapeColumns operation)) tail.columns,
        max (regionOperationRowExtent operation) tail.rowCount⟩

theorem region_eq (body : RegionOperations F) :
    region body = (regionSynthesisSummary body).toRegionShapeSummary := by
  induction body with
  | nil => rfl
  | cons operation rest ih =>
    rw [region, ih]
    rfl

/-- Ordered, index-free shapes, retaining empty regions exactly. -/
def observe : Operations F → List RegionShapeSummary
  | [] => []
  | .region _ body :: rest => region body :: observe rest
  | _ :: rest => observe rest

theorem observe_append (left right : Operations F) :
    observe (left ++ right) = observe left ++ observe right := by
  induction left with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;> simp only [List.cons_append, observe, ih, List.cons_append]

theorem observe_eq (ops : Operations F) :
    observe ops = (synthesisSummary ops).regionShapes := by
  induction ops with
  | nil => rfl
  | cons operation rest ih =>
    cases operation <;>
      simp only [observe, synthesisSummary, SynthesisSummary.combine_regionShapes,
        SynthesisSummary.ofRegion_regionShapes, List.singleton_append, region_eq, ih]
    all_goals rfl

/-- Execute the proven association-list planner on compact shapes alone. -/
def starts (shapes : List RegionShapeSummary) : List Nat :=
  ((indexRegionSummaries 0 shapes).foldl SimplePlacement.modelStep ⟨[],[]⟩).2

theorem starts_observe (ops : Operations F) :
    starts (observe ops) = SimplePlacement.starts ops := by
  rw [observe_eq]
  unfold starts SimplePlacement.starts
  rw [measureRegions_eq_synthesisSummary_regionShapes]

theorem starts_observe_native (ops : Operations F) :
    starts (observe ops) = SimpleFloorPlanner.starts ops :=
  (starts_observe ops).trans (SimplePlacement.starts_eq_native ops)

/-- A source-linked compact shape certificate determines the exact placement. -/
theorem starts_eq_of_observe_eq (ops : Operations F) (shapes : List RegionShapeSummary)
    (observed : observe ops = shapes) : SimplePlacement.starts ops = starts shapes := by
  rw [← observed, starts_observe]

/-- No value-level agreement is needed once the actual shape streams agree. -/
theorem source_starts_eq (left : Operations F) (right : Operations G)
    (same : observe left = observe right) :
    SimplePlacement.starts left = SimplePlacement.starts right := by
  rw [← starts_observe, ← starts_observe, same]

end Midnight.Math.FloorPlanner.SimpleShapes
