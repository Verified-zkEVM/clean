import Midnight.Chips.SynthesisShapeLawful
import Midnight.Math.FloorPlanner.SimpleShapes

/-! Placement observation of the source-linked structural schedule. Fixed values,
copy endpoints and constraint polynomials are irrelevant to placement; selector
activation footprints are retained explicitly and must match the actual callback. -/
namespace Midnight.Chips.SynthesisShapePlacement
open Halo2 Halo2.FloorPlanner Midnight.Math.FloorPlanner

abbrev Footprint := RegionShapeSummary

def footprint (operation : RegionOperation F) : Footprint :=
  ⟨regionOperationShapeColumns operation, regionOperationRowExtent operation⟩

def summarize : List Footprint → RegionShapeSummary
  | [] => ⟨[], 0⟩
  | head :: tail =>
      let rest := summarize tail
      ⟨unionColumns (unionColumns [] head.columns) rest.columns, max head.rowCount rest.rowCount⟩

theorem summarize_map (operations : RegionOperations F) :
    summarize (operations.map footprint) = SimpleShapes.region operations := by
  induction operations with
  | nil => rfl
  | cons operation rest ih =>
      simp only [List.map_cons, summarize, SimpleShapes.region, ← ih, footprint]

def instruction (activation : Nat → Nat → List Footprint) :
    SynthesisCheckpoint.Instruction → List Footprint
  | .advice column row => [⟨[.column .advice column], row + 1⟩]
  | .fixed column row => [⟨[.column .fixed column], row + 1⟩]
  | .selector selector row => activation selector row
  | .copy _ _ => [⟨[], 0⟩]

def region (activation : Nat → Nat → List Footprint)
    (body : List SynthesisCheckpoint.Instruction) : RegionShapeSummary :=
  summarize (body.flatMap (instruction activation))

def observe (activation : Nat → Nat → List Footprint) :
    List SynthesisCheckpoint.Step → List RegionShapeSummary
  | [] => []
  | .region _ body :: rest => region activation body :: observe activation rest
  | .publicInput _ _ :: rest => observe activation rest

theorem observe_append (activation : Nat → Nat → List Footprint)
    (left right : List SynthesisCheckpoint.Step) :
    observe activation (left ++ right) = observe activation left ++ observe activation right := by
  induction left with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp only [List.cons_append, observe, ih, List.cons_append]

theorem lower_instruction (activate : Nat → Nat → RegionOperations F)
    (activation : Nat → Nat → List Footprint)
    (matching : ∀ selector row, (activate selector row).map footprint = activation selector row)
    (entry : Synthesis.Instruction) :
    (SynthesisShapeLawful.lowerInstruction activate entry).map footprint =
      instruction activation (SynthesisCheckpoint.instruction entry) := by
  cases entry <;> first | exact matching _ _ | rfl

theorem lower_region (activate : Nat → Nat → RegionOperations F)
    (activation : Nat → Nat → List Footprint)
    (matching : ∀ selector row, (activate selector row).map footprint = activation selector row)
    (body : List Synthesis.Instruction) :
    SimpleShapes.region (SynthesisShapeLawful.lowerRegion activate body) =
      region activation (body.map SynthesisCheckpoint.instruction) := by
  rw [← summarize_map]
  unfold region
  congr 1
  simp only [SynthesisShapeLawful.lowerRegion, List.map_flatMap, List.flatMap_map]
  simp only [lower_instruction activate activation matching]

theorem lower_observe (activate : Nat → Nat → RegionOperations F)
    (activation : Nat → Nat → List Footprint)
    (matching : ∀ selector row, (activate selector row).map footprint = activation selector row)
    (steps : List Synthesis.Step) :
    SimpleShapes.observe (SynthesisShapeLawful.lower activate steps) =
      observe activation (steps.map SynthesisCheckpoint.step) := by
  induction steps with
  | nil => rfl
  | cons entry rest ih =>
      cases entry <;> simp only [SynthesisShapeLawful.lower, List.map_cons,
        SynthesisCheckpoint.step, SimpleShapes.observe, observe, lower_region _ _ matching, ih]

theorem schedule_observe (schedule : Array Synthesis.Step)
    (activate : Nat → Nat → RegionOperations F) (activation : Nat → Nat → List Footprint)
    (matching : ∀ selector row, (activate selector row).map footprint = activation selector row) :
    SimpleShapes.observe (Synthesis.scheduleToOperations schedule activate) =
      observe activation (SynthesisCheckpoint.shape schedule) := by
  rw [← SynthesisShapeLawful.lower_eq]
  exact lower_observe activate activation matching schedule.toList

end Midnight.Chips.SynthesisShapePlacement
