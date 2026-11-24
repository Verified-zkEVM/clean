import Midnight.Chips.SynthesisShapePlacement
import Midnight.SHA256.Configure
import Midnight.SHA256.SynthesisLayout
import Midnight.SHA256.Semantics.StructuralComposition

/-! Placement computed from the kernel-certified source structure. The only
configuration data retained are actual selector indices, checked against the
configured Clean objects. No captured layout or witness values are inputs. -/
namespace Midnight.SHA256.Semantics.StructuralPlacement
open Halo2 Halo2.FloorPlanner Midnight.Math.FloorPlanner
open Chips.SynthesisShapePlacement

set_option Elab.async false

def gateSelectors : List Nat := [0, 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def lookupSelectors : List Nat := [3, 4, 4]

theorem gateSelectors_eq : cleanGates.map (·.selector.index) = gateSelectors := by decide +kernel
theorem lookupSelectors_eq : cleanLookups.map (·.masterSelector.index) = lookupSelectors := by decide +kernel

/-- Preserve all emitted activations, including both tuples of selector 4. -/
def activationShapes (selector row : Nat) : List Footprint :=
  ((gateSelectors.filter (· == selector)).map fun index => ⟨[.selector index], row + 1⟩) ++
  ((lookupSelectors.filter (· == selector)).map fun _ => ⟨[.selector selector], row + 1⟩)

attribute [local irreducible] cleanGates cleanLookups Synthesis.schedule StructuralComposition.fullChunk

theorem activation_shapes (selector row : Nat) :
    (activation selector row).map footprint = activationShapes selector row := by
  unfold activationShapes
  rw [← gateSelectors_eq, ← lookupSelectors_eq]
  simp only [activation, List.map_append, List.map_map, List.filter_map, Function.comp_def,
    footprint, regionOperationShapeColumns, regionOperationRowExtent, List.map_cons, List.map_nil]

def shapes : List RegionShapeSummary :=
  observe activationShapes StructuralComposition.fullChunk

theorem source_shapes :
    SimpleShapes.observe (Synthesis.operations activation) = shapes := by
  unfold Synthesis.operations Synthesis.toOperations
  rw [SimpleShapes.observe_append, schedule_observe _ _ _ activation_shapes,
    StructuralComposition.sourceShape]
  change observe activationShapes StructuralComposition.fullChunk ++ [] = shapes
  exact List.append_nil _

def starts : List Nat := SimpleShapes.starts shapes

end Midnight.SHA256.Semantics.StructuralPlacement
