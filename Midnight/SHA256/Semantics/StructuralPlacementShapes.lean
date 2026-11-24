import Midnight.SHA256.Semantics.StructuralPlacement

/-! Generated from the proven source expression (the generator is not part of this repository).
Every chunk projection and the
final placement calculation are kernel-checked below. No captured/native layout
is an input to the generator or a hypothesis of the proofs. -/
namespace Midnight.SHA256.Semantics.StructuralPlacementShapes
open Halo2 Halo2.FloorPlanner Midnight.Math.FloorPlanner
open Chips.SynthesisShapePlacement StructuralCheckpoints
set_option Elab.async false
private def shape0 : RegionShapeSummary := ⟨[.selector 3, .column .fixed 10, .column .advice 1], 1⟩
private def shape1 : RegionShapeSummary := ⟨[.column .fixed 9], 1⟩
private def shape2 : RegionShapeSummary := ⟨[.column .advice 0, .column .advice 1, .column .advice 2, .column .advice 3, .column .advice 4, .selector 0, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 0, .column .fixed 1, .column .fixed 2, .column .fixed 3], 1⟩
private def shape3 : RegionShapeSummary := ⟨[.column .advice 0, .column .advice 1, .selector 0, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 0, .column .fixed 1, .column .fixed 2, .column .fixed 3], 1⟩
private def shape4 : RegionShapeSummary := ⟨[.selector 14, .selector 15, .column .advice 3, .column .advice 4, .column .advice 2, .selector 4, .column .fixed 1, .column .advice 7, .column .advice 1, .column .fixed 0, .column .advice 6, .column .advice 0, .column .advice 5], 3⟩
private def shape5 : RegionShapeSummary := ⟨[.selector 9, .column .advice 3, .column .advice 4, .column .advice 2, .selector 11, .selector 4, .column .fixed 0, .column .advice 6, .column .advice 0, .column .fixed 1, .column .advice 7, .column .advice 1], 3⟩
private def shape6 : RegionShapeSummary := ⟨[.selector 10, .column .advice 3, .column .advice 4, .column .advice 2, .selector 11, .selector 4, .column .fixed 0, .column .advice 6, .column .advice 0, .column .fixed 1, .column .advice 7, .column .advice 1], 3⟩
private def shape7 : RegionShapeSummary := ⟨[.selector 7, .column .advice 3, .column .advice 4, .selector 11, .selector 4, .column .fixed 0, .column .advice 6, .column .advice 0, .column .fixed 1, .column .advice 7, .column .advice 1, .column .advice 2], 3⟩
private def shape8 : RegionShapeSummary := ⟨[.selector 5, .column .advice 3, .column .advice 4, .selector 11, .selector 4, .column .fixed 1, .column .advice 7, .column .advice 1, .column .fixed 0, .column .advice 6, .column .advice 0, .column .advice 2], 3⟩
private def shape9 : RegionShapeSummary := ⟨[.selector 8, .column .advice 3, .column .advice 4, .selector 11, .selector 4, .column .fixed 0, .column .advice 6, .column .advice 0, .column .fixed 1, .column .advice 7, .column .advice 1, .column .advice 2], 3⟩
private def shape10 : RegionShapeSummary := ⟨[.selector 6, .column .advice 3, .column .advice 2, .column .advice 4, .selector 11, .selector 4, .column .fixed 1, .column .advice 7, .column .advice 1, .column .fixed 0, .column .advice 6, .column .advice 0], 6⟩
private def shape11 : RegionShapeSummary := ⟨[.selector 12, .selector 15, .column .advice 3, .column .advice 4, .column .advice 2, .selector 4, .column .fixed 1, .column .advice 7, .column .advice 1, .column .fixed 0, .column .advice 6, .column .advice 0], 3⟩
private def shape12 : RegionShapeSummary := ⟨[.selector 13, .selector 15, .column .advice 3, .column .advice 4, .column .advice 2, .selector 4, .column .fixed 1, .column .advice 7, .column .advice 1, .column .fixed 0, .column .advice 6, .column .advice 0], 3⟩
private def shape13 : RegionShapeSummary := ⟨[.column .advice 0, .column .advice 1, .selector 0, .column .fixed 4, .column .fixed 5, .column .fixed 6, .column .fixed 7, .column .fixed 8, .column .fixed 0, .column .fixed 1, .column .fixed 2, .column .fixed 3, .selector 3, .column .fixed 10], 4⟩
private def shape14 : RegionShapeSummary := ⟨[], 0⟩

def inputShapes : List RegionShapeSummary := [shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0, shape0]
theorem input_shapes : observe StructuralPlacement.activationShapes inputChunk = inputShapes := by cbv

def initialShapes : List RegionShapeSummary := [shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1, shape1]
theorem initial_shapes : observe StructuralPlacement.activationShapes initialChunk = initialShapes := by cbv

def paddingShapes : List RegionShapeSummary := [shape1, shape1, shape1]
theorem padding_shapes : observe StructuralPlacement.activationShapes paddingChunk = paddingShapes := by cbv

def packingShapes : List RegionShapeSummary := [shape2, shape2, shape2, shape2, shape2, shape2, shape3]
theorem packing_shapes : observe StructuralPlacement.activationShapes packingChunk = packingShapes := by cbv

def prepare0Shapes : List RegionShapeSummary := [shape4]
theorem prepare0_shapes : observe StructuralPlacement.activationShapes prepare0Chunk = prepare0Shapes := by cbv

def prepare1Shapes : List RegionShapeSummary := [shape4]
theorem prepare1_shapes : observe StructuralPlacement.activationShapes prepare1Chunk = prepare1Shapes := by cbv

def prepare2Shapes : List RegionShapeSummary := [shape4]
theorem prepare2_shapes : observe StructuralPlacement.activationShapes prepare2Chunk = prepare2Shapes := by cbv

def prepare3Shapes : List RegionShapeSummary := [shape4]
theorem prepare3_shapes : observe StructuralPlacement.activationShapes prepare3Chunk = prepare3Shapes := by cbv

def prepare4Shapes : List RegionShapeSummary := [shape4]
theorem prepare4_shapes : observe StructuralPlacement.activationShapes prepare4Chunk = prepare4Shapes := by cbv

def prepare5Shapes : List RegionShapeSummary := [shape4]
theorem prepare5_shapes : observe StructuralPlacement.activationShapes prepare5Chunk = prepare5Shapes := by cbv

def prepare6Shapes : List RegionShapeSummary := [shape4]
theorem prepare6_shapes : observe StructuralPlacement.activationShapes prepare6Chunk = prepare6Shapes := by cbv

def prepare7Shapes : List RegionShapeSummary := [shape4]
theorem prepare7_shapes : observe StructuralPlacement.activationShapes prepare7Chunk = prepare7Shapes := by cbv

def prepare8Shapes : List RegionShapeSummary := [shape4]
theorem prepare8_shapes : observe StructuralPlacement.activationShapes prepare8Chunk = prepare8Shapes := by cbv

def prepare9Shapes : List RegionShapeSummary := [shape4]
theorem prepare9_shapes : observe StructuralPlacement.activationShapes prepare9Chunk = prepare9Shapes := by cbv

def prepare10Shapes : List RegionShapeSummary := [shape4]
theorem prepare10_shapes : observe StructuralPlacement.activationShapes prepare10Chunk = prepare10Shapes := by cbv

def prepare11Shapes : List RegionShapeSummary := [shape4]
theorem prepare11_shapes : observe StructuralPlacement.activationShapes prepare11Chunk = prepare11Shapes := by cbv

def prepare12Shapes : List RegionShapeSummary := [shape4]
theorem prepare12_shapes : observe StructuralPlacement.activationShapes prepare12Chunk = prepare12Shapes := by cbv

def prepare13Shapes : List RegionShapeSummary := [shape4]
theorem prepare13_shapes : observe StructuralPlacement.activationShapes prepare13Chunk = prepare13Shapes := by cbv

def prepare14Shapes : List RegionShapeSummary := [shape4]
theorem prepare14_shapes : observe StructuralPlacement.activationShapes prepare14Chunk = prepare14Shapes := by cbv

def prepare15Shapes : List RegionShapeSummary := [shape4]
theorem prepare15_shapes : observe StructuralPlacement.activationShapes prepare15Chunk = prepare15Shapes := by cbv

def expand16Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand16_shapes : observe StructuralPlacement.activationShapes expand16Chunk = expand16Shapes := by cbv

def expand17Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand17_shapes : observe StructuralPlacement.activationShapes expand17Chunk = expand17Shapes := by cbv

def expand18Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand18_shapes : observe StructuralPlacement.activationShapes expand18Chunk = expand18Shapes := by cbv

def expand19Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand19_shapes : observe StructuralPlacement.activationShapes expand19Chunk = expand19Shapes := by cbv

def expand20Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand20_shapes : observe StructuralPlacement.activationShapes expand20Chunk = expand20Shapes := by cbv

def expand21Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand21_shapes : observe StructuralPlacement.activationShapes expand21Chunk = expand21Shapes := by cbv

def expand22Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand22_shapes : observe StructuralPlacement.activationShapes expand22Chunk = expand22Shapes := by cbv

def expand23Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand23_shapes : observe StructuralPlacement.activationShapes expand23Chunk = expand23Shapes := by cbv

def expand24Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand24_shapes : observe StructuralPlacement.activationShapes expand24Chunk = expand24Shapes := by cbv

def expand25Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand25_shapes : observe StructuralPlacement.activationShapes expand25Chunk = expand25Shapes := by cbv

def expand26Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand26_shapes : observe StructuralPlacement.activationShapes expand26Chunk = expand26Shapes := by cbv

def expand27Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand27_shapes : observe StructuralPlacement.activationShapes expand27Chunk = expand27Shapes := by cbv

def expand28Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand28_shapes : observe StructuralPlacement.activationShapes expand28Chunk = expand28Shapes := by cbv

def expand29Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand29_shapes : observe StructuralPlacement.activationShapes expand29Chunk = expand29Shapes := by cbv

def expand30Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand30_shapes : observe StructuralPlacement.activationShapes expand30Chunk = expand30Shapes := by cbv

def expand31Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand31_shapes : observe StructuralPlacement.activationShapes expand31Chunk = expand31Shapes := by cbv

def expand32Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand32_shapes : observe StructuralPlacement.activationShapes expand32Chunk = expand32Shapes := by cbv

def expand33Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand33_shapes : observe StructuralPlacement.activationShapes expand33Chunk = expand33Shapes := by cbv

def expand34Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand34_shapes : observe StructuralPlacement.activationShapes expand34Chunk = expand34Shapes := by cbv

def expand35Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand35_shapes : observe StructuralPlacement.activationShapes expand35Chunk = expand35Shapes := by cbv

def expand36Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand36_shapes : observe StructuralPlacement.activationShapes expand36Chunk = expand36Shapes := by cbv

def expand37Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand37_shapes : observe StructuralPlacement.activationShapes expand37Chunk = expand37Shapes := by cbv

def expand38Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand38_shapes : observe StructuralPlacement.activationShapes expand38Chunk = expand38Shapes := by cbv

def expand39Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand39_shapes : observe StructuralPlacement.activationShapes expand39Chunk = expand39Shapes := by cbv

def expand40Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand40_shapes : observe StructuralPlacement.activationShapes expand40Chunk = expand40Shapes := by cbv

def expand41Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand41_shapes : observe StructuralPlacement.activationShapes expand41Chunk = expand41Shapes := by cbv

def expand42Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand42_shapes : observe StructuralPlacement.activationShapes expand42Chunk = expand42Shapes := by cbv

def expand43Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand43_shapes : observe StructuralPlacement.activationShapes expand43Chunk = expand43Shapes := by cbv

def expand44Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand44_shapes : observe StructuralPlacement.activationShapes expand44Chunk = expand44Shapes := by cbv

def expand45Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand45_shapes : observe StructuralPlacement.activationShapes expand45Chunk = expand45Shapes := by cbv

def expand46Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand46_shapes : observe StructuralPlacement.activationShapes expand46Chunk = expand46Shapes := by cbv

def expand47Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand47_shapes : observe StructuralPlacement.activationShapes expand47Chunk = expand47Shapes := by cbv

def expand48Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand48_shapes : observe StructuralPlacement.activationShapes expand48Chunk = expand48Shapes := by cbv

def expand49Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand49_shapes : observe StructuralPlacement.activationShapes expand49Chunk = expand49Shapes := by cbv

def expand50Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand50_shapes : observe StructuralPlacement.activationShapes expand50Chunk = expand50Shapes := by cbv

def expand51Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand51_shapes : observe StructuralPlacement.activationShapes expand51Chunk = expand51Shapes := by cbv

def expand52Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand52_shapes : observe StructuralPlacement.activationShapes expand52Chunk = expand52Shapes := by cbv

def expand53Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand53_shapes : observe StructuralPlacement.activationShapes expand53Chunk = expand53Shapes := by cbv

def expand54Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand54_shapes : observe StructuralPlacement.activationShapes expand54Chunk = expand54Shapes := by cbv

def expand55Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand55_shapes : observe StructuralPlacement.activationShapes expand55Chunk = expand55Shapes := by cbv

def expand56Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand56_shapes : observe StructuralPlacement.activationShapes expand56Chunk = expand56Shapes := by cbv

def expand57Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand57_shapes : observe StructuralPlacement.activationShapes expand57Chunk = expand57Shapes := by cbv

def expand58Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand58_shapes : observe StructuralPlacement.activationShapes expand58Chunk = expand58Shapes := by cbv

def expand59Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand59_shapes : observe StructuralPlacement.activationShapes expand59Chunk = expand59Shapes := by cbv

def expand60Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand60_shapes : observe StructuralPlacement.activationShapes expand60Chunk = expand60Shapes := by cbv

def expand61Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand61_shapes : observe StructuralPlacement.activationShapes expand61Chunk = expand61Shapes := by cbv

def expand62Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand62_shapes : observe StructuralPlacement.activationShapes expand62Chunk = expand62Shapes := by cbv

def expand63Shapes : List RegionShapeSummary := [shape5, shape6, shape4]
theorem expand63_shapes : observe StructuralPlacement.activationShapes expand63Chunk = expand63Shapes := by cbv

def round0Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape1, shape10, shape11, shape12]
theorem round0_shapes : observe StructuralPlacement.activationShapes round0Chunk = round0Shapes := by cbv

def round1Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round1_shapes : observe StructuralPlacement.activationShapes round1Chunk = round1Shapes := by cbv

def round2Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round2_shapes : observe StructuralPlacement.activationShapes round2Chunk = round2Shapes := by cbv

def round3Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round3_shapes : observe StructuralPlacement.activationShapes round3Chunk = round3Shapes := by cbv

def round4Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round4_shapes : observe StructuralPlacement.activationShapes round4Chunk = round4Shapes := by cbv

def round5Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round5_shapes : observe StructuralPlacement.activationShapes round5Chunk = round5Shapes := by cbv

def round6Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round6_shapes : observe StructuralPlacement.activationShapes round6Chunk = round6Shapes := by cbv

def round7Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round7_shapes : observe StructuralPlacement.activationShapes round7Chunk = round7Shapes := by cbv

def round8Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round8_shapes : observe StructuralPlacement.activationShapes round8Chunk = round8Shapes := by cbv

def round9Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round9_shapes : observe StructuralPlacement.activationShapes round9Chunk = round9Shapes := by cbv

def round10Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round10_shapes : observe StructuralPlacement.activationShapes round10Chunk = round10Shapes := by cbv

def round11Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round11_shapes : observe StructuralPlacement.activationShapes round11Chunk = round11Shapes := by cbv

def round12Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round12_shapes : observe StructuralPlacement.activationShapes round12Chunk = round12Shapes := by cbv

def round13Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round13_shapes : observe StructuralPlacement.activationShapes round13Chunk = round13Shapes := by cbv

def round14Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round14_shapes : observe StructuralPlacement.activationShapes round14Chunk = round14Shapes := by cbv

def round15Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round15_shapes : observe StructuralPlacement.activationShapes round15Chunk = round15Shapes := by cbv

def round16Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round16_shapes : observe StructuralPlacement.activationShapes round16Chunk = round16Shapes := by cbv

def round17Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round17_shapes : observe StructuralPlacement.activationShapes round17Chunk = round17Shapes := by cbv

def round18Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round18_shapes : observe StructuralPlacement.activationShapes round18Chunk = round18Shapes := by cbv

def round19Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round19_shapes : observe StructuralPlacement.activationShapes round19Chunk = round19Shapes := by cbv

def round20Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round20_shapes : observe StructuralPlacement.activationShapes round20Chunk = round20Shapes := by cbv

def round21Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round21_shapes : observe StructuralPlacement.activationShapes round21Chunk = round21Shapes := by cbv

def round22Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round22_shapes : observe StructuralPlacement.activationShapes round22Chunk = round22Shapes := by cbv

def round23Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round23_shapes : observe StructuralPlacement.activationShapes round23Chunk = round23Shapes := by cbv

def round24Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round24_shapes : observe StructuralPlacement.activationShapes round24Chunk = round24Shapes := by cbv

def round25Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round25_shapes : observe StructuralPlacement.activationShapes round25Chunk = round25Shapes := by cbv

def round26Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round26_shapes : observe StructuralPlacement.activationShapes round26Chunk = round26Shapes := by cbv

def round27Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round27_shapes : observe StructuralPlacement.activationShapes round27Chunk = round27Shapes := by cbv

def round28Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round28_shapes : observe StructuralPlacement.activationShapes round28Chunk = round28Shapes := by cbv

def round29Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round29_shapes : observe StructuralPlacement.activationShapes round29Chunk = round29Shapes := by cbv

def round30Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round30_shapes : observe StructuralPlacement.activationShapes round30Chunk = round30Shapes := by cbv

def round31Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round31_shapes : observe StructuralPlacement.activationShapes round31Chunk = round31Shapes := by cbv

def round32Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round32_shapes : observe StructuralPlacement.activationShapes round32Chunk = round32Shapes := by cbv

def round33Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round33_shapes : observe StructuralPlacement.activationShapes round33Chunk = round33Shapes := by cbv

def round34Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round34_shapes : observe StructuralPlacement.activationShapes round34Chunk = round34Shapes := by cbv

def round35Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round35_shapes : observe StructuralPlacement.activationShapes round35Chunk = round35Shapes := by cbv

def round36Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round36_shapes : observe StructuralPlacement.activationShapes round36Chunk = round36Shapes := by cbv

def round37Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round37_shapes : observe StructuralPlacement.activationShapes round37Chunk = round37Shapes := by cbv

def round38Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round38_shapes : observe StructuralPlacement.activationShapes round38Chunk = round38Shapes := by cbv

def round39Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round39_shapes : observe StructuralPlacement.activationShapes round39Chunk = round39Shapes := by cbv

def round40Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round40_shapes : observe StructuralPlacement.activationShapes round40Chunk = round40Shapes := by cbv

def round41Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round41_shapes : observe StructuralPlacement.activationShapes round41Chunk = round41Shapes := by cbv

def round42Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round42_shapes : observe StructuralPlacement.activationShapes round42Chunk = round42Shapes := by cbv

def round43Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round43_shapes : observe StructuralPlacement.activationShapes round43Chunk = round43Shapes := by cbv

def round44Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round44_shapes : observe StructuralPlacement.activationShapes round44Chunk = round44Shapes := by cbv

def round45Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round45_shapes : observe StructuralPlacement.activationShapes round45Chunk = round45Shapes := by cbv

def round46Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round46_shapes : observe StructuralPlacement.activationShapes round46Chunk = round46Shapes := by cbv

def round47Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round47_shapes : observe StructuralPlacement.activationShapes round47Chunk = round47Shapes := by cbv

def round48Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round48_shapes : observe StructuralPlacement.activationShapes round48Chunk = round48Shapes := by cbv

def round49Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round49_shapes : observe StructuralPlacement.activationShapes round49Chunk = round49Shapes := by cbv

def round50Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round50_shapes : observe StructuralPlacement.activationShapes round50Chunk = round50Shapes := by cbv

def round51Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round51_shapes : observe StructuralPlacement.activationShapes round51Chunk = round51Shapes := by cbv

def round52Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round52_shapes : observe StructuralPlacement.activationShapes round52Chunk = round52Shapes := by cbv

def round53Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round53_shapes : observe StructuralPlacement.activationShapes round53Chunk = round53Shapes := by cbv

def round54Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round54_shapes : observe StructuralPlacement.activationShapes round54Chunk = round54Shapes := by cbv

def round55Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round55_shapes : observe StructuralPlacement.activationShapes round55Chunk = round55Shapes := by cbv

def round56Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round56_shapes : observe StructuralPlacement.activationShapes round56Chunk = round56Shapes := by cbv

def round57Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round57_shapes : observe StructuralPlacement.activationShapes round57Chunk = round57Shapes := by cbv

def round58Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round58_shapes : observe StructuralPlacement.activationShapes round58Chunk = round58Shapes := by cbv

def round59Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round59_shapes : observe StructuralPlacement.activationShapes round59Chunk = round59Shapes := by cbv

def round60Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round60_shapes : observe StructuralPlacement.activationShapes round60Chunk = round60Shapes := by cbv

def round61Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round61_shapes : observe StructuralPlacement.activationShapes round61Chunk = round61Shapes := by cbv

def round62Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round62_shapes : observe StructuralPlacement.activationShapes round62Chunk = round62Shapes := by cbv

def round63Shapes : List RegionShapeSummary := [shape1, shape7, shape8, shape9, shape10, shape11, shape12]
theorem round63_shapes : observe StructuralPlacement.activationShapes round63Chunk = round63Shapes := by cbv

def feedforwardShapes : List RegionShapeSummary := [shape11, shape11, shape11, shape11, shape12, shape12, shape12, shape12]
theorem feedforward_shapes : observe StructuralPlacement.activationShapes feedforwardChunk = feedforwardShapes := by cbv

def serialize0Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize0_shapes : observe StructuralPlacement.activationShapes serialize0Chunk = serialize0Shapes := by cbv

def serialize1Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize1_shapes : observe StructuralPlacement.activationShapes serialize1Chunk = serialize1Shapes := by cbv

def serialize2Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize2_shapes : observe StructuralPlacement.activationShapes serialize2Chunk = serialize2Shapes := by cbv

def serialize3Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize3_shapes : observe StructuralPlacement.activationShapes serialize3Chunk = serialize3Shapes := by cbv

def serialize4Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize4_shapes : observe StructuralPlacement.activationShapes serialize4Chunk = serialize4Shapes := by cbv

def serialize5Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize5_shapes : observe StructuralPlacement.activationShapes serialize5Chunk = serialize5Shapes := by cbv

def serialize6Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize6_shapes : observe StructuralPlacement.activationShapes serialize6Chunk = serialize6Shapes := by cbv

def serialize7Shapes : List RegionShapeSummary := [shape13, shape14]
theorem serialize7_shapes : observe StructuralPlacement.activationShapes serialize7Chunk = serialize7Shapes := by cbv

def publicShapes : List RegionShapeSummary := []
theorem public_shapes : observe StructuralPlacement.activationShapes publicChunk = publicShapes := by cbv

def shapes : List RegionShapeSummary :=
  inputShapes ++ (initialShapes ++ (paddingShapes ++ (packingShapes ++ (prepare0Shapes ++ (prepare1Shapes ++ (prepare2Shapes ++ (prepare3Shapes ++ (prepare4Shapes ++ (prepare5Shapes ++ (prepare6Shapes ++ (prepare7Shapes ++ (prepare8Shapes ++ (prepare9Shapes ++ (prepare10Shapes ++ (prepare11Shapes ++ (prepare12Shapes ++ (prepare13Shapes ++ (prepare14Shapes ++ (prepare15Shapes ++ (expand16Shapes ++ (expand17Shapes ++ (expand18Shapes ++ (expand19Shapes ++ (expand20Shapes ++ (expand21Shapes ++ (expand22Shapes ++ (expand23Shapes ++ (expand24Shapes ++ (expand25Shapes ++ (expand26Shapes ++ (expand27Shapes ++ (expand28Shapes ++ (expand29Shapes ++ (expand30Shapes ++ (expand31Shapes ++ (expand32Shapes ++ (expand33Shapes ++ (expand34Shapes ++ (expand35Shapes ++ (expand36Shapes ++ (expand37Shapes ++ (expand38Shapes ++ (expand39Shapes ++ (expand40Shapes ++ (expand41Shapes ++ (expand42Shapes ++ (expand43Shapes ++ (expand44Shapes ++ (expand45Shapes ++ (expand46Shapes ++ (expand47Shapes ++ (expand48Shapes ++ (expand49Shapes ++ (expand50Shapes ++ (expand51Shapes ++ (expand52Shapes ++ (expand53Shapes ++ (expand54Shapes ++ (expand55Shapes ++ (expand56Shapes ++ (expand57Shapes ++ (expand58Shapes ++ (expand59Shapes ++ (expand60Shapes ++ (expand61Shapes ++ (expand62Shapes ++ (expand63Shapes ++ (round0Shapes ++ (round1Shapes ++ (round2Shapes ++ (round3Shapes ++ (round4Shapes ++ (round5Shapes ++ (round6Shapes ++ (round7Shapes ++ (round8Shapes ++ (round9Shapes ++ (round10Shapes ++ (round11Shapes ++ (round12Shapes ++ (round13Shapes ++ (round14Shapes ++ (round15Shapes ++ (round16Shapes ++ (round17Shapes ++ (round18Shapes ++ (round19Shapes ++ (round20Shapes ++ (round21Shapes ++ (round22Shapes ++ (round23Shapes ++ (round24Shapes ++ (round25Shapes ++ (round26Shapes ++ (round27Shapes ++ (round28Shapes ++ (round29Shapes ++ (round30Shapes ++ (round31Shapes ++ (round32Shapes ++ (round33Shapes ++ (round34Shapes ++ (round35Shapes ++ (round36Shapes ++ (round37Shapes ++ (round38Shapes ++ (round39Shapes ++ (round40Shapes ++ (round41Shapes ++ (round42Shapes ++ (round43Shapes ++ (round44Shapes ++ (round45Shapes ++ (round46Shapes ++ (round47Shapes ++ (round48Shapes ++ (round49Shapes ++ (round50Shapes ++ (round51Shapes ++ (round52Shapes ++ (round53Shapes ++ (round54Shapes ++ (round55Shapes ++ (round56Shapes ++ (round57Shapes ++ (round58Shapes ++ (round59Shapes ++ (round60Shapes ++ (round61Shapes ++ (round62Shapes ++ (round63Shapes ++ (feedforwardShapes ++ (serialize0Shapes ++ (serialize1Shapes ++ (serialize2Shapes ++ (serialize3Shapes ++ (serialize4Shapes ++ (serialize5Shapes ++ (serialize6Shapes ++ (serialize7Shapes ++ (publicShapes ++ ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem shapes_eq : StructuralPlacement.shapes = shapes := by
  unfold StructuralPlacement.shapes
  simp only [StructuralComposition.fullChunk, StructuralComposition.scheduleChunk,
    StructuralComposition.prepareChunk, StructuralComposition.expandChunk,
    StructuralComposition.roundsChunk, StructuralComposition.serializeChunk, observe_append,
    input_shapes, initial_shapes, padding_shapes, packing_shapes, prepare0_shapes, prepare1_shapes, prepare2_shapes, prepare3_shapes, prepare4_shapes, prepare5_shapes, prepare6_shapes, prepare7_shapes, prepare8_shapes, prepare9_shapes, prepare10_shapes, prepare11_shapes, prepare12_shapes, prepare13_shapes, prepare14_shapes, prepare15_shapes, expand16_shapes, expand17_shapes, expand18_shapes, expand19_shapes, expand20_shapes, expand21_shapes, expand22_shapes, expand23_shapes, expand24_shapes, expand25_shapes, expand26_shapes, expand27_shapes, expand28_shapes, expand29_shapes, expand30_shapes, expand31_shapes, expand32_shapes, expand33_shapes, expand34_shapes, expand35_shapes, expand36_shapes, expand37_shapes, expand38_shapes, expand39_shapes, expand40_shapes, expand41_shapes, expand42_shapes, expand43_shapes, expand44_shapes, expand45_shapes, expand46_shapes, expand47_shapes, expand48_shapes, expand49_shapes, expand50_shapes, expand51_shapes, expand52_shapes, expand53_shapes, expand54_shapes, expand55_shapes, expand56_shapes, expand57_shapes, expand58_shapes, expand59_shapes, expand60_shapes, expand61_shapes, expand62_shapes, expand63_shapes, round0_shapes, round1_shapes, round2_shapes, round3_shapes, round4_shapes, round5_shapes, round6_shapes, round7_shapes, round8_shapes, round9_shapes, round10_shapes, round11_shapes, round12_shapes, round13_shapes, round14_shapes, round15_shapes, round16_shapes, round17_shapes, round18_shapes, round19_shapes, round20_shapes, round21_shapes, round22_shapes, round23_shapes, round24_shapes, round25_shapes, round26_shapes, round27_shapes, round28_shapes, round29_shapes, round30_shapes, round31_shapes, round32_shapes, round33_shapes, round34_shapes, round35_shapes, round36_shapes, round37_shapes, round38_shapes, round39_shapes, round40_shapes, round41_shapes, round42_shapes, round43_shapes, round44_shapes, round45_shapes, round46_shapes, round47_shapes, round48_shapes, round49_shapes, round50_shapes, round51_shapes, round52_shapes, round53_shapes, round54_shapes, round55_shapes, round56_shapes, round57_shapes, round58_shapes, round59_shapes, round60_shapes, round61_shapes, round62_shapes, round63_shapes, feedforward_shapes, serialize0_shapes, serialize1_shapes, serialize2_shapes, serialize3_shapes, serialize4_shapes, serialize5_shapes, serialize6_shapes, serialize7_shapes, public_shapes, shapes, List.append_assoc, List.append_nil]

end Midnight.SHA256.Semantics.StructuralPlacementShapes
