import Midnight.SHA256.Semantics.StructuralCheckpoints
import Midnight.SHA256.Semantics.StructuralProgram

namespace Midnight.SHA256.Semantics.StructuralComposition
open Halo2 Chips.SynthesisCheckpoint StructuralCheckpoints Midnight.Math.Checkpoint
set_option Elab.async false

attribute [local irreducible] Synthesis.prepareMessage Synthesis.sigma0 Synthesis.sigma1

def prepareChunk : List Step := prepare0Chunk ++ (prepare1Chunk ++ (prepare2Chunk ++ (prepare3Chunk ++ (prepare4Chunk ++ (prepare5Chunk ++ (prepare6Chunk ++ (prepare7Chunk ++ (prepare8Chunk ++ (prepare9Chunk ++ (prepare10Chunk ++ (prepare11Chunk ++ (prepare12Chunk ++ (prepare13Chunk ++ (prepare14Chunk ++ (prepare15Chunk ++ ([]))))))))))))))))

theorem prepareChain : Chain frame shape (StructuralProgram.prepareStep packingOutput) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] packingAfter (#[]) prepare15After prepare15Output prepareChunk := by
  exact Chain.cons prepare0Checked (Chain.cons prepare1Checked (Chain.cons prepare2Checked (Chain.cons prepare3Checked (Chain.cons prepare4Checked (Chain.cons prepare5Checked (Chain.cons prepare6Checked (Chain.cons prepare7Checked (Chain.cons prepare8Checked (Chain.cons prepare9Checked (Chain.cons prepare10Checked (Chain.cons prepare11Checked (Chain.cons prepare12Checked (Chain.cons prepare13Checked (Chain.cons prepare14Checked (Chain.cons prepare15Checked (Chain.nil _ _))))))))))))))))

theorem prepareChecked : Checkpoint (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat).foldlM (fun value index => (StructuralProgram.prepareStep packingOutput) index value) (#[])) packingAfter prepare15Output prepare15After prepareChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ prepareChain

def expandChunk : List Step := expand16Chunk ++ (expand17Chunk ++ (expand18Chunk ++ (expand19Chunk ++ (expand20Chunk ++ (expand21Chunk ++ (expand22Chunk ++ (expand23Chunk ++ (expand24Chunk ++ (expand25Chunk ++ (expand26Chunk ++ (expand27Chunk ++ (expand28Chunk ++ (expand29Chunk ++ (expand30Chunk ++ (expand31Chunk ++ (expand32Chunk ++ (expand33Chunk ++ (expand34Chunk ++ (expand35Chunk ++ (expand36Chunk ++ (expand37Chunk ++ (expand38Chunk ++ (expand39Chunk ++ (expand40Chunk ++ (expand41Chunk ++ (expand42Chunk ++ (expand43Chunk ++ (expand44Chunk ++ (expand45Chunk ++ (expand46Chunk ++ (expand47Chunk ++ (expand48Chunk ++ (expand49Chunk ++ (expand50Chunk ++ (expand51Chunk ++ (expand52Chunk ++ (expand53Chunk ++ (expand54Chunk ++ (expand55Chunk ++ (expand56Chunk ++ (expand57Chunk ++ (expand58Chunk ++ (expand59Chunk ++ (expand60Chunk ++ (expand61Chunk ++ (expand62Chunk ++ (expand63Chunk ++ ([]))))))))))))))))))))))))))))))))))))))))))))))))

theorem expandChain : Chain frame shape (StructuralProgram.expandStep) [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] prepare15After (prepare15Output) expand63After expand63Output expandChunk := by
  exact Chain.cons expand16Checked (Chain.cons expand17Checked (Chain.cons expand18Checked (Chain.cons expand19Checked (Chain.cons expand20Checked (Chain.cons expand21Checked (Chain.cons expand22Checked (Chain.cons expand23Checked (Chain.cons expand24Checked (Chain.cons expand25Checked (Chain.cons expand26Checked (Chain.cons expand27Checked (Chain.cons expand28Checked (Chain.cons expand29Checked (Chain.cons expand30Checked (Chain.cons expand31Checked (Chain.cons expand32Checked (Chain.cons expand33Checked (Chain.cons expand34Checked (Chain.cons expand35Checked (Chain.cons expand36Checked (Chain.cons expand37Checked (Chain.cons expand38Checked (Chain.cons expand39Checked (Chain.cons expand40Checked (Chain.cons expand41Checked (Chain.cons expand42Checked (Chain.cons expand43Checked (Chain.cons expand44Checked (Chain.cons expand45Checked (Chain.cons expand46Checked (Chain.cons expand47Checked (Chain.cons expand48Checked (Chain.cons expand49Checked (Chain.cons expand50Checked (Chain.cons expand51Checked (Chain.cons expand52Checked (Chain.cons expand53Checked (Chain.cons expand54Checked (Chain.cons expand55Checked (Chain.cons expand56Checked (Chain.cons expand57Checked (Chain.cons expand58Checked (Chain.cons expand59Checked (Chain.cons expand60Checked (Chain.cons expand61Checked (Chain.cons expand62Checked (Chain.cons expand63Checked (Chain.nil _ _))))))))))))))))))))))))))))))))))))))))))))))))

theorem expandChecked : Checkpoint (([16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] : List Nat).foldlM (fun value index => (StructuralProgram.expandStep) index value) (prepare15Output)) prepare15After expand63Output expand63After expandChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ expandChain

def scheduleChunk : List Step := prepareChunk ++ (expandChunk ++ [])
theorem scheduleChecked : Checkpoint (StructuralProgram.schedule packingOutput) packingAfter scheduleOutput expand63After scheduleChunk := by
  unfold StructuralProgram.schedule
  exact Checked.bind _ _ _ _ _ _ _ _ _ _ _ prepareChecked
    (Checked.bind _ _ _ _ _ _ _ _ _ _ _ expandChecked (Checked.pure _ _ _ _))

attribute [local irreducible] Synthesis.compressionRound Synthesis.wordToBytes Synthesis.addStates

def roundsChunk : List Step := round0Chunk ++ (round1Chunk ++ (round2Chunk ++ (round3Chunk ++ (round4Chunk ++ (round5Chunk ++ (round6Chunk ++ (round7Chunk ++ (round8Chunk ++ (round9Chunk ++ (round10Chunk ++ (round11Chunk ++ (round12Chunk ++ (round13Chunk ++ (round14Chunk ++ (round15Chunk ++ (round16Chunk ++ (round17Chunk ++ (round18Chunk ++ (round19Chunk ++ (round20Chunk ++ (round21Chunk ++ (round22Chunk ++ (round23Chunk ++ (round24Chunk ++ (round25Chunk ++ (round26Chunk ++ (round27Chunk ++ (round28Chunk ++ (round29Chunk ++ (round30Chunk ++ (round31Chunk ++ (round32Chunk ++ (round33Chunk ++ (round34Chunk ++ (round35Chunk ++ (round36Chunk ++ (round37Chunk ++ (round38Chunk ++ (round39Chunk ++ (round40Chunk ++ (round41Chunk ++ (round42Chunk ++ (round43Chunk ++ (round44Chunk ++ (round45Chunk ++ (round46Chunk ++ (round47Chunk ++ (round48Chunk ++ (round49Chunk ++ (round50Chunk ++ (round51Chunk ++ (round52Chunk ++ (round53Chunk ++ (round54Chunk ++ (round55Chunk ++ (round56Chunk ++ (round57Chunk ++ (round58Chunk ++ (round59Chunk ++ (round60Chunk ++ (round61Chunk ++ (round62Chunk ++ (round63Chunk ++ ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem roundsChain : Chain frame shape (StructuralProgram.roundStep scheduleOutput) (List.range 64) expand63After (initialOutput) round63After round63Output roundsChunk := by
  exact Chain.cons round0Checked (Chain.cons round1Checked (Chain.cons round2Checked (Chain.cons round3Checked (Chain.cons round4Checked (Chain.cons round5Checked (Chain.cons round6Checked (Chain.cons round7Checked (Chain.cons round8Checked (Chain.cons round9Checked (Chain.cons round10Checked (Chain.cons round11Checked (Chain.cons round12Checked (Chain.cons round13Checked (Chain.cons round14Checked (Chain.cons round15Checked (Chain.cons round16Checked (Chain.cons round17Checked (Chain.cons round18Checked (Chain.cons round19Checked (Chain.cons round20Checked (Chain.cons round21Checked (Chain.cons round22Checked (Chain.cons round23Checked (Chain.cons round24Checked (Chain.cons round25Checked (Chain.cons round26Checked (Chain.cons round27Checked (Chain.cons round28Checked (Chain.cons round29Checked (Chain.cons round30Checked (Chain.cons round31Checked (Chain.cons round32Checked (Chain.cons round33Checked (Chain.cons round34Checked (Chain.cons round35Checked (Chain.cons round36Checked (Chain.cons round37Checked (Chain.cons round38Checked (Chain.cons round39Checked (Chain.cons round40Checked (Chain.cons round41Checked (Chain.cons round42Checked (Chain.cons round43Checked (Chain.cons round44Checked (Chain.cons round45Checked (Chain.cons round46Checked (Chain.cons round47Checked (Chain.cons round48Checked (Chain.cons round49Checked (Chain.cons round50Checked (Chain.cons round51Checked (Chain.cons round52Checked (Chain.cons round53Checked (Chain.cons round54Checked (Chain.cons round55Checked (Chain.cons round56Checked (Chain.cons round57Checked (Chain.cons round58Checked (Chain.cons round59Checked (Chain.cons round60Checked (Chain.cons round61Checked (Chain.cons round62Checked (Chain.cons round63Checked (Chain.nil _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem roundsChecked : Checkpoint ((List.range 64).foldlM (fun value item => (StructuralProgram.roundStep scheduleOutput) item value) (initialOutput)) expand63After round63Output round63After roundsChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ roundsChain

def serializeChunk : List Step := serialize0Chunk ++ (serialize1Chunk ++ (serialize2Chunk ++ (serialize3Chunk ++ (serialize4Chunk ++ (serialize5Chunk ++ (serialize6Chunk ++ (serialize7Chunk ++ ([]))))))))
theorem serializeChain : Chain frame shape (StructuralProgram.serializeStep) (feedforwardOutput.toList) feedforwardAfter (#[]) serialize7After serialize7Output serializeChunk := by
  exact Chain.cons serialize0Checked (Chain.cons serialize1Checked (Chain.cons serialize2Checked (Chain.cons serialize3Checked (Chain.cons serialize4Checked (Chain.cons serialize5Checked (Chain.cons serialize6Checked (Chain.cons serialize7Checked (Chain.nil _ _))))))))
theorem serializeChecked : Checkpoint ((feedforwardOutput.toList).foldlM (fun value item => (StructuralProgram.serializeStep) item value) (#[])) feedforwardAfter serialize7Output serialize7After serializeChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ serializeChain

def fullChunk : List Step := inputChunk ++ (initialChunk ++ (paddingChunk ++ (packingChunk ++ (scheduleChunk ++ (roundsChunk ++ (feedforwardChunk ++ (serializeChunk ++ (publicChunk ++ ([])))))))))
theorem sourceChecked : Checkpoint Synthesis.synthesize beginCursor () publicAfter fullChunk := by
  rw [StructuralProgram.source_eq]
  unfold StructuralProgram.program
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ inputChecked ?_
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ initialChecked ?_
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ paddingChecked ?_
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ packingChecked ?_
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ scheduleChecked ?_
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ roundsChecked ?_
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ feedforwardChecked ?_
  refine Checked.bind _ _ _ _ _ _ _ _ _ _ _ serializeChecked ?_
  simpa only [List.append_nil, publicAction, publicOutput, StructuralProgram.expose] using publicChecked

attribute [local irreducible] Synthesis.synthesize

theorem sourceShape : shape Synthesis.schedule = fullChunk :=
  Checkpoint.observed Synthesis.synthesize 0 [] () publicAfter fullChunk sourceChecked

end Midnight.SHA256.Semantics.StructuralComposition
