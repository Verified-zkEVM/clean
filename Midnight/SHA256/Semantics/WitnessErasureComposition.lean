import Midnight.SHA256.Semantics.WitnessErasureCheckpoints
import Midnight.SHA256.Semantics.WitnessCheckpointComposition
import Midnight.SHA256.Semantics.StructuralProgram

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2 Chips.SynthesisCheckpoint StructuralCheckpoints Midnight.Math.Checkpoint
set_option Elab.async false
attribute [local irreducible] Midnight.Math.Checkpoint.Checked observe
attribute [local irreducible] WitnessCheckpoints.inputOperations WitnessCheckpoints.initialOperations WitnessCheckpoints.paddingOperations WitnessCheckpoints.packingOperations WitnessCheckpoints.prepare0Operations WitnessCheckpoints.prepare1Operations WitnessCheckpoints.prepare2Operations WitnessCheckpoints.prepare3Operations WitnessCheckpoints.prepare4Operations WitnessCheckpoints.prepare5Operations WitnessCheckpoints.prepare6Operations WitnessCheckpoints.prepare7Operations WitnessCheckpoints.prepare8Operations WitnessCheckpoints.prepare9Operations WitnessCheckpoints.prepare10Operations WitnessCheckpoints.prepare11Operations WitnessCheckpoints.prepare12Operations WitnessCheckpoints.prepare13Operations WitnessCheckpoints.prepare14Operations WitnessCheckpoints.prepare15Operations WitnessCheckpoints.expand16Operations WitnessCheckpoints.expand17Operations WitnessCheckpoints.expand18Operations WitnessCheckpoints.expand19Operations WitnessCheckpoints.expand20Operations WitnessCheckpoints.expand21Operations WitnessCheckpoints.expand22Operations WitnessCheckpoints.expand23Operations WitnessCheckpoints.expand24Operations WitnessCheckpoints.expand25Operations WitnessCheckpoints.expand26Operations WitnessCheckpoints.expand27Operations WitnessCheckpoints.expand28Operations WitnessCheckpoints.expand29Operations WitnessCheckpoints.expand30Operations WitnessCheckpoints.expand31Operations WitnessCheckpoints.expand32Operations WitnessCheckpoints.expand33Operations WitnessCheckpoints.expand34Operations WitnessCheckpoints.expand35Operations WitnessCheckpoints.expand36Operations WitnessCheckpoints.expand37Operations WitnessCheckpoints.expand38Operations WitnessCheckpoints.expand39Operations WitnessCheckpoints.expand40Operations WitnessCheckpoints.expand41Operations WitnessCheckpoints.expand42Operations WitnessCheckpoints.expand43Operations WitnessCheckpoints.expand44Operations WitnessCheckpoints.expand45Operations WitnessCheckpoints.expand46Operations WitnessCheckpoints.expand47Operations WitnessCheckpoints.expand48Operations WitnessCheckpoints.expand49Operations WitnessCheckpoints.expand50Operations WitnessCheckpoints.expand51Operations WitnessCheckpoints.expand52Operations WitnessCheckpoints.expand53Operations WitnessCheckpoints.expand54Operations WitnessCheckpoints.expand55Operations WitnessCheckpoints.expand56Operations WitnessCheckpoints.expand57Operations WitnessCheckpoints.expand58Operations WitnessCheckpoints.expand59Operations WitnessCheckpoints.expand60Operations WitnessCheckpoints.expand61Operations WitnessCheckpoints.expand62Operations WitnessCheckpoints.expand63Operations WitnessCheckpoints.round0Operations WitnessCheckpoints.round1Operations WitnessCheckpoints.round2Operations WitnessCheckpoints.round3Operations WitnessCheckpoints.round4Operations WitnessCheckpoints.round5Operations WitnessCheckpoints.round6Operations WitnessCheckpoints.round7Operations WitnessCheckpoints.round8Operations WitnessCheckpoints.round9Operations WitnessCheckpoints.round10Operations WitnessCheckpoints.round11Operations WitnessCheckpoints.round12Operations WitnessCheckpoints.round13Operations WitnessCheckpoints.round14Operations WitnessCheckpoints.round15Operations WitnessCheckpoints.round16Operations WitnessCheckpoints.round17Operations WitnessCheckpoints.round18Operations WitnessCheckpoints.round19Operations WitnessCheckpoints.round20Operations WitnessCheckpoints.round21Operations WitnessCheckpoints.round22Operations WitnessCheckpoints.round23Operations WitnessCheckpoints.round24Operations WitnessCheckpoints.round25Operations WitnessCheckpoints.round26Operations WitnessCheckpoints.round27Operations WitnessCheckpoints.round28Operations WitnessCheckpoints.round29Operations WitnessCheckpoints.round30Operations WitnessCheckpoints.round31Operations WitnessCheckpoints.round32Operations WitnessCheckpoints.round33Operations WitnessCheckpoints.round34Operations WitnessCheckpoints.round35Operations WitnessCheckpoints.round36Operations WitnessCheckpoints.round37Operations WitnessCheckpoints.round38Operations WitnessCheckpoints.round39Operations WitnessCheckpoints.round40Operations WitnessCheckpoints.round41Operations WitnessCheckpoints.round42Operations WitnessCheckpoints.round43Operations WitnessCheckpoints.round44Operations WitnessCheckpoints.round45Operations WitnessCheckpoints.round46Operations WitnessCheckpoints.round47Operations WitnessCheckpoints.round48Operations WitnessCheckpoints.round49Operations WitnessCheckpoints.round50Operations WitnessCheckpoints.round51Operations WitnessCheckpoints.round52Operations WitnessCheckpoints.round53Operations WitnessCheckpoints.round54Operations WitnessCheckpoints.round55Operations WitnessCheckpoints.round56Operations WitnessCheckpoints.round57Operations WitnessCheckpoints.round58Operations WitnessCheckpoints.round59Operations WitnessCheckpoints.round60Operations WitnessCheckpoints.round61Operations WitnessCheckpoints.round62Operations WitnessCheckpoints.round63Operations WitnessCheckpoints.feedforwardOperations WitnessCheckpoints.serialize0Operations WitnessCheckpoints.serialize1Operations WitnessCheckpoints.serialize2Operations WitnessCheckpoints.serialize3Operations WitnessCheckpoints.serialize4Operations WitnessCheckpoints.serialize5Operations WitnessCheckpoints.serialize6Operations WitnessCheckpoints.serialize7Operations WitnessCheckpoints.publicOperations
local notation "inputChunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.inputOperations 0))
local notation "initialChunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.initialOperations 0))
local notation "paddingChunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.paddingOperations 0))
local notation "packingChunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.packingOperations 0))
local notation "prepare0Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare0Operations 0))
local notation "prepare1Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare1Operations 0))
local notation "prepare2Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare2Operations 0))
local notation "prepare3Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare3Operations 0))
local notation "prepare4Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare4Operations 0))
local notation "prepare5Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare5Operations 0))
local notation "prepare6Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare6Operations 0))
local notation "prepare7Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare7Operations 0))
local notation "prepare8Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare8Operations 0))
local notation "prepare9Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare9Operations 0))
local notation "prepare10Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare10Operations 0))
local notation "prepare11Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare11Operations 0))
local notation "prepare12Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare12Operations 0))
local notation "prepare13Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare13Operations 0))
local notation "prepare14Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare14Operations 0))
local notation "prepare15Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.prepare15Operations 0))
local notation "expand16Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand16Operations 0))
local notation "expand17Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand17Operations 0))
local notation "expand18Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand18Operations 0))
local notation "expand19Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand19Operations 0))
local notation "expand20Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand20Operations 0))
local notation "expand21Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand21Operations 0))
local notation "expand22Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand22Operations 0))
local notation "expand23Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand23Operations 0))
local notation "expand24Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand24Operations 0))
local notation "expand25Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand25Operations 0))
local notation "expand26Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand26Operations 0))
local notation "expand27Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand27Operations 0))
local notation "expand28Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand28Operations 0))
local notation "expand29Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand29Operations 0))
local notation "expand30Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand30Operations 0))
local notation "expand31Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand31Operations 0))
local notation "expand32Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand32Operations 0))
local notation "expand33Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand33Operations 0))
local notation "expand34Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand34Operations 0))
local notation "expand35Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand35Operations 0))
local notation "expand36Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand36Operations 0))
local notation "expand37Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand37Operations 0))
local notation "expand38Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand38Operations 0))
local notation "expand39Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand39Operations 0))
local notation "expand40Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand40Operations 0))
local notation "expand41Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand41Operations 0))
local notation "expand42Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand42Operations 0))
local notation "expand43Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand43Operations 0))
local notation "expand44Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand44Operations 0))
local notation "expand45Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand45Operations 0))
local notation "expand46Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand46Operations 0))
local notation "expand47Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand47Operations 0))
local notation "expand48Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand48Operations 0))
local notation "expand49Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand49Operations 0))
local notation "expand50Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand50Operations 0))
local notation "expand51Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand51Operations 0))
local notation "expand52Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand52Operations 0))
local notation "expand53Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand53Operations 0))
local notation "expand54Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand54Operations 0))
local notation "expand55Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand55Operations 0))
local notation "expand56Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand56Operations 0))
local notation "expand57Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand57Operations 0))
local notation "expand58Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand58Operations 0))
local notation "expand59Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand59Operations 0))
local notation "expand60Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand60Operations 0))
local notation "expand61Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand61Operations 0))
local notation "expand62Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand62Operations 0))
local notation "expand63Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.expand63Operations 0))
local notation "round0Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round0Operations 0))
local notation "round1Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round1Operations 0))
local notation "round2Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round2Operations 0))
local notation "round3Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round3Operations 0))
local notation "round4Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round4Operations 0))
local notation "round5Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round5Operations 0))
local notation "round6Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round6Operations 0))
local notation "round7Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round7Operations 0))
local notation "round8Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round8Operations 0))
local notation "round9Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round9Operations 0))
local notation "round10Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round10Operations 0))
local notation "round11Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round11Operations 0))
local notation "round12Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round12Operations 0))
local notation "round13Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round13Operations 0))
local notation "round14Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round14Operations 0))
local notation "round15Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round15Operations 0))
local notation "round16Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round16Operations 0))
local notation "round17Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round17Operations 0))
local notation "round18Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round18Operations 0))
local notation "round19Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round19Operations 0))
local notation "round20Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round20Operations 0))
local notation "round21Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round21Operations 0))
local notation "round22Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round22Operations 0))
local notation "round23Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round23Operations 0))
local notation "round24Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round24Operations 0))
local notation "round25Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round25Operations 0))
local notation "round26Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round26Operations 0))
local notation "round27Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round27Operations 0))
local notation "round28Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round28Operations 0))
local notation "round29Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round29Operations 0))
local notation "round30Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round30Operations 0))
local notation "round31Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round31Operations 0))
local notation "round32Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round32Operations 0))
local notation "round33Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round33Operations 0))
local notation "round34Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round34Operations 0))
local notation "round35Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round35Operations 0))
local notation "round36Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round36Operations 0))
local notation "round37Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round37Operations 0))
local notation "round38Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round38Operations 0))
local notation "round39Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round39Operations 0))
local notation "round40Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round40Operations 0))
local notation "round41Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round41Operations 0))
local notation "round42Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round42Operations 0))
local notation "round43Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round43Operations 0))
local notation "round44Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round44Operations 0))
local notation "round45Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round45Operations 0))
local notation "round46Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round46Operations 0))
local notation "round47Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round47Operations 0))
local notation "round48Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round48Operations 0))
local notation "round49Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round49Operations 0))
local notation "round50Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round50Operations 0))
local notation "round51Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round51Operations 0))
local notation "round52Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round52Operations 0))
local notation "round53Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round53Operations 0))
local notation "round54Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round54Operations 0))
local notation "round55Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round55Operations 0))
local notation "round56Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round56Operations 0))
local notation "round57Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round57Operations 0))
local notation "round58Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round58Operations 0))
local notation "round59Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round59Operations 0))
local notation "round60Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round60Operations 0))
local notation "round61Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round61Operations 0))
local notation "round62Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round62Operations 0))
local notation "round63Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.round63Operations 0))
local notation "feedforwardChunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.feedforwardOperations 0))
local notation "serialize0Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize0Operations 0))
local notation "serialize1Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize1Operations 0))
local notation "serialize2Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize2Operations 0))
local notation "serialize3Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize3Operations 0))
local notation "serialize4Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize4Operations 0))
local notation "serialize5Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize5Operations 0))
local notation "serialize6Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize6Operations 0))
local notation "serialize7Chunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.serialize7Operations 0))
local notation "publicChunk" => (List.map WitnessErasure.Code.encode (WitnessCheckpoints.publicOperations 0))

attribute [local irreducible] Synthesis.prepareMessage Synthesis.sigma0 Synthesis.sigma1

noncomputable def prepareChunk : List WitnessErasure.Code.Top := prepare0Chunk ++ (prepare1Chunk ++ (prepare2Chunk ++ (prepare3Chunk ++ (prepare4Chunk ++ (prepare5Chunk ++ (prepare6Chunk ++ (prepare7Chunk ++ (prepare8Chunk ++ (prepare9Chunk ++ (prepare10Chunk ++ (prepare11Chunk ++ (prepare12Chunk ++ (prepare13Chunk ++ (prepare14Chunk ++ (prepare15Chunk ++ ([]))))))))))))))))

theorem prepareChain : Chain frame observe (StructuralProgram.prepareStep packingOutput) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] packingAfter (#[]) prepare15After prepare15Output prepareChunk := by
  exact Chain.cons prepare0Checked (Chain.cons prepare1Checked (Chain.cons prepare2Checked (Chain.cons prepare3Checked (Chain.cons prepare4Checked (Chain.cons prepare5Checked (Chain.cons prepare6Checked (Chain.cons prepare7Checked (Chain.cons prepare8Checked (Chain.cons prepare9Checked (Chain.cons prepare10Checked (Chain.cons prepare11Checked (Chain.cons prepare12Checked (Chain.cons prepare13Checked (Chain.cons prepare14Checked (Chain.cons prepare15Checked (Chain.nil _ _))))))))))))))))

theorem prepareChecked : Checked (([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List Nat).foldlM (fun value index => (StructuralProgram.prepareStep packingOutput) index value) (#[])) packingAfter prepare15Output prepare15After prepareChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ prepareChain

noncomputable def expandChunk : List WitnessErasure.Code.Top := expand16Chunk ++ (expand17Chunk ++ (expand18Chunk ++ (expand19Chunk ++ (expand20Chunk ++ (expand21Chunk ++ (expand22Chunk ++ (expand23Chunk ++ (expand24Chunk ++ (expand25Chunk ++ (expand26Chunk ++ (expand27Chunk ++ (expand28Chunk ++ (expand29Chunk ++ (expand30Chunk ++ (expand31Chunk ++ (expand32Chunk ++ (expand33Chunk ++ (expand34Chunk ++ (expand35Chunk ++ (expand36Chunk ++ (expand37Chunk ++ (expand38Chunk ++ (expand39Chunk ++ (expand40Chunk ++ (expand41Chunk ++ (expand42Chunk ++ (expand43Chunk ++ (expand44Chunk ++ (expand45Chunk ++ (expand46Chunk ++ (expand47Chunk ++ (expand48Chunk ++ (expand49Chunk ++ (expand50Chunk ++ (expand51Chunk ++ (expand52Chunk ++ (expand53Chunk ++ (expand54Chunk ++ (expand55Chunk ++ (expand56Chunk ++ (expand57Chunk ++ (expand58Chunk ++ (expand59Chunk ++ (expand60Chunk ++ (expand61Chunk ++ (expand62Chunk ++ (expand63Chunk ++ ([]))))))))))))))))))))))))))))))))))))))))))))))))

theorem expandChain : Chain frame observe (StructuralProgram.expandStep) [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] prepare15After (prepare15Output) expand63After expand63Output expandChunk := by
  exact Chain.cons expand16Checked (Chain.cons expand17Checked (Chain.cons expand18Checked (Chain.cons expand19Checked (Chain.cons expand20Checked (Chain.cons expand21Checked (Chain.cons expand22Checked (Chain.cons expand23Checked (Chain.cons expand24Checked (Chain.cons expand25Checked (Chain.cons expand26Checked (Chain.cons expand27Checked (Chain.cons expand28Checked (Chain.cons expand29Checked (Chain.cons expand30Checked (Chain.cons expand31Checked (Chain.cons expand32Checked (Chain.cons expand33Checked (Chain.cons expand34Checked (Chain.cons expand35Checked (Chain.cons expand36Checked (Chain.cons expand37Checked (Chain.cons expand38Checked (Chain.cons expand39Checked (Chain.cons expand40Checked (Chain.cons expand41Checked (Chain.cons expand42Checked (Chain.cons expand43Checked (Chain.cons expand44Checked (Chain.cons expand45Checked (Chain.cons expand46Checked (Chain.cons expand47Checked (Chain.cons expand48Checked (Chain.cons expand49Checked (Chain.cons expand50Checked (Chain.cons expand51Checked (Chain.cons expand52Checked (Chain.cons expand53Checked (Chain.cons expand54Checked (Chain.cons expand55Checked (Chain.cons expand56Checked (Chain.cons expand57Checked (Chain.cons expand58Checked (Chain.cons expand59Checked (Chain.cons expand60Checked (Chain.cons expand61Checked (Chain.cons expand62Checked (Chain.cons expand63Checked (Chain.nil _ _))))))))))))))))))))))))))))))))))))))))))))))))

theorem expandChecked : Checked (([16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] : List Nat).foldlM (fun value index => (StructuralProgram.expandStep) index value) (prepare15Output)) prepare15After expand63Output expand63After expandChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ expandChain

noncomputable def scheduleChunk : List WitnessErasure.Code.Top := prepareChunk ++ (expandChunk ++ [])
theorem scheduleChecked : Checked (StructuralProgram.schedule packingOutput) packingAfter scheduleOutput expand63After scheduleChunk := by
  unfold StructuralProgram.schedule
  exact Checked.bind _ _ _ _ _ _ _ _ _ _ _ prepareChecked
    (Checked.bind _ _ _ _ _ _ _ _ _ _ _ expandChecked (Checked.pure _ _ _ _))

attribute [local irreducible] Synthesis.compressionRound Synthesis.wordToBytes Synthesis.addStates

noncomputable def roundsChunk : List WitnessErasure.Code.Top := round0Chunk ++ (round1Chunk ++ (round2Chunk ++ (round3Chunk ++ (round4Chunk ++ (round5Chunk ++ (round6Chunk ++ (round7Chunk ++ (round8Chunk ++ (round9Chunk ++ (round10Chunk ++ (round11Chunk ++ (round12Chunk ++ (round13Chunk ++ (round14Chunk ++ (round15Chunk ++ (round16Chunk ++ (round17Chunk ++ (round18Chunk ++ (round19Chunk ++ (round20Chunk ++ (round21Chunk ++ (round22Chunk ++ (round23Chunk ++ (round24Chunk ++ (round25Chunk ++ (round26Chunk ++ (round27Chunk ++ (round28Chunk ++ (round29Chunk ++ (round30Chunk ++ (round31Chunk ++ (round32Chunk ++ (round33Chunk ++ (round34Chunk ++ (round35Chunk ++ (round36Chunk ++ (round37Chunk ++ (round38Chunk ++ (round39Chunk ++ (round40Chunk ++ (round41Chunk ++ (round42Chunk ++ (round43Chunk ++ (round44Chunk ++ (round45Chunk ++ (round46Chunk ++ (round47Chunk ++ (round48Chunk ++ (round49Chunk ++ (round50Chunk ++ (round51Chunk ++ (round52Chunk ++ (round53Chunk ++ (round54Chunk ++ (round55Chunk ++ (round56Chunk ++ (round57Chunk ++ (round58Chunk ++ (round59Chunk ++ (round60Chunk ++ (round61Chunk ++ (round62Chunk ++ (round63Chunk ++ ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem roundsChain : Chain frame observe (StructuralProgram.roundStep scheduleOutput) (List.range 64) expand63After (initialOutput) round63After round63Output roundsChunk := by
  exact Chain.cons round0Checked (Chain.cons round1Checked (Chain.cons round2Checked (Chain.cons round3Checked (Chain.cons round4Checked (Chain.cons round5Checked (Chain.cons round6Checked (Chain.cons round7Checked (Chain.cons round8Checked (Chain.cons round9Checked (Chain.cons round10Checked (Chain.cons round11Checked (Chain.cons round12Checked (Chain.cons round13Checked (Chain.cons round14Checked (Chain.cons round15Checked (Chain.cons round16Checked (Chain.cons round17Checked (Chain.cons round18Checked (Chain.cons round19Checked (Chain.cons round20Checked (Chain.cons round21Checked (Chain.cons round22Checked (Chain.cons round23Checked (Chain.cons round24Checked (Chain.cons round25Checked (Chain.cons round26Checked (Chain.cons round27Checked (Chain.cons round28Checked (Chain.cons round29Checked (Chain.cons round30Checked (Chain.cons round31Checked (Chain.cons round32Checked (Chain.cons round33Checked (Chain.cons round34Checked (Chain.cons round35Checked (Chain.cons round36Checked (Chain.cons round37Checked (Chain.cons round38Checked (Chain.cons round39Checked (Chain.cons round40Checked (Chain.cons round41Checked (Chain.cons round42Checked (Chain.cons round43Checked (Chain.cons round44Checked (Chain.cons round45Checked (Chain.cons round46Checked (Chain.cons round47Checked (Chain.cons round48Checked (Chain.cons round49Checked (Chain.cons round50Checked (Chain.cons round51Checked (Chain.cons round52Checked (Chain.cons round53Checked (Chain.cons round54Checked (Chain.cons round55Checked (Chain.cons round56Checked (Chain.cons round57Checked (Chain.cons round58Checked (Chain.cons round59Checked (Chain.cons round60Checked (Chain.cons round61Checked (Chain.cons round62Checked (Chain.cons round63Checked (Chain.nil _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem roundsChecked : Checked ((List.range 64).foldlM (fun value item => (StructuralProgram.roundStep scheduleOutput) item value) (initialOutput)) expand63After round63Output round63After roundsChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ roundsChain

noncomputable def serializeChunk : List WitnessErasure.Code.Top := serialize0Chunk ++ (serialize1Chunk ++ (serialize2Chunk ++ (serialize3Chunk ++ (serialize4Chunk ++ (serialize5Chunk ++ (serialize6Chunk ++ (serialize7Chunk ++ ([]))))))))
theorem serializeChain : Chain frame observe (StructuralProgram.serializeStep) (feedforwardOutput.toList) feedforwardAfter (#[]) serialize7After serialize7Output serializeChunk := by
  exact Chain.cons serialize0Checked (Chain.cons serialize1Checked (Chain.cons serialize2Checked (Chain.cons serialize3Checked (Chain.cons serialize4Checked (Chain.cons serialize5Checked (Chain.cons serialize6Checked (Chain.cons serialize7Checked (Chain.nil _ _))))))))
theorem serializeChecked : Checked ((feedforwardOutput.toList).foldlM (fun value item => (StructuralProgram.serializeStep) item value) (#[])) feedforwardAfter serialize7Output serialize7After serializeChunk :=
  Chain.checked _ _ _ _ _ _ _ _ _ serializeChain

noncomputable def fullChunk : List WitnessErasure.Code.Top := inputChunk ++ (initialChunk ++ (paddingChunk ++ (packingChunk ++ (scheduleChunk ++ (roundsChunk ++ (feedforwardChunk ++ (serializeChunk ++ (publicChunk ++ ([])))))))))
theorem sourceChecked : Checked Synthesis.synthesize beginCursor () publicAfter fullChunk := by
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
  simpa only [List.append_nil, StructuralCheckpoints.publicAction, StructuralCheckpoints.publicOutput,
    StructuralProgram.expose] using publicChecked

/-- Expose the initial state syntactically before applying the observation
projection, so elaboration never needs to evaluate the closed source action. -/
theorem observed_at {α : Type} (action : Synthesis.Build α) (next : Nat)
    (constants : List (Nat × Halo2.Cell)) (output : α)
    (after : Cursor) (chunk : List WitnessErasure.Code.Top)
    (checked : Checked action ⟨next, constants⟩ output after chunk) :
    observe (action ⟨#[], next, constants⟩).2.steps = chunk :=
  Checked.observed action ⟨next, constants⟩ output after chunk checked

theorem observed_initial {α : Type} (action : Synthesis.Build α) (output : α)
    (after : Cursor) (chunk : List WitnessErasure.Code.Top)
    (checked : Checked action beginCursor output after chunk) :
    observe (Synthesis.runSteps action) = chunk :=
  observed_at action 0 [] output after chunk checked

attribute [local irreducible] Synthesis.synthesize Synthesis.schedule Synthesis.runSteps fullChunk

theorem source_code : observe Synthesis.schedule = fullChunk := by
  unfold Synthesis.schedule
  exact observed_initial Synthesis.synthesize () publicAfter fullChunk sourceChecked

/-- All 142 full-code stage chunks, in source order, including the public-copy
stage. The only remaining suffix consists of the five original table loads. -/
theorem fullChunk_eq :
    fullChunk ++ (Preimage.tables.operations 0).map WitnessErasure.Code.encode =
      (WitnessCheckpoints.preimageOperations 0).map WitnessErasure.Code.encode := by
  simp only [fullChunk, prepareChunk, expandChunk, scheduleChunk, roundsChunk, serializeChunk,
    WitnessCheckpoints.preimageOperations, WitnessCheckpoints.bodyOperations,
    WitnessCheckpoints.preparedOperations, WitnessCheckpoints.expandedOperations,
    WitnessCheckpoints.scheduledOperations, WitnessCheckpoints.roundsOperations,
    WitnessCheckpoints.serializedOperations,
    List.map_append, List.append_nil, List.append_assoc]

theorem tables_eq : Preimage.tables.operations 0 = Synthesis.tableOperations := rfl

attribute [local irreducible] WitnessCircuit.preimageCircuit WitnessCheckpoints.preimageOperations
  Synthesis.toOperations Synthesis.operations

/-- Exact original comparison, assembled from bounded kernel-checked stages.
Advice programs alone are erased by Code; all native configuration payloads,
fixed coefficients, public copies and table values remain literal source terms. -/
theorem reference_code :
    ((WitnessCircuit.preimageCircuit WitnessErasure.referenceInput).operations).map
        WitnessErasure.Code.encode =
      (Synthesis.operations SHA256.activation).map WitnessErasure.Code.encode := by
  calc
    _ = ((WitnessCircuit.preimageCircuit Preimage.privatePrograms).operations).map
          WitnessErasure.Code.encode :=
      input_independent WitnessErasure.referenceInput Preimage.privatePrograms
    _ = (WitnessCheckpoints.preimageOperations 0).map WitnessErasure.Code.encode :=
      congrArg (List.map WitnessErasure.Code.encode) (WitnessCheckpoints.preimage_operations 0)
    _ = fullChunk ++ (Preimage.tables.operations 0).map WitnessErasure.Code.encode :=
      fullChunk_eq.symm
    _ = observe Synthesis.schedule ++
          (Preimage.tables.operations 0).map WitnessErasure.Code.encode :=
      congrArg (fun code => code ++ (Preimage.tables.operations 0).map WitnessErasure.Code.encode)
        source_code.symm
    _ = (Synthesis.operations SHA256.activation).map WitnessErasure.Code.encode := by
      rw [Synthesis.operations, List.map_append, tables_eq]
      unfold observe Synthesis.toOperations
      rfl

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
