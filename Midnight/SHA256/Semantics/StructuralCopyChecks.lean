import Midnight.Chips.SynthesisCopySegment
import Midnight.SHA256.Semantics.StructuralComposition
import Midnight.SHA256.Semantics.StructuralCopyTable
namespace Midnight.SHA256.Semantics.StructuralCopies
open Chips.SynthesisCopySegment StructuralCheckpoints
set_option Elab.async false
set_option maxRecDepth 100000

theorem inputChecked : Segment StructuralCopyTable.table beginCursor.next inputAfter.next inputChunk := by
  constructor <;> decide +kernel

theorem initialChecked : Segment StructuralCopyTable.table inputAfter.next initialAfter.next initialChunk := by
  constructor <;> decide +kernel

theorem paddingChecked : Segment StructuralCopyTable.table initialAfter.next paddingAfter.next paddingChunk := by
  constructor <;> decide +kernel

theorem packingChecked : Segment StructuralCopyTable.table paddingAfter.next packingAfter.next packingChunk := by
  constructor <;> decide +kernel

theorem prepare0Checked : Segment StructuralCopyTable.table packingAfter.next prepare0After.next prepare0Chunk := by
  constructor <;> decide +kernel

theorem prepare1Checked : Segment StructuralCopyTable.table prepare0After.next prepare1After.next prepare1Chunk := by
  constructor <;> decide +kernel

theorem prepare2Checked : Segment StructuralCopyTable.table prepare1After.next prepare2After.next prepare2Chunk := by
  constructor <;> decide +kernel

theorem prepare3Checked : Segment StructuralCopyTable.table prepare2After.next prepare3After.next prepare3Chunk := by
  constructor <;> decide +kernel

theorem prepare4Checked : Segment StructuralCopyTable.table prepare3After.next prepare4After.next prepare4Chunk := by
  constructor <;> decide +kernel

theorem prepare5Checked : Segment StructuralCopyTable.table prepare4After.next prepare5After.next prepare5Chunk := by
  constructor <;> decide +kernel

theorem prepare6Checked : Segment StructuralCopyTable.table prepare5After.next prepare6After.next prepare6Chunk := by
  constructor <;> decide +kernel

theorem prepare7Checked : Segment StructuralCopyTable.table prepare6After.next prepare7After.next prepare7Chunk := by
  constructor <;> decide +kernel

theorem prepare8Checked : Segment StructuralCopyTable.table prepare7After.next prepare8After.next prepare8Chunk := by
  constructor <;> decide +kernel

theorem prepare9Checked : Segment StructuralCopyTable.table prepare8After.next prepare9After.next prepare9Chunk := by
  constructor <;> decide +kernel

theorem prepare10Checked : Segment StructuralCopyTable.table prepare9After.next prepare10After.next prepare10Chunk := by
  constructor <;> decide +kernel

theorem prepare11Checked : Segment StructuralCopyTable.table prepare10After.next prepare11After.next prepare11Chunk := by
  constructor <;> decide +kernel

theorem prepare12Checked : Segment StructuralCopyTable.table prepare11After.next prepare12After.next prepare12Chunk := by
  constructor <;> decide +kernel

theorem prepare13Checked : Segment StructuralCopyTable.table prepare12After.next prepare13After.next prepare13Chunk := by
  constructor <;> decide +kernel

theorem prepare14Checked : Segment StructuralCopyTable.table prepare13After.next prepare14After.next prepare14Chunk := by
  constructor <;> decide +kernel

theorem prepare15Checked : Segment StructuralCopyTable.table prepare14After.next prepare15After.next prepare15Chunk := by
  constructor <;> decide +kernel

theorem expand16Checked : Segment StructuralCopyTable.table prepare15After.next expand16After.next expand16Chunk := by
  constructor <;> decide +kernel

theorem expand17Checked : Segment StructuralCopyTable.table expand16After.next expand17After.next expand17Chunk := by
  constructor <;> decide +kernel

theorem expand18Checked : Segment StructuralCopyTable.table expand17After.next expand18After.next expand18Chunk := by
  constructor <;> decide +kernel

theorem expand19Checked : Segment StructuralCopyTable.table expand18After.next expand19After.next expand19Chunk := by
  constructor <;> decide +kernel

theorem expand20Checked : Segment StructuralCopyTable.table expand19After.next expand20After.next expand20Chunk := by
  constructor <;> decide +kernel

theorem expand21Checked : Segment StructuralCopyTable.table expand20After.next expand21After.next expand21Chunk := by
  constructor <;> decide +kernel

theorem expand22Checked : Segment StructuralCopyTable.table expand21After.next expand22After.next expand22Chunk := by
  constructor <;> decide +kernel

theorem expand23Checked : Segment StructuralCopyTable.table expand22After.next expand23After.next expand23Chunk := by
  constructor <;> decide +kernel

theorem expand24Checked : Segment StructuralCopyTable.table expand23After.next expand24After.next expand24Chunk := by
  constructor <;> decide +kernel

theorem expand25Checked : Segment StructuralCopyTable.table expand24After.next expand25After.next expand25Chunk := by
  constructor <;> decide +kernel

theorem expand26Checked : Segment StructuralCopyTable.table expand25After.next expand26After.next expand26Chunk := by
  constructor <;> decide +kernel

theorem expand27Checked : Segment StructuralCopyTable.table expand26After.next expand27After.next expand27Chunk := by
  constructor <;> decide +kernel

theorem expand28Checked : Segment StructuralCopyTable.table expand27After.next expand28After.next expand28Chunk := by
  constructor <;> decide +kernel

theorem expand29Checked : Segment StructuralCopyTable.table expand28After.next expand29After.next expand29Chunk := by
  constructor <;> decide +kernel

theorem expand30Checked : Segment StructuralCopyTable.table expand29After.next expand30After.next expand30Chunk := by
  constructor <;> decide +kernel

theorem expand31Checked : Segment StructuralCopyTable.table expand30After.next expand31After.next expand31Chunk := by
  constructor <;> decide +kernel

theorem expand32Checked : Segment StructuralCopyTable.table expand31After.next expand32After.next expand32Chunk := by
  constructor <;> decide +kernel

theorem expand33Checked : Segment StructuralCopyTable.table expand32After.next expand33After.next expand33Chunk := by
  constructor <;> decide +kernel

theorem expand34Checked : Segment StructuralCopyTable.table expand33After.next expand34After.next expand34Chunk := by
  constructor <;> decide +kernel

theorem expand35Checked : Segment StructuralCopyTable.table expand34After.next expand35After.next expand35Chunk := by
  constructor <;> decide +kernel

theorem expand36Checked : Segment StructuralCopyTable.table expand35After.next expand36After.next expand36Chunk := by
  constructor <;> decide +kernel

theorem expand37Checked : Segment StructuralCopyTable.table expand36After.next expand37After.next expand37Chunk := by
  constructor <;> decide +kernel

theorem expand38Checked : Segment StructuralCopyTable.table expand37After.next expand38After.next expand38Chunk := by
  constructor <;> decide +kernel

theorem expand39Checked : Segment StructuralCopyTable.table expand38After.next expand39After.next expand39Chunk := by
  constructor <;> decide +kernel

theorem expand40Checked : Segment StructuralCopyTable.table expand39After.next expand40After.next expand40Chunk := by
  constructor <;> decide +kernel

theorem expand41Checked : Segment StructuralCopyTable.table expand40After.next expand41After.next expand41Chunk := by
  constructor <;> decide +kernel

theorem expand42Checked : Segment StructuralCopyTable.table expand41After.next expand42After.next expand42Chunk := by
  constructor <;> decide +kernel

theorem expand43Checked : Segment StructuralCopyTable.table expand42After.next expand43After.next expand43Chunk := by
  constructor <;> decide +kernel

theorem expand44Checked : Segment StructuralCopyTable.table expand43After.next expand44After.next expand44Chunk := by
  constructor <;> decide +kernel

theorem expand45Checked : Segment StructuralCopyTable.table expand44After.next expand45After.next expand45Chunk := by
  constructor <;> decide +kernel

theorem expand46Checked : Segment StructuralCopyTable.table expand45After.next expand46After.next expand46Chunk := by
  constructor <;> decide +kernel

theorem expand47Checked : Segment StructuralCopyTable.table expand46After.next expand47After.next expand47Chunk := by
  constructor <;> decide +kernel

theorem expand48Checked : Segment StructuralCopyTable.table expand47After.next expand48After.next expand48Chunk := by
  constructor <;> decide +kernel

theorem expand49Checked : Segment StructuralCopyTable.table expand48After.next expand49After.next expand49Chunk := by
  constructor <;> decide +kernel

theorem expand50Checked : Segment StructuralCopyTable.table expand49After.next expand50After.next expand50Chunk := by
  constructor <;> decide +kernel

theorem expand51Checked : Segment StructuralCopyTable.table expand50After.next expand51After.next expand51Chunk := by
  constructor <;> decide +kernel

theorem expand52Checked : Segment StructuralCopyTable.table expand51After.next expand52After.next expand52Chunk := by
  constructor <;> decide +kernel

theorem expand53Checked : Segment StructuralCopyTable.table expand52After.next expand53After.next expand53Chunk := by
  constructor <;> decide +kernel

theorem expand54Checked : Segment StructuralCopyTable.table expand53After.next expand54After.next expand54Chunk := by
  constructor <;> decide +kernel

theorem expand55Checked : Segment StructuralCopyTable.table expand54After.next expand55After.next expand55Chunk := by
  constructor <;> decide +kernel

theorem expand56Checked : Segment StructuralCopyTable.table expand55After.next expand56After.next expand56Chunk := by
  constructor <;> decide +kernel

theorem expand57Checked : Segment StructuralCopyTable.table expand56After.next expand57After.next expand57Chunk := by
  constructor <;> decide +kernel

theorem expand58Checked : Segment StructuralCopyTable.table expand57After.next expand58After.next expand58Chunk := by
  constructor <;> decide +kernel

theorem expand59Checked : Segment StructuralCopyTable.table expand58After.next expand59After.next expand59Chunk := by
  constructor <;> decide +kernel

theorem expand60Checked : Segment StructuralCopyTable.table expand59After.next expand60After.next expand60Chunk := by
  constructor <;> decide +kernel

theorem expand61Checked : Segment StructuralCopyTable.table expand60After.next expand61After.next expand61Chunk := by
  constructor <;> decide +kernel

theorem expand62Checked : Segment StructuralCopyTable.table expand61After.next expand62After.next expand62Chunk := by
  constructor <;> decide +kernel

theorem expand63Checked : Segment StructuralCopyTable.table expand62After.next expand63After.next expand63Chunk := by
  constructor <;> decide +kernel

theorem round0Checked : Segment StructuralCopyTable.table expand63After.next round0After.next round0Chunk := by
  constructor <;> decide +kernel

theorem round1Checked : Segment StructuralCopyTable.table round0After.next round1After.next round1Chunk := by
  constructor <;> decide +kernel

theorem round2Checked : Segment StructuralCopyTable.table round1After.next round2After.next round2Chunk := by
  constructor <;> decide +kernel

theorem round3Checked : Segment StructuralCopyTable.table round2After.next round3After.next round3Chunk := by
  constructor <;> decide +kernel

theorem round4Checked : Segment StructuralCopyTable.table round3After.next round4After.next round4Chunk := by
  constructor <;> decide +kernel

theorem round5Checked : Segment StructuralCopyTable.table round4After.next round5After.next round5Chunk := by
  constructor <;> decide +kernel

theorem round6Checked : Segment StructuralCopyTable.table round5After.next round6After.next round6Chunk := by
  constructor <;> decide +kernel

theorem round7Checked : Segment StructuralCopyTable.table round6After.next round7After.next round7Chunk := by
  constructor <;> decide +kernel

theorem round8Checked : Segment StructuralCopyTable.table round7After.next round8After.next round8Chunk := by
  constructor <;> decide +kernel

theorem round9Checked : Segment StructuralCopyTable.table round8After.next round9After.next round9Chunk := by
  constructor <;> decide +kernel

theorem round10Checked : Segment StructuralCopyTable.table round9After.next round10After.next round10Chunk := by
  constructor <;> decide +kernel

theorem round11Checked : Segment StructuralCopyTable.table round10After.next round11After.next round11Chunk := by
  constructor <;> decide +kernel

theorem round12Checked : Segment StructuralCopyTable.table round11After.next round12After.next round12Chunk := by
  constructor <;> decide +kernel

theorem round13Checked : Segment StructuralCopyTable.table round12After.next round13After.next round13Chunk := by
  constructor <;> decide +kernel

theorem round14Checked : Segment StructuralCopyTable.table round13After.next round14After.next round14Chunk := by
  constructor <;> decide +kernel

theorem round15Checked : Segment StructuralCopyTable.table round14After.next round15After.next round15Chunk := by
  constructor <;> decide +kernel

theorem round16Checked : Segment StructuralCopyTable.table round15After.next round16After.next round16Chunk := by
  constructor <;> decide +kernel

theorem round17Checked : Segment StructuralCopyTable.table round16After.next round17After.next round17Chunk := by
  constructor <;> decide +kernel

theorem round18Checked : Segment StructuralCopyTable.table round17After.next round18After.next round18Chunk := by
  constructor <;> decide +kernel

theorem round19Checked : Segment StructuralCopyTable.table round18After.next round19After.next round19Chunk := by
  constructor <;> decide +kernel

theorem round20Checked : Segment StructuralCopyTable.table round19After.next round20After.next round20Chunk := by
  constructor <;> decide +kernel

theorem round21Checked : Segment StructuralCopyTable.table round20After.next round21After.next round21Chunk := by
  constructor <;> decide +kernel

theorem round22Checked : Segment StructuralCopyTable.table round21After.next round22After.next round22Chunk := by
  constructor <;> decide +kernel

theorem round23Checked : Segment StructuralCopyTable.table round22After.next round23After.next round23Chunk := by
  constructor <;> decide +kernel

theorem round24Checked : Segment StructuralCopyTable.table round23After.next round24After.next round24Chunk := by
  constructor <;> decide +kernel

theorem round25Checked : Segment StructuralCopyTable.table round24After.next round25After.next round25Chunk := by
  constructor <;> decide +kernel

theorem round26Checked : Segment StructuralCopyTable.table round25After.next round26After.next round26Chunk := by
  constructor <;> decide +kernel

theorem round27Checked : Segment StructuralCopyTable.table round26After.next round27After.next round27Chunk := by
  constructor <;> decide +kernel

theorem round28Checked : Segment StructuralCopyTable.table round27After.next round28After.next round28Chunk := by
  constructor <;> decide +kernel

theorem round29Checked : Segment StructuralCopyTable.table round28After.next round29After.next round29Chunk := by
  constructor <;> decide +kernel

theorem round30Checked : Segment StructuralCopyTable.table round29After.next round30After.next round30Chunk := by
  constructor <;> decide +kernel

theorem round31Checked : Segment StructuralCopyTable.table round30After.next round31After.next round31Chunk := by
  constructor <;> decide +kernel

theorem round32Checked : Segment StructuralCopyTable.table round31After.next round32After.next round32Chunk := by
  constructor <;> decide +kernel

theorem round33Checked : Segment StructuralCopyTable.table round32After.next round33After.next round33Chunk := by
  constructor <;> decide +kernel

theorem round34Checked : Segment StructuralCopyTable.table round33After.next round34After.next round34Chunk := by
  constructor <;> decide +kernel

theorem round35Checked : Segment StructuralCopyTable.table round34After.next round35After.next round35Chunk := by
  constructor <;> decide +kernel

theorem round36Checked : Segment StructuralCopyTable.table round35After.next round36After.next round36Chunk := by
  constructor <;> decide +kernel

theorem round37Checked : Segment StructuralCopyTable.table round36After.next round37After.next round37Chunk := by
  constructor <;> decide +kernel

theorem round38Checked : Segment StructuralCopyTable.table round37After.next round38After.next round38Chunk := by
  constructor <;> decide +kernel

theorem round39Checked : Segment StructuralCopyTable.table round38After.next round39After.next round39Chunk := by
  constructor <;> decide +kernel

theorem round40Checked : Segment StructuralCopyTable.table round39After.next round40After.next round40Chunk := by
  constructor <;> decide +kernel

theorem round41Checked : Segment StructuralCopyTable.table round40After.next round41After.next round41Chunk := by
  constructor <;> decide +kernel

theorem round42Checked : Segment StructuralCopyTable.table round41After.next round42After.next round42Chunk := by
  constructor <;> decide +kernel

theorem round43Checked : Segment StructuralCopyTable.table round42After.next round43After.next round43Chunk := by
  constructor <;> decide +kernel

theorem round44Checked : Segment StructuralCopyTable.table round43After.next round44After.next round44Chunk := by
  constructor <;> decide +kernel

theorem round45Checked : Segment StructuralCopyTable.table round44After.next round45After.next round45Chunk := by
  constructor <;> decide +kernel

theorem round46Checked : Segment StructuralCopyTable.table round45After.next round46After.next round46Chunk := by
  constructor <;> decide +kernel

theorem round47Checked : Segment StructuralCopyTable.table round46After.next round47After.next round47Chunk := by
  constructor <;> decide +kernel

theorem round48Checked : Segment StructuralCopyTable.table round47After.next round48After.next round48Chunk := by
  constructor <;> decide +kernel

theorem round49Checked : Segment StructuralCopyTable.table round48After.next round49After.next round49Chunk := by
  constructor <;> decide +kernel

theorem round50Checked : Segment StructuralCopyTable.table round49After.next round50After.next round50Chunk := by
  constructor <;> decide +kernel

theorem round51Checked : Segment StructuralCopyTable.table round50After.next round51After.next round51Chunk := by
  constructor <;> decide +kernel

theorem round52Checked : Segment StructuralCopyTable.table round51After.next round52After.next round52Chunk := by
  constructor <;> decide +kernel

theorem round53Checked : Segment StructuralCopyTable.table round52After.next round53After.next round53Chunk := by
  constructor <;> decide +kernel

theorem round54Checked : Segment StructuralCopyTable.table round53After.next round54After.next round54Chunk := by
  constructor <;> decide +kernel

theorem round55Checked : Segment StructuralCopyTable.table round54After.next round55After.next round55Chunk := by
  constructor <;> decide +kernel

theorem round56Checked : Segment StructuralCopyTable.table round55After.next round56After.next round56Chunk := by
  constructor <;> decide +kernel

theorem round57Checked : Segment StructuralCopyTable.table round56After.next round57After.next round57Chunk := by
  constructor <;> decide +kernel

theorem round58Checked : Segment StructuralCopyTable.table round57After.next round58After.next round58Chunk := by
  constructor <;> decide +kernel

theorem round59Checked : Segment StructuralCopyTable.table round58After.next round59After.next round59Chunk := by
  constructor <;> decide +kernel

theorem round60Checked : Segment StructuralCopyTable.table round59After.next round60After.next round60Chunk := by
  constructor <;> decide +kernel

theorem round61Checked : Segment StructuralCopyTable.table round60After.next round61After.next round61Chunk := by
  constructor <;> decide +kernel

theorem round62Checked : Segment StructuralCopyTable.table round61After.next round62After.next round62Chunk := by
  constructor <;> decide +kernel

theorem round63Checked : Segment StructuralCopyTable.table round62After.next round63After.next round63Chunk := by
  constructor <;> decide +kernel

theorem feedforwardChecked : Segment StructuralCopyTable.table round63After.next feedforwardAfter.next feedforwardChunk := by
  constructor <;> decide +kernel

theorem serialize0Checked : Segment StructuralCopyTable.table feedforwardAfter.next serialize0After.next serialize0Chunk := by
  constructor <;> decide +kernel

theorem serialize1Checked : Segment StructuralCopyTable.table serialize0After.next serialize1After.next serialize1Chunk := by
  constructor <;> decide +kernel

theorem serialize2Checked : Segment StructuralCopyTable.table serialize1After.next serialize2After.next serialize2Chunk := by
  constructor <;> decide +kernel

theorem serialize3Checked : Segment StructuralCopyTable.table serialize2After.next serialize3After.next serialize3Chunk := by
  constructor <;> decide +kernel

theorem serialize4Checked : Segment StructuralCopyTable.table serialize3After.next serialize4After.next serialize4Chunk := by
  constructor <;> decide +kernel

theorem serialize5Checked : Segment StructuralCopyTable.table serialize4After.next serialize5After.next serialize5Chunk := by
  constructor <;> decide +kernel

theorem serialize6Checked : Segment StructuralCopyTable.table serialize5After.next serialize6After.next serialize6Chunk := by
  constructor <;> decide +kernel

theorem serialize7Checked : Segment StructuralCopyTable.table serialize6After.next serialize7After.next serialize7Chunk := by
  constructor <;> decide +kernel

theorem publicChecked : Segment StructuralCopyTable.table serialize7After.next publicAfter.next publicChunk := by
  constructor <;> decide +kernel

end Midnight.SHA256.Semantics.StructuralCopies
