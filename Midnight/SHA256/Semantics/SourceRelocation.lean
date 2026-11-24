import Midnight.SHA256.WitnessErasure
import Midnight.SHA256.Semantics.WitnessCheckpointComposition
import Midnight.SHA256.Semantics.SourceRelocationLeaves

/-! Advice-erased relocation of the actual witness source. Bounded source-return
proofs establish every checkpoint state; the shift leaves preserve all configured
constraints, fixed values, table data, and ordered equality copies. -/
namespace Midnight.SHA256.Semantics.SourceRelocation
open Halo2 WitnessCheckpoints

attribute [local irreducible] WitnessCircuit.body WitnessCircuit.synthesize WitnessCircuit.preimageCircuit
  Preimage.tables
  inputOperations initialOperations paddingOperations packingOperations prepare0Operations prepare1Operations prepare2Operations prepare3Operations prepare4Operations prepare5Operations prepare6Operations prepare7Operations prepare8Operations prepare9Operations prepare10Operations prepare11Operations prepare12Operations prepare13Operations prepare14Operations prepare15Operations expand16Operations expand17Operations expand18Operations expand19Operations expand20Operations expand21Operations expand22Operations expand23Operations expand24Operations expand25Operations expand26Operations expand27Operations expand28Operations expand29Operations expand30Operations expand31Operations expand32Operations expand33Operations expand34Operations expand35Operations expand36Operations expand37Operations expand38Operations expand39Operations expand40Operations expand41Operations expand42Operations expand43Operations expand44Operations expand45Operations expand46Operations expand47Operations expand48Operations expand49Operations expand50Operations expand51Operations expand52Operations expand53Operations expand54Operations expand55Operations expand56Operations expand57Operations expand58Operations expand59Operations expand60Operations expand61Operations expand62Operations expand63Operations round0Operations round1Operations round2Operations round3Operations round4Operations round5Operations round6Operations round7Operations round8Operations round9Operations round10Operations round11Operations round12Operations round13Operations round14Operations round15Operations round16Operations round17Operations round18Operations round19Operations round20Operations round21Operations round22Operations round23Operations round24Operations round25Operations round26Operations round27Operations round28Operations round29Operations round30Operations round31Operations round32Operations round33Operations round34Operations round35Operations round36Operations round37Operations round38Operations round39Operations round40Operations round41Operations round42Operations round43Operations round44Operations round45Operations round46Operations round47Operations round48Operations round49Operations round50Operations round51Operations round52Operations round53Operations round54Operations round55Operations round56Operations round57Operations round58Operations round59Operations round60Operations round61Operations round62Operations round63Operations feedforwardOperations serialize0Operations serialize1Operations serialize2Operations serialize3Operations serialize4Operations serialize5Operations serialize6Operations serialize7Operations publicOperations

private theorem erase_append (left right : Operations F) :
    WitnessErasure.operations (left ++ right) =
      WitnessErasure.operations left ++ WitnessErasure.operations right := List.map_append

private theorem relocate_append (offset : Nat) (left right : Operations F) :
    Chips.Relocation.operations offset (left ++ right) =
      Chips.Relocation.operations offset left ++ Chips.Relocation.operations offset right :=
  List.map_append

private theorem erase_nil : WitnessErasure.operations ([] : Operations F) = [] := rfl
private theorem relocate_nil (offset : Nat) : Chips.Relocation.operations offset ([] : Operations F) = [] := rfl

/-- Relocation of the complete data path, obtained by composing the checked
source chunks; no full-trace reduction or assumed metadata equality is used. -/
theorem body_chunks (offset : Nat) :
    WitnessErasure.operations (bodyOperations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (bodyOperations 0)) := by
  simp only [bodyOperations, scheduledOperations, preparedOperations, expandedOperations,
    roundsOperations, serializedOperations, erase_append, relocate_append, erase_nil, relocate_nil,
    inputRelocates offset, initialRelocates offset, paddingRelocates offset, packingRelocates offset,
    prepare0Relocates offset, prepare1Relocates offset, prepare2Relocates offset, prepare3Relocates offset,
    prepare4Relocates offset, prepare5Relocates offset, prepare6Relocates offset, prepare7Relocates offset,
    prepare8Relocates offset, prepare9Relocates offset, prepare10Relocates offset, prepare11Relocates offset,
    prepare12Relocates offset, prepare13Relocates offset, prepare14Relocates offset, prepare15Relocates offset,
    expand16Relocates offset, expand17Relocates offset, expand18Relocates offset, expand19Relocates offset,
    expand20Relocates offset, expand21Relocates offset, expand22Relocates offset, expand23Relocates offset,
    expand24Relocates offset, expand25Relocates offset, expand26Relocates offset, expand27Relocates offset,
    expand28Relocates offset, expand29Relocates offset, expand30Relocates offset, expand31Relocates offset,
    expand32Relocates offset, expand33Relocates offset, expand34Relocates offset, expand35Relocates offset,
    expand36Relocates offset, expand37Relocates offset, expand38Relocates offset, expand39Relocates offset,
    expand40Relocates offset, expand41Relocates offset, expand42Relocates offset, expand43Relocates offset,
    expand44Relocates offset, expand45Relocates offset, expand46Relocates offset, expand47Relocates offset,
    expand48Relocates offset, expand49Relocates offset, expand50Relocates offset, expand51Relocates offset,
    expand52Relocates offset, expand53Relocates offset, expand54Relocates offset, expand55Relocates offset,
    expand56Relocates offset, expand57Relocates offset, expand58Relocates offset, expand59Relocates offset,
    expand60Relocates offset, expand61Relocates offset, expand62Relocates offset, expand63Relocates offset,
    round0Relocates offset, round1Relocates offset, round2Relocates offset, round3Relocates offset,
    round4Relocates offset, round5Relocates offset, round6Relocates offset, round7Relocates offset,
    round8Relocates offset, round9Relocates offset, round10Relocates offset, round11Relocates offset,
    round12Relocates offset, round13Relocates offset, round14Relocates offset, round15Relocates offset,
    round16Relocates offset, round17Relocates offset, round18Relocates offset, round19Relocates offset,
    round20Relocates offset, round21Relocates offset, round22Relocates offset, round23Relocates offset,
    round24Relocates offset, round25Relocates offset, round26Relocates offset, round27Relocates offset,
    round28Relocates offset, round29Relocates offset, round30Relocates offset, round31Relocates offset,
    round32Relocates offset, round33Relocates offset, round34Relocates offset, round35Relocates offset,
    round36Relocates offset, round37Relocates offset, round38Relocates offset, round39Relocates offset,
    round40Relocates offset, round41Relocates offset, round42Relocates offset, round43Relocates offset,
    round44Relocates offset, round45Relocates offset, round46Relocates offset, round47Relocates offset,
    round48Relocates offset, round49Relocates offset, round50Relocates offset, round51Relocates offset,
    round52Relocates offset, round53Relocates offset, round54Relocates offset, round55Relocates offset,
    round56Relocates offset, round57Relocates offset, round58Relocates offset, round59Relocates offset,
    round60Relocates offset, round61Relocates offset, round62Relocates offset, round63Relocates offset,
    feedforwardRelocates offset, serialize0Relocates offset, serialize1Relocates offset, serialize2Relocates offset,
    serialize3Relocates offset, serialize4Relocates offset, serialize5Relocates offset, serialize6Relocates offset,
    serialize7Relocates offset]

private theorem tables_relocate (offset : Nat) :
    Chips.Relocation.operations offset (WitnessErasure.operations (Preimage.tables.operations 0)) =
      WitnessErasure.operations (Preimage.tables.operations 0) := by
  unfold Preimage.tables shaTables
  rfl

/-- Arbitrary starting-region identity for the actual private-hint interface. -/
theorem private_preimage (offset : Nat) :
    WitnessErasure.operations ((WitnessCircuit.preimageCircuit Preimage.privatePrograms).operations offset) =
      Chips.Relocation.operations offset
        (WitnessErasure.operations ((WitnessCircuit.preimageCircuit Preimage.privatePrograms).operations 0)) := by
  rw [WitnessCheckpoints.preimage_operations, WitnessCheckpoints.preimage_operations]
  simp only [preimageOperations, erase_append, relocate_append, body_chunks offset,
    publicRelocates offset, tables_relocate]

/-- The exact native keygen operation stream, for every 24 input recipes and
starting region. Only advice programs are erased; all other source data stays. -/
theorem preimage_operations (input : Vector (WitgenIR F 1) 24) (offset : Nat) :
    WitnessErasure.operations ((WitnessCircuit.preimageCircuit input).operations offset) =
      Chips.Relocation.operations offset (Synthesis.operations SHA256.activation) := by
  calc
    _ = WitnessErasure.operations
        ((WitnessCircuit.preimageCircuit Preimage.privatePrograms).operations offset) :=
      WitnessErasure.preimage_operations_independent input Preimage.privatePrograms offset
    _ = Chips.Relocation.operations offset
        (WitnessErasure.operations ((WitnessCircuit.preimageCircuit Preimage.privatePrograms).operations 0)) :=
      private_preimage offset
    _ = Chips.Relocation.operations offset (Synthesis.operations SHA256.activation) :=
      congrArg (Chips.Relocation.operations offset)
        (WitnessErasure.preimage_operations_eq_source Preimage.privatePrograms)

end Midnight.SHA256.Semantics.SourceRelocation
