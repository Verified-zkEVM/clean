import Midnight.SHA256.Semantics.WitnessCheckpointChecks
import Midnight.SHA256.Semantics.WitnessCheckpointProgram
import Midnight.SHA256.Semantics.PreimageSource

/-! Compose the exact checked source stages. All operation chunks are original
witness-bearing operations; metadata is used only through proved Returns. -/
namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel WitnessCheckpointProgram
attribute [local irreducible] WitnessCircuit.body WitnessCircuit.preimageCircuit
attribute [local irreducible] inputOutput initialOutput paddingOutput packingOutput prepare0Output prepare1Output prepare2Output prepare3Output prepare4Output prepare5Output prepare6Output prepare7Output prepare8Output prepare9Output prepare10Output prepare11Output prepare12Output prepare13Output prepare14Output prepare15Output expand16Output expand17Output expand18Output expand19Output expand20Output expand21Output expand22Output expand23Output expand24Output expand25Output expand26Output expand27Output expand28Output expand29Output expand30Output expand31Output expand32Output expand33Output expand34Output expand35Output expand36Output expand37Output expand38Output expand39Output expand40Output expand41Output expand42Output expand43Output expand44Output expand45Output expand46Output expand47Output expand48Output expand49Output expand50Output expand51Output expand52Output expand53Output expand54Output expand55Output expand56Output expand57Output expand58Output expand59Output expand60Output expand61Output expand62Output expand63Output round0Output round1Output round2Output round3Output round4Output round5Output round6Output round7Output round8Output round9Output round10Output round11Output round12Output round13Output round14Output round15Output round16Output round17Output round18Output round19Output round20Output round21Output round22Output round23Output round24Output round25Output round26Output round27Output round28Output round29Output round30Output round31Output round32Output round33Output round34Output round35Output round36Output round37Output round38Output round39Output round40Output round41Output round42Output round43Output round44Output round45Output round46Output round47Output round48Output round49Output round50Output round51Output round52Output round53Output round54Output round55Output round56Output round57Output round58Output round59Output round60Output round61Output round62Output round63Output serialize0Output serialize1Output serialize2Output serialize3Output serialize4Output serialize5Output serialize6Output serialize7Output
attribute [local irreducible] inputAfter initialAfter paddingAfter packingAfter prepare0After prepare1After prepare2After prepare3After prepare4After prepare5After prepare6After prepare7After prepare8After prepare9After prepare10After prepare11After prepare12After prepare13After prepare14After prepare15After expand16After expand17After expand18After expand19After expand20After expand21After expand22After expand23After expand24After expand25After expand26After expand27After expand28After expand29After expand30After expand31After expand32After expand33After expand34After expand35After expand36After expand37After expand38After expand39After expand40After expand41After expand42After expand43After expand44After expand45After expand46After expand47After expand48After expand49After expand50After expand51After expand52After expand53After expand54After expand55After expand56After expand57After expand58After expand59After expand60After expand61After expand62After expand63After round0After round1After round2After round3After round4After round5After round6After round7After round8After round9After round10After round11After round12After round13After round14After round15After round16After round17After round18After round19After round20After round21After round22After round23After round24After round25After round26After round27After round28After round29After round30After round31After round32After round33After round34After round35After round36After round37After round38After round39After round40After round41After round42After round43After round44After round45After round46After round47After round48After round49After round50After round51After round52After round53After round54After round55After round56After round57After round58After round59After round60After round61After round62After round63After feedforwardAfter serialize0After serialize1After serialize2After serialize3After serialize4After serialize5After serialize6After serialize7After
attribute [local irreducible] inputOperations initialOperations paddingOperations packingOperations prepare0Operations prepare1Operations prepare2Operations prepare3Operations prepare4Operations prepare5Operations prepare6Operations prepare7Operations prepare8Operations prepare9Operations prepare10Operations prepare11Operations prepare12Operations prepare13Operations prepare14Operations prepare15Operations expand16Operations expand17Operations expand18Operations expand19Operations expand20Operations expand21Operations expand22Operations expand23Operations expand24Operations expand25Operations expand26Operations expand27Operations expand28Operations expand29Operations expand30Operations expand31Operations expand32Operations expand33Operations expand34Operations expand35Operations expand36Operations expand37Operations expand38Operations expand39Operations expand40Operations expand41Operations expand42Operations expand43Operations expand44Operations expand45Operations expand46Operations expand47Operations expand48Operations expand49Operations expand50Operations expand51Operations expand52Operations expand53Operations expand54Operations expand55Operations expand56Operations expand57Operations expand58Operations expand59Operations expand60Operations expand61Operations expand62Operations expand63Operations round0Operations round1Operations round2Operations round3Operations round4Operations round5Operations round6Operations round7Operations round8Operations round9Operations round10Operations round11Operations round12Operations round13Operations round14Operations round15Operations round16Operations round17Operations round18Operations round19Operations round20Operations round21Operations round22Operations round23Operations round24Operations round25Operations round26Operations round27Operations round28Operations round29Operations round30Operations round31Operations round32Operations round33Operations round34Operations round35Operations round36Operations round37Operations round38Operations round39Operations round40Operations round41Operations round42Operations round43Operations round44Operations round45Operations round46Operations round47Operations round48Operations round49Operations round50Operations round51Operations round52Operations round53Operations round54Operations round55Operations round56Operations round57Operations round58Operations round59Operations round60Operations round61Operations round62Operations round63Operations feedforwardOperations serialize0Operations serialize1Operations serialize2Operations serialize3Operations serialize4Operations serialize5Operations serialize6Operations serialize7Operations publicOperations

def preparedOperations (offset : Nat) : Operations F :=
  (prepare0Operations offset ++ (prepare1Operations offset ++ (prepare2Operations offset ++ (prepare3Operations offset ++ (prepare4Operations offset ++ (prepare5Operations offset ++ (prepare6Operations offset ++ (prepare7Operations offset ++ (prepare8Operations offset ++ (prepare9Operations offset ++ (prepare10Operations offset ++ (prepare11Operations offset ++ (prepare12Operations offset ++ (prepare13Operations offset ++ (prepare14Operations offset ++ (prepare15Operations offset ++ []))))))))))))))))

theorem preparedChecked (offset : Nat) :
    Checked id ((List.range 16).foldlM (fun value item => prepareStep (packingOutput offset) item value) #[])
      (packingAfter offset) (prepare15Output offset) (prepare15After offset) (preparedOperations offset) := by
  apply checked_foldlM
  unfold preparedOperations
  refine .cons (prepare0Checked offset) ?_
  refine .cons (prepare1Checked offset) ?_
  refine .cons (prepare2Checked offset) ?_
  refine .cons (prepare3Checked offset) ?_
  refine .cons (prepare4Checked offset) ?_
  refine .cons (prepare5Checked offset) ?_
  refine .cons (prepare6Checked offset) ?_
  refine .cons (prepare7Checked offset) ?_
  refine .cons (prepare8Checked offset) ?_
  refine .cons (prepare9Checked offset) ?_
  refine .cons (prepare10Checked offset) ?_
  refine .cons (prepare11Checked offset) ?_
  refine .cons (prepare12Checked offset) ?_
  refine .cons (prepare13Checked offset) ?_
  refine .cons (prepare14Checked offset) ?_
  refine .cons (prepare15Checked offset) ?_
  exact .nil _ _

def expandedOperations (offset : Nat) : Operations F :=
  (expand16Operations offset ++ (expand17Operations offset ++ (expand18Operations offset ++ (expand19Operations offset ++ (expand20Operations offset ++ (expand21Operations offset ++ (expand22Operations offset ++ (expand23Operations offset ++ (expand24Operations offset ++ (expand25Operations offset ++ (expand26Operations offset ++ (expand27Operations offset ++ (expand28Operations offset ++ (expand29Operations offset ++ (expand30Operations offset ++ (expand31Operations offset ++ (expand32Operations offset ++ (expand33Operations offset ++ (expand34Operations offset ++ (expand35Operations offset ++ (expand36Operations offset ++ (expand37Operations offset ++ (expand38Operations offset ++ (expand39Operations offset ++ (expand40Operations offset ++ (expand41Operations offset ++ (expand42Operations offset ++ (expand43Operations offset ++ (expand44Operations offset ++ (expand45Operations offset ++ (expand46Operations offset ++ (expand47Operations offset ++ (expand48Operations offset ++ (expand49Operations offset ++ (expand50Operations offset ++ (expand51Operations offset ++ (expand52Operations offset ++ (expand53Operations offset ++ (expand54Operations offset ++ (expand55Operations offset ++ (expand56Operations offset ++ (expand57Operations offset ++ (expand58Operations offset ++ (expand59Operations offset ++ (expand60Operations offset ++ (expand61Operations offset ++ (expand62Operations offset ++ (expand63Operations offset ++ []))))))))))))))))))))))))))))))))))))))))))))))))

theorem expandedChecked (offset : Nat) :
    Checked id ((List.range' 16 48).foldlM (fun value item => expandStep item value) (prepare15Output offset))
      (prepare15After offset) (expand63Output offset) (expand63After offset) (expandedOperations offset) := by
  apply checked_foldlM
  unfold expandedOperations
  refine .cons (expand16Checked offset) ?_
  refine .cons (expand17Checked offset) ?_
  refine .cons (expand18Checked offset) ?_
  refine .cons (expand19Checked offset) ?_
  refine .cons (expand20Checked offset) ?_
  refine .cons (expand21Checked offset) ?_
  refine .cons (expand22Checked offset) ?_
  refine .cons (expand23Checked offset) ?_
  refine .cons (expand24Checked offset) ?_
  refine .cons (expand25Checked offset) ?_
  refine .cons (expand26Checked offset) ?_
  refine .cons (expand27Checked offset) ?_
  refine .cons (expand28Checked offset) ?_
  refine .cons (expand29Checked offset) ?_
  refine .cons (expand30Checked offset) ?_
  refine .cons (expand31Checked offset) ?_
  refine .cons (expand32Checked offset) ?_
  refine .cons (expand33Checked offset) ?_
  refine .cons (expand34Checked offset) ?_
  refine .cons (expand35Checked offset) ?_
  refine .cons (expand36Checked offset) ?_
  refine .cons (expand37Checked offset) ?_
  refine .cons (expand38Checked offset) ?_
  refine .cons (expand39Checked offset) ?_
  refine .cons (expand40Checked offset) ?_
  refine .cons (expand41Checked offset) ?_
  refine .cons (expand42Checked offset) ?_
  refine .cons (expand43Checked offset) ?_
  refine .cons (expand44Checked offset) ?_
  refine .cons (expand45Checked offset) ?_
  refine .cons (expand46Checked offset) ?_
  refine .cons (expand47Checked offset) ?_
  refine .cons (expand48Checked offset) ?_
  refine .cons (expand49Checked offset) ?_
  refine .cons (expand50Checked offset) ?_
  refine .cons (expand51Checked offset) ?_
  refine .cons (expand52Checked offset) ?_
  refine .cons (expand53Checked offset) ?_
  refine .cons (expand54Checked offset) ?_
  refine .cons (expand55Checked offset) ?_
  refine .cons (expand56Checked offset) ?_
  refine .cons (expand57Checked offset) ?_
  refine .cons (expand58Checked offset) ?_
  refine .cons (expand59Checked offset) ?_
  refine .cons (expand60Checked offset) ?_
  refine .cons (expand61Checked offset) ?_
  refine .cons (expand62Checked offset) ?_
  refine .cons (expand63Checked offset) ?_
  exact .nil _ _

def scheduledOperations (offset : Nat) : Operations F :=
  preparedOperations offset ++ (expandedOperations offset ++ [])

theorem scheduledChecked (offset : Nat) :
    Checked id (schedule (packingOutput offset)) (packingAfter offset)
      (scheduleOutput offset) (expand63After offset) (scheduledOperations offset) := by
  unfold schedule scheduledOperations
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (preparedChecked offset) ?_
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (expandedChecked offset) ?_
  exact checked_pure _ _ _

def roundsOperations (offset : Nat) : Operations F :=
  (round0Operations offset ++ (round1Operations offset ++ (round2Operations offset ++ (round3Operations offset ++ (round4Operations offset ++ (round5Operations offset ++ (round6Operations offset ++ (round7Operations offset ++ (round8Operations offset ++ (round9Operations offset ++ (round10Operations offset ++ (round11Operations offset ++ (round12Operations offset ++ (round13Operations offset ++ (round14Operations offset ++ (round15Operations offset ++ (round16Operations offset ++ (round17Operations offset ++ (round18Operations offset ++ (round19Operations offset ++ (round20Operations offset ++ (round21Operations offset ++ (round22Operations offset ++ (round23Operations offset ++ (round24Operations offset ++ (round25Operations offset ++ (round26Operations offset ++ (round27Operations offset ++ (round28Operations offset ++ (round29Operations offset ++ (round30Operations offset ++ (round31Operations offset ++ (round32Operations offset ++ (round33Operations offset ++ (round34Operations offset ++ (round35Operations offset ++ (round36Operations offset ++ (round37Operations offset ++ (round38Operations offset ++ (round39Operations offset ++ (round40Operations offset ++ (round41Operations offset ++ (round42Operations offset ++ (round43Operations offset ++ (round44Operations offset ++ (round45Operations offset ++ (round46Operations offset ++ (round47Operations offset ++ (round48Operations offset ++ (round49Operations offset ++ (round50Operations offset ++ (round51Operations offset ++ (round52Operations offset ++ (round53Operations offset ++ (round54Operations offset ++ (round55Operations offset ++ (round56Operations offset ++ (round57Operations offset ++ (round58Operations offset ++ (round59Operations offset ++ (round60Operations offset ++ (round61Operations offset ++ (round62Operations offset ++ (round63Operations offset ++ []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem roundsChecked (offset : Nat) :
    Checked id ((List.range 64).foldlM (fun value item => roundStep (scheduleOutput offset) item value) (initialOutput offset))
      (expand63After offset) (round63Output offset) (round63After offset) (roundsOperations offset) := by
  apply checked_foldlM
  unfold roundsOperations
  refine .cons (round0Checked offset) ?_
  refine .cons (round1Checked offset) ?_
  refine .cons (round2Checked offset) ?_
  refine .cons (round3Checked offset) ?_
  refine .cons (round4Checked offset) ?_
  refine .cons (round5Checked offset) ?_
  refine .cons (round6Checked offset) ?_
  refine .cons (round7Checked offset) ?_
  refine .cons (round8Checked offset) ?_
  refine .cons (round9Checked offset) ?_
  refine .cons (round10Checked offset) ?_
  refine .cons (round11Checked offset) ?_
  refine .cons (round12Checked offset) ?_
  refine .cons (round13Checked offset) ?_
  refine .cons (round14Checked offset) ?_
  refine .cons (round15Checked offset) ?_
  refine .cons (round16Checked offset) ?_
  refine .cons (round17Checked offset) ?_
  refine .cons (round18Checked offset) ?_
  refine .cons (round19Checked offset) ?_
  refine .cons (round20Checked offset) ?_
  refine .cons (round21Checked offset) ?_
  refine .cons (round22Checked offset) ?_
  refine .cons (round23Checked offset) ?_
  refine .cons (round24Checked offset) ?_
  refine .cons (round25Checked offset) ?_
  refine .cons (round26Checked offset) ?_
  refine .cons (round27Checked offset) ?_
  refine .cons (round28Checked offset) ?_
  refine .cons (round29Checked offset) ?_
  refine .cons (round30Checked offset) ?_
  refine .cons (round31Checked offset) ?_
  refine .cons (round32Checked offset) ?_
  refine .cons (round33Checked offset) ?_
  refine .cons (round34Checked offset) ?_
  refine .cons (round35Checked offset) ?_
  refine .cons (round36Checked offset) ?_
  refine .cons (round37Checked offset) ?_
  refine .cons (round38Checked offset) ?_
  refine .cons (round39Checked offset) ?_
  refine .cons (round40Checked offset) ?_
  refine .cons (round41Checked offset) ?_
  refine .cons (round42Checked offset) ?_
  refine .cons (round43Checked offset) ?_
  refine .cons (round44Checked offset) ?_
  refine .cons (round45Checked offset) ?_
  refine .cons (round46Checked offset) ?_
  refine .cons (round47Checked offset) ?_
  refine .cons (round48Checked offset) ?_
  refine .cons (round49Checked offset) ?_
  refine .cons (round50Checked offset) ?_
  refine .cons (round51Checked offset) ?_
  refine .cons (round52Checked offset) ?_
  refine .cons (round53Checked offset) ?_
  refine .cons (round54Checked offset) ?_
  refine .cons (round55Checked offset) ?_
  refine .cons (round56Checked offset) ?_
  refine .cons (round57Checked offset) ?_
  refine .cons (round58Checked offset) ?_
  refine .cons (round59Checked offset) ?_
  refine .cons (round60Checked offset) ?_
  refine .cons (round61Checked offset) ?_
  refine .cons (round62Checked offset) ?_
  refine .cons (round63Checked offset) ?_
  exact .nil _ _

def serializedOperations (offset : Nat) : Operations F :=
  (serialize0Operations offset ++ (serialize1Operations offset ++ (serialize2Operations offset ++ (serialize3Operations offset ++ (serialize4Operations offset ++ (serialize5Operations offset ++ (serialize6Operations offset ++ (serialize7Operations offset ++ []))))))))

theorem serializedChecked (offset : Nat) :
    Checked id ((feedforwardOutput offset).toList.foldlM (fun value item => serializeStep item value) #[])
      (feedforwardAfter offset) (serialize7Output offset) (serialize7After offset) (serializedOperations offset) := by
  apply checked_foldlM
  unfold serializedOperations
  refine .cons (serialize0Checked offset) ?_
  refine .cons (serialize1Checked offset) ?_
  refine .cons (serialize2Checked offset) ?_
  refine .cons (serialize3Checked offset) ?_
  refine .cons (serialize4Checked offset) ?_
  refine .cons (serialize5Checked offset) ?_
  refine .cons (serialize6Checked offset) ?_
  refine .cons (serialize7Checked offset) ?_
  exact .nil _ _

def bodyOperations (offset : Nat) : Operations F :=
  inputOperations offset ++ (initialOperations offset ++ (paddingOperations offset ++
    (packingOperations offset ++ (scheduledOperations offset ++ (roundsOperations offset ++
      (feedforwardOperations offset ++ serializedOperations offset))))))

theorem bodyChecked (offset : Nat) :
    Checked id (WitnessCircuit.body Preimage.privatePrograms) (beginCursor offset)
      (serialize7Output offset) (serialize7After offset) (bodyOperations offset) := by
  rw [source_body]
  unfold program bodyOperations
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (inputChecked offset) ?_
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (initialChecked offset) ?_
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (paddingChecked offset) ?_
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (packingChecked offset) ?_
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (scheduledChecked offset) ?_
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (roundsChecked offset) ?_
  refine checked_bind _ _ _ _ _ _ _ _ _ _ (feedforwardChecked offset) ?_
  exact serializedChecked offset

private theorem run_of_checked {α : Type} (action : Build α) (before : Cursor)
    (output : α) (after : Cursor) (ops : Operations F)
    (checked : Checked id action before output after ops) :
    action before.1 before.2 = ((output,after.1),(ops,after.2)) := by
  have exactRun := checked []
  change (action before.1 before.2).1.1 = output ∧
    ((action before.1 before.2).1.2,(action before.1 before.2).2.2) = after ∧
    (action before.1 before.2).2.1 = ops at exactRun
  have cache : (action before.1 before.2).1.2 = after.1 :=
    congrArg (fun position : Cursor => position.1) exactRun.2.1
  have next : (action before.1 before.2).2.2 = after.2 :=
    congrArg (fun position : Cursor => position.2) exactRun.2.1
  exact Prod.ext (Prod.ext exactRun.1 cache) (Prod.ext exactRun.2.2 next)

theorem body_run (offset : Nat) :
    WitnessCircuit.body Preimage.privatePrograms [] offset =
      ((serialize7Output offset,(serialize7After offset).1),
       (bodyOperations offset,(serialize7After offset).2)) :=
  run_of_checked _ _ _ _ _ (bodyChecked offset)

theorem synthesize_run (offset : Nat) :
    WitnessCircuit.synthesize Preimage.privatePrograms offset =
      (serialize7Output offset,bodyOperations offset,(serialize7After offset).2) := by
  unfold WitnessCircuit.synthesize
  change (let result := WitnessCircuit.body Preimage.privatePrograms [] offset
    (result.1.1,result.2.1 ++ [],result.2.2)) = _
  rw [body_run]
  simp only [List.append_nil]

theorem synthesize_operations (offset : Nat) :
    (WitnessCircuit.synthesize Preimage.privatePrograms).operations offset = bodyOperations offset := by
  unfold Circuit.operations
  rw [synthesize_run]

theorem synthesize_output (offset : Nat) :
    (WitnessCircuit.synthesize Preimage.privatePrograms).output offset = serialize7Output offset := by
  unfold Circuit.output
  rw [synthesize_run]

theorem synthesize_next (offset : Nat) :
    (WitnessCircuit.synthesize Preimage.privatePrograms).nextRegionIndex offset =
      (serialize7After offset).2 := by
  unfold Circuit.nextRegionIndex
  rw [synthesize_run]

set_option maxRecDepth 10000 in
theorem public_operations (offset : Nat) :
    publicOperations offset =
      (Preimage.expose (serialize7Output offset)).operations (serialize7After offset).2 := by
  cbv

theorem tables_operations (offset : Nat) :
    Preimage.tables.operations offset = Preimage.tables.operations 0 := rfl

def preimageOperations (offset : Nat) : Operations F :=
  bodyOperations offset ++ (publicOperations offset ++ Preimage.tables.operations 0)

/-- The original complete circuit, including its actual public copies and five
loaded tables, equals the concatenation of the checked source stages. -/
theorem preimage_operations (offset : Nat) :
    (WitnessCircuit.preimageCircuit Preimage.privatePrograms).operations offset =
      preimageOperations offset := by
  rw [Preimage.preimage_source,Circuit.operations_bind,synthesize_operations,
    synthesize_output,synthesize_next]
  unfold Preimage.finish preimageOperations
  simp only [Circuit.operations_bind,Circuit.operations_pure,List.append_nil,Preimage.expose_next]
  rw [← public_operations,tables_operations]

end Midnight.SHA256.Semantics.WitnessCheckpoints
