import Midnight.SHA256.Semantics.ScheduleGadgets
import Midnight.SHA256.Semantics.ScheduleSpec

/-! The exact source message-schedule loops, with word representations and
honest witness completeness maintained through all 64 entries. -/
namespace Midnight.SHA256.Semantics.Schedule
open Halo2 WitnessCircuit WitnessBuild Initialize PrepareCircuit Linear ScheduleGadgets

attribute [local irreducible] WitnessCircuit.prepareMessage WitnessCircuit.sigma0 WitnessCircuit.sigma1
  ScheduleGadgets.appendInput ScheduleGadgets.appendExpanded

def inputValues (env : Placed Environment F) (block : Array (AssignedCell F)) (items : List Nat) : Array Nat :=
  items.toArray.map fun i => cellValue env.place env.env block[i]!

theorem inputValues_append_one (env : Placed Environment F) (block : Array (AssignedCell F))
    (items : List Nat) (i : Nat) (initial : Array Nat) :
    initial ++ inputValues env block (items ++ [i]) =
      (initial ++ inputValues env block items).push (cellValue env.place env.env block[i]!) := by
  apply Array.ext'
  simp [inputValues]

def initLoop (block : Array (AssignedCell F)) (items : List Nat) (initial : Array Word) : Build (Array Word) :=
  forIn items initial fun i words => do return .yield (← appendInput block i words)

def expandLoop (items : List Nat) (initial : Array Word) : Build (Array Word) :=
  forIn items initial fun i words => do return .yield (← appendExpanded i words)

theorem initLoop_lawful (block : Array (AssignedCell F)) (items : List Nat) (initial : Array Word) :
    Lawful (initLoop block items initial) :=
  lawful_forIn_list items initial _ (fun i _ words =>
    lawful_bind (appendInput_lawful block i words) (fun _ => lawful_pure _))

theorem expandLoop_lawful (items : List Nat) (initial : Array Word) :
    Lawful (expandLoop items initial) :=
  lawful_forIn_list items initial _ (fun i _ words =>
    lawful_bind (appendExpanded_lawful i words) (fun _ => lawful_pure _))

theorem source_loops (block : Array (AssignedCell F)) :
    messageSchedule block = (do
      let words ← initLoop block (List.range 16) #[]
      let words ← expandLoop (List.range' 16 48) words
      return words.map (·.combined.plain)) := by
  unfold messageSchedule initLoop expandLoop appendInput appendExpanded
  simp only [WitnessBuild.bind_assoc, WitnessBuild.pure_bind,
    Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem messageSchedule_lawful (block : Array (AssignedCell F)) : Lawful (messageSchedule block) := by
  rw [source_loops]
  exact lawful_bind (initLoop_lawful _ _ _) fun words =>
    lawful_bind (expandLoop_lawful _ words) fun _ => lawful_pure _

theorem initLoop_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (block : Array (AssignedCell F)) (items : List Nat)
    (inputs : ∀ i ∈ items, cellValue env.place env.env block[i]! < 2^32)
    (initial : Array Word) (values : Array Nat) (rep : WordsRep env initial values) :
    Sound env (initLoop block items initial)
      (fun output => WordsRep env output (values ++ inputValues env block items)) := by
  intro cache self valid satisfied
  apply forIn_list_prefix items initial (appendInput block) []
    (fun processed words nextCache _ => WordsRep env words (values ++ inputValues env block processed) ∧
      CacheMeaning env nextCache) env.place env.env
    (fun i _ words => appendInput_lawful block i words) ?_ cache self ?_ satisfied
  · intro processed i remaining split words nextCache nextIndex previous constraints
    have member : i ∈ items := by rw [split]; simp
    have result := appendInput_sound env table block i words _ previous.1 _
      ⟨inputs i member, rfl⟩ nextCache nextIndex previous.2 constraints
    simpa only [List.nil_append, inputValues_append_one, Placed.toEnvironment] using result
  · simpa [inputValues] using And.intro rep valid

theorem initLoop_complete (env : Placed ProverEnvironment F) (table : Gates.SpreadTable env.env.toEnvironment)
    (block : Array (AssignedCell F)) (items : List Nat)
    (inputs : ∀ i ∈ items, cellValue env.place env.env.toEnvironment block[i]! < 2^32)
    (initial : Array Word) (values : Array Nat) (rep : WordsRep env.toEnvironment initial values) :
    RoundGadgets.Complete env (initLoop block items initial)
      (fun output => WordsRep env.toEnvironment output (values ++ inputValues env.toEnvironment block items)) := by
  intro cache self valid witnesses
  apply forIn_list_prefix_complete items initial (appendInput block) []
    (fun processed words nextCache _ => WordsRep env.toEnvironment words
      (values ++ inputValues env.toEnvironment block processed) ∧ CacheMeaning env.toEnvironment nextCache)
    env.place env.env (fun i _ words => appendInput_lawful block i words) ?_
    cache self ?_ witnesses
  · intro processed i remaining split words nextCache nextIndex previous programs
    have member : i ∈ items := by rw [split]; simp
    have result := appendInput_honest env table block i words _ previous.1 _
      ⟨inputs i member, rfl⟩ nextCache nextIndex previous.2 programs
    simpa only [List.nil_append, inputValues_append_one, Placed.toEnvironment] using result
  · simpa [inputValues] using And.intro rep valid

/-- The actual next loop index is determined by its already-processed prefix. -/
theorem range_prefix_index (start count : Nat) (processed : List Nat) (i : Nat) (remaining : List Nat)
    (split : List.range' start count = processed ++ i :: remaining) : i = start + processed.length := by
  have sizes := congrArg List.length split
  have bound : processed.length < count := by
    simp only [List.length_range', List.length_append, List.length_cons] at sizes
    omega
  have index := congrArg (fun xs : List Nat => xs[processed.length]?) split
  rw [List.getElem?_range' bound, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero] at index
  simpa only [Nat.one_mul, Option.some.injEq] using index.symm

def fold (items : List Nat) (values : Array Nat) : Array Nat :=
  items.foldl (fun values i => ScheduleSpec.step i values) values

theorem fold_append_one (items : List Nat) (values : Array Nat) (i : Nat) :
    fold (items ++ [i]) values = ScheduleSpec.step i (fold items values) := by
  simp only [fold, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem expandLoop_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (start count : Nat) (lower : 16 ≤ start) (initial : Array Word) (values : Array Nat)
    (rep : WordsRep env initial values) (size : values.size = start) :
    Sound env (expandLoop (List.range' start count) initial)
      (fun output => WordsRep env output (fold (List.range' start count) values)) := by
  intro cache self valid satisfied
  apply forIn_list_prefix (List.range' start count) initial appendExpanded []
    (fun processed words nextCache _ => WordsRep env words (fold processed values) ∧ CacheMeaning env nextCache)
    env.place env.env (fun i _ words => appendExpanded_lawful i words) ?_ cache self ?_ satisfied
  · intro processed i remaining split words nextCache nextIndex previous constraints
    have index := range_prefix_index start count processed i remaining split
    have currentSize : words.size = i := by
      rw [previous.1.1]
      change (fold processed values).size = i
      simp only [fold, ScheduleSpec.fold_size, size]
      exact index.symm
    have result := appendExpanded_sound env table i words _ previous.1 (by omega) currentSize
      nextCache nextIndex previous.2 constraints
    simpa only [List.nil_append, fold_append_one, ScheduleSpec.step, ScheduleSpec.next] using result
  · exact ⟨rep, valid⟩

theorem expandLoop_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (start count : Nat) (lower : 16 ≤ start) (initial : Array Word) (values : Array Nat)
    (rep : WordsRep env.toEnvironment initial values) (size : values.size = start) :
    RoundGadgets.Complete env (expandLoop (List.range' start count) initial)
      (fun output => WordsRep env.toEnvironment output (fold (List.range' start count) values)) := by
  intro cache self valid witnesses
  apply forIn_list_prefix_complete (List.range' start count) initial appendExpanded []
    (fun processed words nextCache _ => WordsRep env.toEnvironment words (fold processed values) ∧
      CacheMeaning env.toEnvironment nextCache) env.place env.env
    (fun i _ words => appendExpanded_lawful i words) ?_ cache self ?_ witnesses
  · intro processed i remaining split words nextCache nextIndex previous programs
    have index := range_prefix_index start count processed i remaining split
    have currentSize : words.size = i := by
      rw [previous.1.1]
      change (fold processed values).size = i
      simp only [fold, ScheduleSpec.fold_size, size]
      exact index.symm
    have result := appendExpanded_complete env table i words _ previous.1 (by omega) currentSize
      nextCache nextIndex previous.2 programs
    simpa only [List.nil_append, fold_append_one, ScheduleSpec.step, ScheduleSpec.next] using result
  · exact ⟨rep, valid⟩

theorem inputValues_range (env : Placed Environment F) (block : Array (AssignedCell F))
    (size : block.size = 16) :
    inputValues env block (List.range 16) = block.map (cellValue env.place env.env) := by
  have range : (List.range 16).toArray = Array.range 16 := by decide +kernel
  simp only [inputValues, range]
  apply Array.ext
  · simp only [Array.size_map, Array.size_range, size]
  · intro i hi hj
    have inBlock : i < block.size := by simpa only [Array.size_map] using hj
    simp only [Array.getElem_map, Array.getElem_range, getElem!_pos block i inBlock]

theorem block_indices (env : Placed Environment F) (block : Array (AssignedCell F))
    (blockValues : Vector Nat 16)
    (values : block.map (cellValue env.place env.env) = blockValues.toArray)
    (bounded : ∀ cell ∈ block, cellValue env.place env.env cell < 2^32) :
    ∀ i ∈ List.range 16, cellValue env.place env.env block[i]! < 2^32 := by
  have size : block.size = 16 := by
    have h := congrArg Array.size values
    simpa only [Array.size_map, Vector.size_toArray] using h
  intro i member
  have hi : i < block.size := by rw [size]; exact List.mem_range.mp member
  rw [getElem!_pos block i hi]
  exact bounded _ (Array.getElem_mem hi)

theorem init16_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (block : Array (AssignedCell F)) (blockValues : Vector Nat 16)
    (values : block.map (cellValue env.place env.env) = blockValues.toArray)
    (bounded : ∀ cell ∈ block, cellValue env.place env.env cell < 2^32) :
    Sound env (initLoop block (List.range 16) #[])
      (fun output => WordsRep env output blockValues.toArray) := by
  have size : block.size = 16 := by
    have h := congrArg Array.size values
    simpa only [Array.size_map, Vector.size_toArray] using h
  have empty : WordsRep env #[] #[] := ⟨rfl, by simp⟩
  have result := initLoop_sound env table block (List.range 16)
    (block_indices env block blockValues values bounded) #[] #[] empty
  simpa only [Array.empty_append, inputValues_range env block size, values] using result

theorem init16_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (block : Array (AssignedCell F)) (blockValues : Vector Nat 16)
    (values : block.map (cellValue env.place env.env.toEnvironment) = blockValues.toArray)
    (bounded : ∀ cell ∈ block, cellValue env.place env.env.toEnvironment cell < 2^32) :
    RoundGadgets.Complete env (initLoop block (List.range 16) #[])
      (fun output => WordsRep env.toEnvironment output blockValues.toArray) := by
  change block.map (cellValue env.toEnvironment.place env.toEnvironment.env) = blockValues.toArray at values
  have size : block.size = 16 := by
    have h := congrArg Array.size values
    simpa only [Array.size_map, Vector.size_toArray] using h
  have empty : WordsRep env.toEnvironment #[] #[] := ⟨rfl, by simp⟩
  have result := initLoop_complete env table block (List.range 16)
    (block_indices env.toEnvironment block blockValues values bounded) #[] #[] empty
  simpa only [Array.empty_append, inputValues_range env.toEnvironment block size, values] using result

/-- The final source map only projects existing plain cells; it introduces no
new witness assignment or semantic assumption. -/
theorem output_reference (env : Placed Environment F) (words : Array Word) (block : Vector Nat 16)
    (rep : WordsRep env words (fold (List.range' 16 48) block.toArray)) :
    (words.map (·.combined.plain)).map (cellValue env.place env.env) =
        (Specs.SHA256.messageSchedule block).toArray ∧
      ∀ cell ∈ words.map (·.combined.plain), cellValue env.place env.env cell < 2^32 := by
  constructor
  · have result := rep.plainValues
    have reference := ScheduleSpec.expand_eq_messageSchedule block
    change ScheduleSpec.expand block.toArray = _ at reference
    simpa only [Array.map_map, Function.comp_def] using result.trans reference
  · intro cell member
    obtain ⟨word, inWords, rfl⟩ := Array.mem_map.mp member
    obtain ⟨i, hi, eq⟩ := Array.getElem_of_mem inWords
    have plain := message_plain (env := env) (rep.2 i hi)
    have wordEq : words[i]! = word := by rw [getElem!_pos words i hi]; exact eq
    rw [wordEq] at plain
    rw [plain.2]
    exact plain.1

/-- All 64 actual source output cells represent Clean's SHA message schedule. -/
theorem messageSchedule_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (block : Array (AssignedCell F)) (blockValues : Vector Nat 16)
    (values : block.map (cellValue env.place env.env) = blockValues.toArray)
    (bounded : ∀ cell ∈ block, cellValue env.place env.env cell < 2^32) :
    Sound env (WitnessCircuit.messageSchedule block) (fun output =>
      output.map (cellValue env.place env.env) = (Specs.SHA256.messageSchedule blockValues).toArray ∧
        ∀ cell ∈ output, cellValue env.place env.env cell < 2^32) := by
  rw [source_loops]
  apply sound_bind (initLoop_lawful _ _ _) (init16_sound env table block blockValues values bounded)
  intro words represented
  apply sound_bind (expandLoop_lawful _ _)
    (expandLoop_sound env table 16 48 (by decide +kernel) words blockValues.toArray represented
      (Vector.size_toArray blockValues))
  intro output expanded
  apply sound_pure env (output.map (·.combined.plain))
  exact output_reference env output blockValues expanded

/-- Honest assignments from the original advice programs satisfy the complete
source schedule and produce its mathematically specified words. -/
theorem messageSchedule_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (block : Array (AssignedCell F)) (blockValues : Vector Nat 16)
    (values : block.map (cellValue env.place env.env.toEnvironment) = blockValues.toArray)
    (bounded : ∀ cell ∈ block, cellValue env.place env.env.toEnvironment cell < 2^32) :
    RoundGadgets.Complete env (WitnessCircuit.messageSchedule block) (fun output =>
      output.map (cellValue env.place env.env.toEnvironment) = (Specs.SHA256.messageSchedule blockValues).toArray ∧
        ∀ cell ∈ output, cellValue env.place env.env.toEnvironment cell < 2^32) := by
  rw [source_loops]
  apply RoundGadgets.complete_bind (initLoop_lawful _ _ _)
    (init16_complete env table block blockValues values bounded)
  intro words represented
  apply RoundGadgets.complete_bind (expandLoop_lawful _ _)
    (expandLoop_complete env table 16 48 (by decide +kernel) words blockValues.toArray represented
      (Vector.size_toArray blockValues))
  intro output expanded
  apply RoundGadgets.complete_pure env (output.map (·.combined.plain))
  exact output_reference env.toEnvironment output blockValues expanded

end Midnight.SHA256.Semantics.Schedule
