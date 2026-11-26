import Midnight.SHA256.Semantics.Round
import Midnight.SHA256.Semantics.RoundsSpec

/-! Contracts for the actual 64-round source loop. The operational loop preserves
all source calls and the exact cache/index threading; the pure fold only names
its mathematical postcondition. -/
namespace Midnight.SHA256.Semantics.Rounds
open Halo2 WitnessCircuit WitnessBuild Initialize PrepareCircuit Linear

attribute [local irreducible] compressionRound Specs.SHA256.sha256Round
  Specs.SHA256.sha256Compress Synthesis.roundConstants

/-- A size-checked representation of all 64 source schedule cells. -/
def ScheduleRep (env : Placed Environment F) (cells : Array (AssignedCell F)) (words : Vector Nat 64) : Prop :=
  cells.size = 64 ∧ ∀ index, index < 64 → PlainRep env cells[index]! words.toArray[index]!

/-- A representation constructor for the schedule circuit's array-valued
postcondition. The array equality also proves there are exactly 64 cells. -/
theorem ScheduleRep.of_values (env : Placed Environment F) (cells : Array (AssignedCell F))
    (words : Vector Nat 64)
    (values : cells.map (cellValue env.place env.env) = words.toArray)
    (bounded : ∀ cell ∈ cells, cellValue env.place env.env cell < 2 ^ 32) :
    ScheduleRep env cells words := by
  have size : cells.size = 64 := by
    have h := congrArg Array.size values
    simpa only [Array.size_map, Vector.size_toArray] using h
  refine ⟨size, ?_⟩
  intro index bound
  have inCells : index < cells.size := by omega
  have inWords : index < words.toArray.size := by simpa using bound
  have eq := congrArg (fun data : Array Nat => data[index]!) values
  change (cells.map (cellValue env.place env.env))[index]! = words.toArray[index]! at eq
  rw [getElem!_pos (cells.map (cellValue env.place env.env)) index (by simpa using inCells),
    getElem!_pos words.toArray index inWords] at eq
  rw [getElem!_pos cells index inCells, getElem!_pos words.toArray index inWords]
  have value : cellValue env.place env.env cells[index] = words.toArray[index] := by
    simpa only [Array.getElem_map] using eq
  refine ⟨?_, value⟩
  rw [← value]
  exact bounded _ (Array.getElem_mem inCells)

/-- The exact source loop body, with a list exposing the iteration order. -/
def loop (words : Array (AssignedCell F)) (items : List Nat) (initial : Compression) : Build Compression :=
  forIn items initial fun index state => do
    return .yield (← compressionRound state Synthesis.roundConstants[index]! words[index]!)

/-- The let-mut/range loop occurring in `WitnessCircuit.body`, without replacing
any round call or witness program. -/
def source (words : Array (AssignedCell F)) (initial : Compression) : Build Compression := do
  let mut state := initial
  for i in [:64] do state ← compressionRound state Synthesis.roundConstants[i]! words[i]!
  return state

theorem source_loop (words : Array (AssignedCell F)) (initial : Compression) :
    source words initial = loop words (List.range 64) initial := by
  unfold source loop
  simp only [WitnessBuild.bind_pure, Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem loop_lawful (words : Array (AssignedCell F)) (items : List Nat) (initial : Compression) :
    Lawful (loop words items initial) :=
  lawful_forIn_list items initial _ (fun _ _ state =>
    lawful_bind (Round.compressionRound_lawful state _ _) (fun _ => lawful_pure _))

theorem source_lawful (words : Array (AssignedCell F)) (initial : Compression) :
    Lawful (source words initial) := by
  rw [source_loop]
  exact loop_lawful _ _ _

theorem loop_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (cells : Array (AssignedCell F)) (words : Vector Nat 64) (schedule : ScheduleRep env cells words)
    (items : List Nat) (indices : ∀ index ∈ items, index < 64)
    (initial : Compression) (state : Vector Nat 8) (rep : StateRep env initial state) :
    Sound env (loop cells items initial)
      (fun output => StateRep env output (RoundsSpec.fold words items state)) := by
  intro cache self cacheValid satisfied
  apply forIn_list_prefix items initial
    (fun index state => compressionRound state Synthesis.roundConstants[index]! cells[index]!) []
    (fun processed output nextCache _ =>
      StateRep env output (RoundsSpec.fold words processed state) ∧ CacheMeaning env nextCache)
    env.place env.env (fun _ _ out => Round.compressionRound_lawful out _ _) ?_
    cache self ?_ satisfied
  · intro processed index remaining split output nextCache nextIndex previous constraints
    have bound : index < 64 := indices index (by rw [split]; simp)
    have result := Round.compressionRound_sound env table output _ previous.1
      Synthesis.roundConstants[index]! (roundConstant_lt ⟨index, bound⟩)
      cells[index]! words.toArray[index]! (schedule.2 index bound)
      nextCache nextIndex previous.2 constraints
    simpa only [List.nil_append, RoundsSpec.fold_append_one, RoundsSpec.step] using result
  · exact ⟨rep, cacheValid⟩

theorem loop_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (cells : Array (AssignedCell F)) (words : Vector Nat 64) (schedule : ScheduleRep env.toEnvironment cells words)
    (items : List Nat) (indices : ∀ index ∈ items, index < 64)
    (initial : Compression) (state : Vector Nat 8) (rep : StateRep env.toEnvironment initial state)
    (cache : WitnessCircuit.Cache) (self : RegionIndex) (cacheValid : CacheMeaning env.toEnvironment cache)
    (witnesses : ExtendsWitnesses env.place env.env ((loop cells items initial cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((loop cells items initial cache).operations self) self ∧
      StateRep env.toEnvironment ((loop cells items initial cache).output self).1
        (RoundsSpec.fold words items state) ∧
      CacheMeaning env.toEnvironment ((loop cells items initial cache).output self).2 := by
  apply forIn_list_prefix_complete items initial
    (fun index state => compressionRound state Synthesis.roundConstants[index]! cells[index]!) []
    (fun processed output nextCache _ =>
      StateRep env.toEnvironment output (RoundsSpec.fold words processed state) ∧
      CacheMeaning env.toEnvironment nextCache)
    env.place env.env (fun _ _ out => Round.compressionRound_lawful out _ _) ?_
    cache self ?_ witnesses
  · intro processed index remaining split output nextCache nextIndex previous witness
    have bound : index < 64 := indices index (by rw [split]; simp)
    have result := Round.compressionRound_complete env table output _ previous.1
      Synthesis.roundConstants[index]! (roundConstant_lt ⟨index, bound⟩)
      cells[index]! words.toArray[index]! (schedule.2 index bound)
      nextCache nextIndex previous.2 witness
    simpa only [List.nil_append, RoundsSpec.fold_append_one, RoundsSpec.step] using result
  · exact ⟨rep, cacheValid⟩

attribute [local irreducible] source loop

/-- The 64 actual source rounds return Clean's compression state. This is the
state before the separate feed-forward addition performed by `addStates`. -/
theorem source_sound (env : Placed Environment F) (table : Gates.SpreadTable env.env)
    (cells : Array (AssignedCell F)) (words : Vector Nat 64) (schedule : ScheduleRep env cells words)
    (initial : Compression) (state : Vector Nat 8) (rep : StateRep env initial state) :
    Sound env (source cells initial)
      (fun output => StateRep env output (Specs.SHA256.sha256Compress state words)) := by
  rw [source_loop, ← RoundsSpec.fold_reference]
  exact loop_sound env table cells words schedule (List.range 64)
    (fun index member => List.mem_range.mp member) initial state rep

/-- Honest source witness execution satisfies every actual round constraint and
preserves the representation and constant cache across all 64 rounds. -/
theorem source_complete (env : Placed ProverEnvironment F)
    (table : Gates.SpreadTable env.env.toEnvironment)
    (cells : Array (AssignedCell F)) (words : Vector Nat 64) (schedule : ScheduleRep env.toEnvironment cells words)
    (initial : Compression) (state : Vector Nat 8) (rep : StateRep env.toEnvironment initial state)
    (cache : WitnessCircuit.Cache) (self : RegionIndex) (cacheValid : CacheMeaning env.toEnvironment cache)
    (witnesses : ExtendsWitnesses env.place env.env ((source cells initial cache).operations self) self) :
    Constraints env.place env.env.toEnvironment ((source cells initial cache).operations self) self ∧
      StateRep env.toEnvironment ((source cells initial cache).output self).1
        (Specs.SHA256.sha256Compress state words) ∧
      CacheMeaning env.toEnvironment ((source cells initial cache).output self).2 := by
  rw [source_loop] at witnesses ⊢
  rw [← RoundsSpec.fold_reference]
  exact loop_complete env table cells words schedule (List.range 64)
    (fun index member => List.mem_range.mp member) initial state rep cache self cacheValid witnesses

end Midnight.SHA256.Semantics.Rounds
