import Midnight.SHA256.Semantics.WitnessCheckpointModel
import Midnight.SHA256.WitnessBuild

/-! Exact named source loops for composing bounded witness-source checkpoints.
Every step remains the original witness-bearing circuit action. -/
namespace Midnight.SHA256.Semantics.WitnessCheckpointProgram
open Halo2 WitnessCircuit WitnessBuild WitnessCheckpoint

theorem forIn_yield_fold {α β : Type} (items : List α) (initial : β)
    (step : α → β → Build β) :
    (forIn items initial fun item value => do return .yield (← step item value)) =
      items.foldlM (fun value item => step item value) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [forIn_yield_cons, List.foldlM_cons]
    congr 1
    funext next
    exact ih next

theorem lift_foldlM {α β : Type} (items : List α) (initial : β)
    (step : α → β → Build β) :
    lift (items.foldlM (fun value item => step item value) initial) =
      items.foldlM (fun value item => lift (step item value)) initial := by
  induction items generalizing initial with
  | nil => exact lift_pure initial
  | cons item rest ih =>
    simp only [List.foldlM_cons, lift_bind, ih]

theorem checked_foldlM_observed {α β Observation : Type}
    (observe : Operations F → List Observation) (items : List α) (initial output : β)
    (step : α → β → Build β) (before after : Cursor) (chunk : List Observation)
    (chain : Midnight.Math.Checkpoint.Chain frame observe (fun item value => lift (step item value))
      items before initial after output chunk) :
    Checked observe (items.foldlM (fun value item => step item value) initial)
      before output after chunk := by
  unfold Checked
  rw [lift_foldlM]
  exact chain.checked _ _ _ _ _ _ _ _ _

theorem checked_foldlM {α β : Type} (items : List α) (initial output : β)
    (step : α → β → Build β) (before after : Cursor) (chunk : Operations F)
    (chain : Midnight.Math.Checkpoint.Chain frame id (fun item value => lift (step item value))
      items before initial after output chunk) :
    Checked id (items.foldlM (fun value item => step item value) initial)
      before output after chunk :=
  checked_foldlM_observed id items initial output step before after chunk chain

def prepareStep (block : Array WitnessCircuit.Cell) (index : Nat) (words : Array Word) :
    Build (Array Word) := do
  let word ← prepareMessage #[block[index]!]
  return words.push word

def expandStep (index : Nat) (words : Array Word) : Build (Array Word) := do
  let s0 ← sigma0 words[index-15]!
  let s1 ← sigma1 words[index-2]!
  let word ← prepareMessage #[words[index-16]!.combined.plain,
    words[index-7]!.combined.plain, s0, s1]
  return words.push word

def schedule (block : Array WitnessCircuit.Cell) : Build (Array WitnessCircuit.Cell) := do
  let initial ← (List.range 16).foldlM (fun words index => prepareStep block index words) #[]
  let words ← (List.range' 16 48).foldlM (fun words index => expandStep index words) initial
  return words.map (·.combined.plain)

theorem schedule_eq (block : Array WitnessCircuit.Cell) : messageSchedule block = schedule block := by
  unfold messageSchedule schedule prepareStep expandStep
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  simp_rw [← forIn_yield_fold]
  simp only [bind_assoc, pure_bind]
  rfl

def roundStep (words : Array WitnessCircuit.Cell) (index : Nat) (state : Compression) :
    Build Compression := compressionRound state Synthesis.roundConstants[index]! words[index]!

def serializeStep (word : WitnessCircuit.Cell) (outputs : Array WitnessCircuit.Cell) :
    Build (Array WitnessCircuit.Cell) := do
  return outputs ++ (← wordToBytes word)

def program (input : Vector (WitgenIR F 1) 24) : Build (Array WitnessCircuit.Cell) := do
  let bytes ← assignBytes input
  let initial ← initialState
  let padded ← pad bytes
  let block ← blockFromBytes padded
  let words ← schedule block
  let state ← (List.range 64).foldlM (fun state index => roundStep words index state) initial
  let digest ← addStates initial state
  digest.toList.foldlM (fun output word => serializeStep word output) #[]

theorem source_body (input : Vector (WitgenIR F 1) 24) : body input = program input := by
  unfold body program
  simp only [schedule_eq]
  unfold roundStep serializeStep
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  simp_rw [← forIn_yield_fold]
  simp only [Array.forIn_toList, bind_assoc, pure_bind, bind_pure]
  rfl

end Midnight.SHA256.Semantics.WitnessCheckpointProgram
