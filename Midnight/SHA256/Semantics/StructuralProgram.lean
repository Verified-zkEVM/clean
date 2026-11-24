import Midnight.SHA256.Synthesis
import Midnight.Math.Checkpoint

/-! An exact named decomposition of the original source schedule. These names
only expose source loop boundaries for composing bounded reduction proofs. -/
namespace Midnight.SHA256.Semantics.StructuralProgram
open Halo2 Synthesis

variable {α β : Type}

theorem forIn_yield_fold (items : List α) (initial : β) (step : α → β → Build β) :
    (forIn items initial fun item value => do return .yield (← step item value)) =
      items.foldlM (fun value item => step item value) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.forIn_cons, List.foldlM_cons, bind_assoc, pure_bind]
    congr 1
    funext next
    exact ih next

def prepareStep (block : Array Cell) (index : Nat) (words : Array Word) : Build (Array Word) := do
  let word ← prepareMessage #[block[index]!]
  return words.push word

def expandStep (index : Nat) (words : Array Word) : Build (Array Word) := do
  let s0 ← sigma0 words[index-15]!
  let s1 ← sigma1 words[index-2]!
  let word ← prepareMessage #[words[index-16]!.combined.plain, words[index-7]!.combined.plain, s0, s1]
  return words.push word

def schedule (block : Array Cell) : Build (Array Cell) := do
  let initial ← (List.range 16).foldlM (fun words index => prepareStep block index words) #[]
  let words ← (List.range' 16 48).foldlM (fun words index => expandStep index words) initial
  return words.map (·.combined.plain)

theorem schedule_eq (block : Array Cell) : messageSchedule block = schedule block := by
  unfold messageSchedule schedule prepareStep expandStep
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  simp_rw [← forIn_yield_fold]
  simp only [bind_assoc, pure_bind]
  rfl

def roundStep (words : Array Cell) (index : Nat) (state : Compression) : Build Compression :=
  compressionRound state roundConstants[index]! words[index]!

def serializeStep (word : Cell) (outputs : Array Cell) : Build (Array Cell) := do
  return outputs ++ (← wordToBytes word)

def expose (outputs : Array Cell) : Build Unit := do
  for i in [:outputs.size] do
    modify fun state => { state with steps := state.steps.push (.publicInput outputs[i]! i) }

def program : Build Unit := do
  let bytes ← assignBytes
  let initial ← initialState
  let padded ← pad bytes
  let block ← blockFromBytes padded
  let words ← schedule block
  let state ← (List.range 64).foldlM (fun state index => roundStep words index state) initial
  let digest ← addStates initial state
  let outputs ← digest.toList.foldlM (fun output word => serializeStep word output) #[]
  expose outputs

theorem source_eq : synthesize = program := by
  unfold synthesize program
  simp only [schedule_eq]
  unfold roundStep serializeStep expose
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  simp_rw [← forIn_yield_fold]
  simp only [Array.forIn_toList, bind_assoc, pure_bind]
  rfl

end Midnight.SHA256.Semantics.StructuralProgram
