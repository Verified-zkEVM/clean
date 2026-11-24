import Midnight.SHA256.WitnessCheckpoint

/-! Small exact computation contracts used by generated source checkpoints.
The operation list is always obtained from the actual action. Generated output
metadata becomes usable only after a kernel proof of `Returns`. -/
namespace Midnight.SHA256.Semantics.WitnessCheckpointModel
open Halo2 WitnessCircuit WitnessCheckpoint

def Returns {α : Type} (action : Build α) (before : Cursor) (output : α)
    (after : Cursor) : Prop :=
  (action before.1 before.2).1 = (output, after.1) ∧
    (action before.1 before.2).2.2 = after.2

def operations {α : Type} (action : Build α) (before : Cursor) : Operations F :=
  (action before.1 before.2).2.1

theorem checked {α : Type} (action : Build α) (before : Cursor) (output : α)
    (after : Cursor) (returns : Returns action before output after) :
    Checked id action before output after (operations action before) := by
  intro prior
  change (action before.1 before.2).1.1 = output ∧
    ((action before.1 before.2).1.2, (action before.1 before.2).2.2) = after ∧
    prior ++ (action before.1 before.2).2.1 = prior ++ operations action before
  obtain ⟨result, next⟩ := returns
  refine ⟨congrArg Prod.fst result, ?_, rfl⟩
  rw [congrArg Prod.snd result, next]

end Midnight.SHA256.Semantics.WitnessCheckpointModel
