import Midnight.Math.Checkpoint
import Midnight.SHA256.WitnessCircuit

/-! Apply the shared exact-checkpoint contracts to the original witness-bearing
StateT circuit. The adapter only accumulates its emitted operations; it does not
reinterpret or replace witness programs. -/
namespace Midnight.SHA256.WitnessCheckpoint
open Halo2 Midnight.Math.Checkpoint

abbrev Cursor := WitnessCircuit.Cache × RegionIndex

structure State where
  cache : WitnessCircuit.Cache
  next : RegionIndex
  operations : Operations F

def frame : Frame State Cursor (Operations F) where
  position state := (state.cache,state.next)
  trace := State.operations
  assemble cursor ops := ⟨cursor.1,cursor.2,ops⟩
  position_assemble := by intro _ _; rfl
  trace_assemble := by intro _ _; rfl
  reconstruct := by intro state; rfl

def lift {α : Type} (action : WitnessCircuit.Build α) : StateM State α := fun state =>
  let result := action state.cache state.next
  (result.1.1, ⟨result.1.2,result.2.2,state.operations ++ result.2.1⟩)

theorem lift_pure {α : Type} (output : α) : lift (pure output) = pure output := by
  funext state
  simp only [lift]
  change (output,⟨state.cache,state.next,state.operations ++ []⟩) = (output,state)
  rw [List.append_nil]

theorem lift_bind {α β : Type} (first : WitnessCircuit.Build α)
    (next : α → WitnessCircuit.Build β) :
    lift (first >>= next) = (lift first >>= fun output => lift (next output)) := by
  funext state
  change (_,State.mk _ _ (state.operations ++ (_ ++ _))) =
    (_,State.mk _ _ ((state.operations ++ _) ++ _))
  rw [List.append_assoc]
  rfl

abbrev Checked {α Observation : Type} (observe : Operations F → List Observation)
    (action : WitnessCircuit.Build α) (before : Cursor) (output : α) (after : Cursor)
    (chunk : List Observation) := Midnight.Math.Checkpoint.Checked frame observe (lift action) before output after chunk

theorem checked_pure {α Observation : Type} (observe : Operations F → List Observation)
    (before : Cursor) (output : α) : Checked observe (pure output) before output before [] := by
  unfold Checked
  rw [lift_pure]
  exact Midnight.Math.Checkpoint.Checked.pure frame observe before output

theorem checked_bind {α β Observation : Type} (observe : Operations F → List Observation)
    (first : WitnessCircuit.Build α) (next : α → WitnessCircuit.Build β)
    (before middle after : Cursor) (left : α) (right : β) (chunk₁ chunk₂ : List Observation)
    (hfirst : Checked observe first before left middle chunk₁)
    (hnext : Checked observe (next left) middle right after chunk₂) :
    Checked observe (first >>= next) before right after (chunk₁ ++ chunk₂) := by
  unfold Checked
  rw [lift_bind]
  exact Midnight.Math.Checkpoint.Checked.bind frame observe (lift first)
    (fun output => lift (next output)) before middle after left right chunk₁ chunk₂ hfirst hnext

end Midnight.SHA256.WitnessCheckpoint
