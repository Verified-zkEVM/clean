/-! Exact bounded reduction checkpoints for stateful source programs. The trace
observation is arbitrary: clients may retain full operations or only the
addresses relevant to a particular checker. Every checkpoint proves the actual
source return value and cursor as well as the observed appended trace. -/
namespace Midnight.Math.Checkpoint

structure Frame (State Cursor Trace : Type) where
  position : State → Cursor
  trace : State → Trace
  assemble : Cursor → Trace → State
  position_assemble : ∀ cursorValue traceValue, position (assemble cursorValue traceValue) = cursorValue
  trace_assemble : ∀ cursorValue traceValue, trace (assemble cursorValue traceValue) = traceValue
  reconstruct : ∀ state, assemble (position state) (trace state) = state

variable {State Cursor Trace Observation α β : Type}

theorem Frame.state_of_position_eq (frame : Frame State Cursor Trace)
    (state : State) (position : Cursor) (same : frame.position state = position) :
    state = frame.assemble position (frame.trace state) := by
  rw [← same]
  exact (frame.reconstruct state).symm

/-- This is an exact source computation contract, universally quantified over
its already accumulated trace. It does not accept an assumed source result. -/
def Checked (frame : Frame State Cursor Trace) (observe : Trace → List Observation)
    (action : StateM State α) (before : Cursor) (output : α) (after : Cursor)
    (chunk : List Observation) : Prop :=
  ∀ priorTrace, let result := action (frame.assemble before priorTrace)
    result.1 = output ∧ frame.position result.2 = after ∧
      observe (frame.trace result.2) = observe priorTrace ++ chunk

theorem Checked.pure (frame : Frame State Cursor Trace) (observe : Trace → List Observation)
    (before : Cursor) (output : α) :
    Checked frame observe (pure output) before output before [] := by
  intro priorTrace
  change output = output ∧ frame.position (frame.assemble before priorTrace) = before ∧
    observe (frame.trace (frame.assemble before priorTrace)) = observe priorTrace ++ []
  simp only [frame.position_assemble, frame.trace_assemble, List.append_nil, and_self]

theorem Checked.bind (frame : Frame State Cursor Trace) (observe : Trace → List Observation)
    (first : StateM State α) (next : α → StateM State β)
    (before middle after : Cursor) (left : α) (right : β) (chunk₁ chunk₂ : List Observation)
    (hfirst : Checked frame observe first before left middle chunk₁)
    (hnext : Checked frame observe (next left) middle right after chunk₂) :
    Checked frame observe (first >>= next) before right after (chunk₁ ++ chunk₂) := by
  intro priorTrace
  have a := hfirst priorTrace
  have state := frame.state_of_position_eq _ _ a.2.1
  have b := hnext (frame.trace (first (frame.assemble before priorTrace)).2)
  change (next (first (frame.assemble before priorTrace)).1 (first (frame.assemble before priorTrace)).2).1 = right ∧
    frame.position (next (first (frame.assemble before priorTrace)).1 (first (frame.assemble before priorTrace)).2).2 = after ∧
    observe (frame.trace (next (first (frame.assemble before priorTrace)).1
      (first (frame.assemble before priorTrace)).2).2) = observe priorTrace ++ (chunk₁ ++ chunk₂)
  rw [a.1, state]
  exact ⟨b.1, b.2.1, by rw [b.2.2, a.2.2, List.append_assoc]⟩

/-- Ordered bounded source steps. The expected result of each checked step is
exactly the input to the following step; no continuation state is assumed. -/
inductive Chain {Index : Type} (frame : Frame State Cursor Trace)
    (observe : Trace → List Observation) (step : Index → α → StateM State α) :
    List Index → Cursor → α → Cursor → α → List Observation → Prop where
  | nil (position : Cursor) (value : α) : Chain frame observe step [] position value position value []
  | cons {index items before middle after input intermediate output chunk rest}
      (head : Checked frame observe (step index input) before intermediate middle chunk)
      (tail : Chain frame observe step items middle intermediate after output rest) :
      Chain frame observe step (index :: items) before input after output (chunk ++ rest)

theorem Chain.checked {Index : Type} (frame : Frame State Cursor Trace)
    (observe : Trace → List Observation) (step : Index → α → StateM State α)
    (items : List Index) (before after : Cursor) (input output : α) (chunk : List Observation)
    (chain : Chain frame observe step items before input after output chunk) :
    Checked frame observe (items.foldlM (fun value index => step index value) input)
      before output after chunk := by
  induction chain with
  | nil position value => exact Checked.pure _ _ _ _
  | cons head tail ih =>
    rw [List.foldlM_cons]
    exact Checked.bind _ _ _ _ _ _ _ _ _ _ _ head ih

namespace Reduction
/-- Explicit function heads let the kernel-producing CBV simplifier normalize
symbolic trace prefixes without expanding them into stuck recursors. -/
theorem map_append {α β : Type} (f : α → β) (left right : List α) :
    List.map f (List.append left right) = List.append (List.map f left) (List.map f right) :=
  List.map_append
theorem nil_append {α : Type} (right : List α) :
    List.append ([] : List α) right = right := rfl
theorem cons_append {α : Type} (head : α) (left right : List α) :
    List.append (head :: left) right = head :: List.append left right := rfl
theorem append_nil {α : Type} (left : List α) : List.append left [] = left := List.append_nil left
theorem append_assoc {α : Type} (left middle right : List α) :
    List.append (List.append left middle) right = List.append left (List.append middle right) :=
  List.append_assoc left middle right
theorem concat_append {α : Type} (left : List α) (last : α) :
    List.concat left last = List.append left [last] := List.concat_eq_append
end Reduction

end Midnight.Math.Checkpoint
