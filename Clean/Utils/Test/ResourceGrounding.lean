module

public import Clean.Utils.ResourceHistory.Grounding

/-! A semantic refinement regression: one event owns a read followed by a write.
The independent accumulator machine has no versions or resource records in its state.
-/

@[expose] public section

namespace ResourceGroundingTests

open Utils.ResourceHistory

private abbrev State := ℕ × ℕ -- program counter and accumulator
private abbrev Record := ℕ × ℕ -- version and value
private abbrev Row := ℕ × ℕ × ℕ -- program counter, claimed old value, increment

private def step (state : State) (increment : ℕ) (next : State) : Prop :=
  next = (state.1 + 1, state.2 + increment)

private def trace (initial : State) (events : List ℕ) (final : State) : Prop :=
  events.foldl (fun state increment => (state.1 + 1, state.2 + increment)) initial = final

private def control (row : Row) := (row.1, row.1 + 1)
private def event (row : Row) := row.2.2
private def accesses (row : Row) : List (Record × Record) :=
  [((2 * row.1, row.2.1), (2 * row.1 + 1, row.2.1)),
   ((2 * row.1 + 1, row.2.1), (2 * row.1 + 2, row.2.1 + row.2.2))]

private def stateTruth (pc : ℕ) (state : State) : Prop := pc = state.1
private def represents (frontier : ResourceFrontier Unit Record) (state : State) : Prop :=
  ∃ version, frontier () = some (version, state.2)

/-- Authentic current records turn the row's claimed value into the machine's actual value. -/
private theorem refinement : EventRefinement (fun _ : Record => ()) id control accesses event step
    (fun _ => True) stateTruth represents where
  localStep row _ initial final state pc represented replay := by
    obtain ⟨version, represented⟩ := represented
    have current : initial () = some (2 * row.1, row.2.1) := replay.1
    have same := Option.some.inj (represented.symm.trans current)
    have value : state.2 = row.2.1 := congrArg Prod.snd same
    refine ⟨(state.1 + 1, state.2 + row.2.2), rfl, ?_, ?_⟩
    · change row.1 + 1 = state.1 + 1
      exact congrArg (· + 1) pc
    · refine ⟨2 * row.1 + 2, ?_⟩
      rw [replay.final_eq_fold (fun _ => ()) id]
      simp [accesses, value]

/-- The shared-history theorem grounds a multi-access event in an independent trace. -/
example : ∃ result, trace (0, 5) [7] result ∧
    stateTruth 1 result ∧ represents (fun _ => some (2, 12)) result := by
  apply ground (fun _ : Record => ()) id control accesses event step (fun _ => True)
    stateTruth represents refinement trace (fun _ => rfl)
    (fun state next final increment events first suffix => by
      change next = (state.1 + 1, state.2 + increment) at first
      subst next
      exact suffix)
    [(0, 5, 7)] 0 1 (fun _ => some (0, 5)) (fun _ => some (2, 12)) (0, 5)
  · exact ⟨rfl, rfl⟩
  · simp [accesses, ResourceReplay, Function.update]
    funext key
    cases key
    rfl
  · intros; trivial
  · rfl
  · exact ⟨0, rfl⟩

/-- A forged claimed old value cannot be grounded, even when the local addition is correct. -/
example : ¬ ResourceReplay (fun _ : Record => ()) id (fun _ => some (0, 5))
    (accesses (0, 99, 7)) (fun _ => some (2, 106)) := by
  simp [accesses, ResourceReplay]

end ResourceGroundingTests
