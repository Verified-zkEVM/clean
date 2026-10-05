module

public import Clean.Utils.ResourceHistory.Replay
public import Clean.Utils.OfflineMemory

/-! # The existing offline-memory model as resource replay

The older model lists accesses newest first and starts from zero memory. Its online
semantics is exactly `ResourceReplay` in chronological order. Versions are irrelevant
to this semantic equivalence; the offline sorting theorem is an alternative way to
establish it, rather than a requirement of resource replay.
-/

@[expose] public section

namespace Utils.ResourceHistory.OfflineMemory

def edge (access : MemoryAccess) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let (_, address, read, write) := access
  ((address, read), (address, write))

def frontier (accesses : MemoryAccessList) (sorted : accesses.isTimestampSorted) :
    ResourceFrontier ℕ (ℕ × ℕ) :=
  fun address => some (address, accesses.lastWriteValue sorted address)

theorem frontier_cons (t address read write : ℕ) (rest : MemoryAccessList)
    (sorted : MemoryAccessList.isTimestampSorted ((t, address, read, write) :: rest)) :
    frontier ((t, address, read, write) :: rest) sorted =
      Function.update (frontier rest (List.Pairwise.of_cons sorted)) address (some (address, write)) := by
  funext k
  by_cases same : k = address
  · subst k
    simp [frontier, MemoryAccessList.lastWriteValue]
  · simp [frontier, MemoryAccessList.lastWriteValue, Function.update_of_ne same, Ne.symm same]

theorem fold_eq_frontier (accesses : MemoryAccessList) (sorted : accesses.isTimestampSorted) :
    accesses.reverse.foldl (fun current row =>
      Function.update current (edge row).1.1 (some (edge row).2))
      (fun address => some (address, 0)) = frontier accesses sorted := by
  induction accesses with
  | nil => rfl
  | cons access rest ih =>
    rcases access with ⟨t, address, read, write⟩
    rw [List.reverse_cons, List.foldl_append, ih (List.Pairwise.of_cons sorted)]
    exact (frontier_cons t address read write rest sorted).symm

/-- Bridge the existing chronological memory semantics to the generic resource relation. -/
theorem online_iff_replay (accesses : MemoryAccessList) (sorted : accesses.isTimestampSorted) :
    accesses.isConsistentOnline sorted ↔
      ResourceReplay Prod.fst edge (fun address => some (address, 0))
        accesses.reverse (frontier accesses sorted) := by
  induction accesses with
  | nil => exact iff_of_true trivial rfl
  | cons access rest ih =>
    rcases access with ⟨t, address, read, write⟩
    rw [List.reverse_cons, ResourceReplay.append_iff]
    constructor
    · rintro ⟨current, consistent⟩
      refine ⟨frontier rest (List.Pairwise.of_cons sorted), (ih _).mp consistent, ?_⟩
      constructor
      · simp only [frontier, edge, current]
      · exact (frontier_cons t address read write rest sorted).symm
    · rintro ⟨middle, firstPart, last⟩
      have middleEq := firstPart.final_eq_fold Prod.fst edge
      rw [fold_eq_frontier rest (List.Pairwise.of_cons sorted)] at middleEq
      subst middle
      constructor
      · have current := last.1
        simp only [frontier, edge, Option.some.injEq, Prod.mk.injEq, true_and] at current
        exact current.symm
      · exact (ih _).mpr firstPart

/-- The address-sorted offline checker establishes the same generic replay semantics. -/
theorem offline_iff_replay (accesses : MemoryAccessList) (sorted : accesses.isTimestampSorted)
    (unique : accesses.Notimestampdup) :
    (∃ permuted : AddressSortedMemoryAccessList,
      permuted.val.Perm accesses ∧
        MemoryAccessList.isConsistentOffline permuted.val permuted.property) ↔
      ResourceReplay Prod.fst edge (fun address => some (address, 0))
        accesses.reverse (frontier accesses sorted) :=
  (MemoryAccessList.isConsistentOnline_iff_isConsistentOffline accesses sorted unique).symm.trans
    (online_iff_replay accesses sorted)

end Utils.ResourceHistory.OfflineMemory
