module

public import Clean.Utils.ResourceHistory.Grounding
public import Clean.Utils.ResourceHistory.Inventory
public import Clean.Utils.ResourceHistory.Refresh
public import Clean.Utils.ResourceHistory.OfflineMemory
public import Clean.Air.LedgerView
public import Clean.Air.Realizes

/-! Regression proofs for the semantic obligations of mutable resource histories. -/

@[expose] public section

namespace ResourceHistoryTests

open Utils.ResourceHistory

/-- A disconnected component survives plain balance. -/
example : Ranked.EndpointBalanced (↑[(0, 1), (2, 3), (3, 2)] : Multiset (ℕ × ℕ)) id 0 1 := by
  unfold Ranked.EndpointBalanced
  decide

/-- It cannot satisfy the stronger chronology premise. -/
example : ¬ ∀ e ∈ [(0, 1), (2, 3), (3, 2)], e.1 < e.2 := by
  intro h
  have := h (3, 2) (by simp)
  omega

/-- Equal endpoints permit exactly the empty ranked history. -/
example (edges : Multiset (ℕ × ℕ)) (n : ℕ)
    (balanced : Ranked.EndpointBalanced edges id n n)
    (strict : ∀ e ∈ edges, e.1 < e.2) : edges = 0 :=
  Ranked.eq_zero_of_endpointBalanced_self edges id id strict balanced

abbrev Record := ℕ × ℕ × ℕ -- key, version, value
abbrev Access := ResourceAccess Record ℕ Bool -- write intent is explicit

private def key (record : Record) := record.1
private def edge (access : Access) := (access.before, access.after)
private abbrev older (a b : Record) := a.2.1 < b.2.1

private def store : Access := ⟨(0, 0, 0), (0, 1, 7), 0, 0, true⟩
private def readBack : Access := ⟨(0, 1, 7), (0, 2, 7), 0, 1, false⟩
private def storeAgain : Access := ⟨(0, 2, 7), (0, 3, 9), 0, 2, true⟩
private def initial : ResourceFrontier ℕ Record := fun k =>
  if k = 0 then some (0, 0, 0) else none
private def final : ResourceFrontier ℕ Record := fun k =>
  if k = 0 then some (0, 3, 9) else none

/-- One event can write, read its result, and write again at the same key. -/
private theorem repeated_accesses : ResourceReplay key edge initial [store, readBack, storeAgain] final := by
  apply replay_of_balance key edge older (fun _ => Nat.lt_irrefl _) (fun {_ _ _} ab bc => Nat.lt_trans ab bc) _ _ _
  · apply frontierBalance_of_inventory key edge _ _ _ {(0, 0, 0)} {(0, 3, 9)}
    · decide
    · intro k
      by_cases h : k = 0
      · subst k
        decide
      · simp only [initial, h, ↓reduceIte, optionalRecord, Option.toList_none, Multiset.coe_nil]
        apply Multiset.filter_eq_nil.mpr
        intro record member
        have same := Multiset.mem_singleton.mp member
        subst record
        exact Ne.symm h
    · intro k
      by_cases h : k = 0
      · subst k
        decide
      · simp only [final, h, ↓reduceIte, optionalRecord, Option.toList_none, Multiset.coe_nil]
        apply Multiset.filter_eq_nil.mpr
        intro record member
        have same := Multiset.mem_singleton.mp member
        subst record
        exact Ne.symm h
    · intro row member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> rfl
  · intro row member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro k
    by_cases h : k = 0
    · subst k
      decide
    · simp [accessesAt, store, readBack, storeAgain, key, edge, Ne.symm h]

/-- Unrepresented keys remain absent; a frontier hole is not an allocation token. -/
example : initial 42 = final 42 :=
  repeated_accesses.frame key edge 42 (by
    intro row member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide)

/-- A stale read following the store fails the sequential semantics. -/
example : ¬ ResourceReplay key edge initial
    [store, ⟨(0, 0, 0), (0, 2, 0), 0, 1, false⟩] final := by
  simp [ResourceReplay, initial, store, key, edge, Function.update_self]

/-- A balanced history still fails if execution reverses its accesses. -/
example : ¬ ResourceReplay key edge initial [readBack, store, storeAgain] final := by
  simp [ResourceReplay, initial, readBack, key, edge]

/-- Same-value writes retain their intent; value equality cannot authorize them as reads. -/
example : (ResourceAccess.mk (0, 1, 7) (0, 2, 7) 0 0 true : Access).intent = true := rfl

/-- Splitting an event bundle preserves the exact intermediate frontier. -/
example : ∃ middle, ResourceReplay key edge initial [store] middle ∧
    ResourceReplay key edge middle [readBack, storeAgain] final :=
  (ResourceReplay.append_iff key edge [store] [readBack, storeAgain] initial final).mp repeated_accesses

/-- Different keys may share the same version. -/
example : ResourceReplay Prod.fst id (fun k : ℕ => some (k, 0))
    [((0, 0), (0, 1)), ((1, 0), (1, 1))]
    (Function.update (Function.update (fun k => some (k, 0)) 0 (some (0, 1))) 1 (some (1, 1))) := by
  simp [ResourceReplay, Function.update_of_ne]

/-- Rewriting a refresh preserves the full observation, including the resource key. -/
example : Refresh.EdgeRewrite (fun r : Record => (r.1, r.2.2)) (fun r => r.2.1)
    ((0, 9, 7), (0, 10, 8)) ((0, 1, 7), (0, 10, 8)) := by
  unfold Refresh.EdgeRewrite
  decide

/-- State normalization can erase an administrative step before ranking the real events. -/
example : Ranked.EndpointBalanced (↑[((0, true), (1, true))] : Multiset ((ℕ × Bool) × (ℕ × Bool)))
    (fun e => (e.1.1, e.2.1)) 0 1 := by
  exact balance_filter_project
    (↑[((0, false), (0, true)), ((0, true), (1, true))] : Multiset ((ℕ × Bool) × (ℕ × Bool)))
    id Prod.fst (fun e => decide (e.1.1 ≠ e.2.1)) (0, false) (1, true)
    (by unfold Ranked.EndpointBalanced; decide) (by decide)

/-- The existing offline checker and the new resource semantics agree on a store/read log. -/
example : ResourceReplay Prod.fst OfflineMemory.edge (fun address => some (address, 0))
    [(1, 0, 0, 7), (2, 0, 7, 7)]
    (OfflineMemory.frontier [(2, 0, 7, 7), (1, 0, 0, 7)] (by simp [MemoryAccessList.isTimestampSorted, timestamp_ordering])) := by
  apply (OfflineMemory.online_iff_replay [(2, 0, 7, 7), (1, 0, 0, 7)] _).mp
  simp [MemoryAccessList.isConsistentOnline, MemoryAccessList.lastWriteValue]

open Air.Flat

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def channel : Channel (ZMod 7) field where
  name := "resource-history-regression"
  Guarantees _ _ := True

/-- Zero multiplicities still occupy physical capacity. -/
example : ¬ BalancedInteractions
    (List.replicate 7 (channel.pushedIfValue 0 0)) := by
  intro balanced
  have bound := balanced.1
  norm_num [ZMod.ringChar_zmod_n] at bound

/-- Field cancellation alone does not give exact natural occurrence counts. -/
example : ∀ message, balanceOf (List.replicate 7 (channel.pushedValue 0)) message = 0 := by
  intro message
  by_cases same : (channel.pushedValue 0).msg = message
  · simp [balanceOf, same]
    decide
  · simp [balanceOf, same]

/-- Typed balance retains duplicate occurrences instead of deduplicating a ledger. -/
example : BalancedInteractions
    ([0, 0].map channel.pushedValue ++ [0, 0].map channel.pulledValue) :=
  (channel.balanced_unit_iff [0, 0] [0, 0]).mpr ⟨by norm_num [ZMod.ringChar_zmod_n], .refl _⟩

/-- A disabled physical entry contributes no logical record. -/
example : LedgerEntry.produced (F := ZMod 7) (Message := field) [⟨.produce, false, (0 : ZMod 7)⟩] = [] := rfl

end ResourceHistoryTests
