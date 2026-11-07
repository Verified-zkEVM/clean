module

public import Clean

/-! Consumer regressions for complete frontiers and administrative refresh elimination.
Keys include an address space as well as an address. Initial records have nonzero versions
and values, and the complete boundary retains a participating resource with no accesses.
Ordinary umbrella imports also check that these APIs are publicly available to consumers.
-/

@[expose] public section

namespace ResourceFrontierTests

open Utils.ResourceHistory

private abbrev Key := ℕ × Bool
private abbrev Record := Key × ℕ × ℕ
private abbrev Edge := Record × Record

private def initial : ResourceFrontier Key Record := fun k =>
  if k = (7, false) then some ((7, false), 11, 40)
  else if k = (7, true) then some ((7, true), 11, 90)
  else if k = (9, false) then some ((9, false), 5, 77)
  else none

private def final : ResourceFrontier Key Record := fun k =>
  if k = (7, false) then some ((7, false), 13, 42)
  else if k = (7, true) then some ((7, true), 12, 93)
  else if k = (9, false) then some ((9, false), 5, 77)
  else none

private def rows : List Edge :=
  [(((7, false), 11, 40), ((7, false), 12, 41)),
   (((7, true), 11, 90), ((7, true), 12, 93)),
   (((7, false), 12, 41), ((7, false), 13, 42))]

/-- Global inventory balance authenticates repeated accesses without merging address spaces. -/
private theorem replay : ResourceReplay Prod.fst id initial rows final := by
  apply replay_of_balance Prod.fst id (fun a b : Record => a.2.1 < b.2.1)
    (fun _ => Nat.lt_irrefl _) (fun {_ _ _} ab bc => Nat.lt_trans ab bc)
  · apply frontierBalance_of_inventory Prod.fst id rows initial final
      (↑[((7, false), 11, 40), ((7, true), 11, 90), ((9, false), 5, 77)])
      (↑[((7, false), 13, 42), ((7, true), 12, 93), ((9, false), 5, 77)])
    · decide
    · intro k
      by_cases a : k = (7, false)
      · subst k; decide
      by_cases b : k = (7, true)
      · subst k; decide
      by_cases c : k = (9, false)
      · subst k; decide
      simp [initial, optionalRecord, a, b, c, Ne.symm a, Ne.symm b, Ne.symm c]
    · intro k
      by_cases a : k = (7, false)
      · subst k; decide
      by_cases b : k = (7, true)
      · subst k; decide
      by_cases c : k = (9, false)
      · subst k; decide
      simp [final, optionalRecord, a, b, c, Ne.symm a, Ne.symm b, Ne.symm c]
    · intro row member
      simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> rfl
  · intro row member
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro k
    by_cases a : k = (7, false)
    · subst k; decide
    by_cases b : k = (7, true)
    · subst k; decide
    simp [accessesAt, rows, Ne.symm a, Ne.symm b]

/-- Replay determines every final entry, including participating but untouched keys. -/
example : final = rows.foldl (fun (current : ResourceFrontier Key Record) row =>
    Function.update current row.1.1 (some row.2)) initial :=
  replay.final_eq_fold Prod.fst id

/-- An untouched nonzero record is retained, rather than replaced with a zero default. -/
example : final (9, false) = some ((9, false), 5, 77) := by
  rw [← replay.frame Prod.fst id (9, false) (by
    intro row member
    simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide)]
  rfl

/-- Matching the numeric address does not authorize a value from the other address space. -/
example : ¬ ResourceReplay Prod.fst id initial
    [(((7, false), 11, 90), ((7, false), 12, 93))] final := by
  simp [ResourceReplay, initial]

private def observation (r : Record) := (r.1, r.2.2)
private def version (r : Record) := r.2.1
private def refreshInitial : Multiset Record :=
  ↑[((7, false), 11, 40), ((7, true), 14, 90), ((9, false), 5, 77)]
private def refreshFinal : Multiset Record :=
  ↑[((7, false), 21, 42), ((7, true), 15, 90), ((9, false), 5, 77)]
private def realAccesses : Multiset Edge :=
  {(((7, false), 13, 40), ((7, false), 20, 42))}
private def refreshes : Multiset Edge :=
  ↑[(((7, false), 11, 40), ((7, false), 12, 40)),
    (((7, false), 12, 40), ((7, false), 13, 40)),
    (((7, false), 20, 42), ((7, false), 21, 42)),
    (((7, true), 14, 90), ((7, true), 15, 90))]

/-- Elimination handles chained refreshes, refreshes after a real write, and a key with
only refreshes. It retains real successors and all final observations with multiplicity,
while each rewritten predecessor and boundary record has a no-later version. -/
example : ∃ (real' : Multiset Edge) (final' : Multiset Record),
    refreshInitial + real'.map Prod.snd = final' + real'.map Prod.fst ∧
    Multiset.Rel (Refresh.EdgeRewrite observation version) realAccesses real' ∧
    Multiset.Rel (Refresh.RecordRewrite observation version) refreshFinal final' ∧
    real'.map Prod.snd = realAccesses.map Prod.snd ∧
    final'.map observation = refreshFinal.map observation ∧
    real'.card = realAccesses.card ∧ final'.card = refreshFinal.card := by
  obtain ⟨real', final', balance, realRel, finalRel⟩ :=
    Refresh.eliminate observation version refreshInitial 4 refreshes realAccesses refreshFinal
      (by decide) (by simp [refreshes, Refresh.IsRefresh, observation, version]) (by decide)
  have successors : realAccesses.map Prod.snd = real'.map Prod.snd :=
    Multiset.Rel.recOn realRel rfl fun related _ ih => by
      simp only [Multiset.map_cons, related.1, ih]
  have observations : refreshFinal.map observation = final'.map observation :=
    Multiset.Rel.recOn finalRel rfl fun related _ ih => by
      simp only [Multiset.map_cons, related.1, ih]
  refine ⟨real', final', balance, realRel, finalRel, successors.symm, observations.symm, ?_, ?_⟩
  · have counts := congrArg Multiset.card successors.symm
    simpa only [Multiset.card_map] using counts
  · have counts := congrArg Multiset.card observations.symm
    simpa only [Multiset.card_map] using counts

end ResourceFrontierTests
