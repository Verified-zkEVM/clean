module

public import Clean.Utils.ResourceHistory.Replay

/-! # Forcing the next resource prefix

An execution may reveal one event's accesses before ordering all remaining rows.
If this event's successor versions precede all remaining producers, balance forces
its head predecessor and every internal link. The remaining consumers are arbitrary.
Version windows can establish this ordering without first reconstructing the entire schedule.
-/

@[expose] public section

namespace Utils.ResourceHistory

variable {Access Record : Type*}

/-- Balance establishes the current record and all links of the earliest access prefix.
Neither a previous-access link nor a pre-event bound on a predecessor is assumed. -/
theorem prefix_links (edge : Access → Record × Record) (before : Record → Record → Prop)
    (irrefl : ∀ a, ¬ before a a)
    (trans : ∀ ⦃a b c⦄, before a b → before b c → before a c)
    (own : List Access) (nonempty : own ≠ []) (live : Option Record)
    (otherPushes remainingPulls : Multiset Record)
    (increases : ∀ row ∈ own, before (edge row).1 (edge row).2)
    (ordered : own.Pairwise (fun a b => before (edge a).2 (edge b).2))
    (later : ∀ row ∈ own, ∀ record ∈ otherPushes, before (edge row).2 record)
    (balanced : optionalRecord live + ((↑(own.map fun row => (edge row).2) : Multiset Record) + otherPushes) =
      ↑(own.map fun row => (edge row).1) + remainingPulls) :
    live = some (edge (own.head nonempty)).1 ∧
      own.IsChain (fun a b => (edge b).1 = (edge a).2) := by
  induction own generalizing live with
  | nil => exact (nonempty rfl).elim
  | cons row rest ih =>
    have progress := increases row (List.mem_cons_self ..)
    have order := List.pairwise_cons.mp ordered
    have noProducer : (edge row).1 ∉
        (↑((row :: rest).map fun r => (edge r).2) : Multiset Record) + otherPushes := by
      intro member
      rcases Multiset.mem_add.mp member with ownProducer | otherProducer
      · obtain ⟨producer, member, equal⟩ := List.mem_map.mp (Multiset.mem_coe.mp ownProducer)
        rcases List.mem_cons.mp member with rfl | member
        · exact irrefl _ (equal ▸ progress)
        · have lt := trans progress (order.1 producer member)
          exact irrefl _ (equal ▸ lt)
      · exact irrefl _ (trans progress (later row (List.mem_cons_self ..) _ otherProducer))
    have present : (edge row).1 ∈ optionalRecord live := by
      have member : (edge row).1 ∈ optionalRecord live +
          (↑((row :: rest).map fun r => (edge r).2) + otherPushes) := by
        rw [balanced]
        exact Multiset.mem_add.mpr (Or.inl
          (Multiset.mem_coe.mpr (List.mem_map_of_mem (List.mem_cons_self ..))))
      exact (Multiset.mem_add.mp member).resolve_right noProducer
    have current : live = some (edge row).1 := by
      cases live <;> simp_all [optionalRecord]
    refine ⟨current, ?_⟩
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next tail =>
      have residual : optionalRecord (some (edge row).2) +
          (↑((next :: tail).map fun r => (edge r).2) + otherPushes) =
        ↑((next :: tail).map fun r => (edge r).1) + remainingPulls := by
        rw [current] at balanced
        simp only [optionalRecord, Option.toList_some, List.map_cons, ← Multiset.cons_coe,
          Multiset.coe_nil, Multiset.cons_add, zero_add] at balanced ⊢
        exact (Multiset.cons_inj_right (edge row).1).mp balanced
      obtain ⟨head, links⟩ := ih (List.cons_ne_nil _ _) (some (edge row).2)
        (fun r member => increases r (List.mem_cons_of_mem _ member)) order.2
        (fun r member => later r (List.mem_cons_of_mem _ member)) residual
      exact List.isChain_cons_cons.mpr ⟨(Option.some.inj head).symm, links⟩

end Utils.ResourceHistory
