module

public import Clean.Utils.ResourceHistory.Replay

/-! # From complete inventories to per-key conservation

The boundary inventory contains at most one record for each participating key.
Filtering a global occurrence balance gives `FrontierBalance` when local accesses
preserve their key. Boundary uniqueness and coverage remain explicit obligations
of the boundary provider, rather than assumptions hidden in a ledger decoder.
-/

@[expose] public section

namespace Utils.ResourceHistory

variable {Key Record Access : Type*} [DecidableEq Key]

/-- Exact global conservation specializes to every participating resource. No record
or access is deduplicated, and both boundary inventories must cover their frontiers. -/
theorem frontierBalance_of_inventory (key : Record → Key) (edge : Access → Record × Record)
    (rows : List Access) (initial final : ResourceFrontier Key Record)
    (initialInventory finalInventory : Multiset Record)
    (conservation : initialInventory + (↑rows : Multiset Access).map (fun row => (edge row).2) =
      finalInventory + (↑rows : Multiset Access).map (fun row => (edge row).1))
    (initialRecords : ∀ k, initialInventory.filter (fun record => key record = k) =
      optionalRecord (initial k))
    (finalRecords : ∀ k, finalInventory.filter (fun record => key record = k) =
      optionalRecord (final k))
    (preserves : ∀ row ∈ rows, key (edge row).2 = key (edge row).1) :
    FrontierBalance key edge rows initial final := by
  intro k
  have selected := congrArg (Multiset.filter (fun record => key record = k)) conservation
  rw [Multiset.filter_add, Multiset.filter_add, initialRecords k, finalRecords k,
    Multiset.filter_map, Multiset.filter_map] at selected
  have sameKeys : (↑rows : Multiset Access).filter (fun row => key (edge row).2 = k) =
      (↑rows : Multiset Access).filter (fun row => key (edge row).1 = k) := by
    apply Multiset.filter_congr
    intro row member
    rw [preserves row member]
  simp only [Function.comp_def] at selected
  rw [sameKeys] at selected
  exact selected

end Utils.ResourceHistory
