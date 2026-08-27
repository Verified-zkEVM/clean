import Clean.Halo2.Keygen.CompressSelectors

namespace Halo2

/-!
# Trace-sensitive selector-packing certificates

The greedy selector compressor observes only a small subset of a circuit's conflict
relation. These definitions expose the exact `any` questions it asks, so a circuit
can justify the packing without materializing or equating a complete conflict matrix.
-/

/-- One conflict question asked while considering a selector for a combination. -/
structure SelectorCombinationQuery (α : Type) where
  combination : List α
  selector : α
  expected : Bool
deriving DecidableEq, Repr

/-- Conflict questions asked by one reference execution of the greedy inner loop. -/
def extendCombinationQueries {α : Type} (maxDegree : ℕ)
    (degree : α → ℕ) (conflicts : α → α → Bool) :
    ℕ → List α → List α → List (SelectorCombinationQuery α)
  | _, _, [] => []
  | currentDegree, combination, selector :: remaining =>
      if currentDegree + combination.length = maxDegree then
        []
      else
        let query := {
          combination
          selector
          expected := combination.any (conflicts · selector) }
        if query.expected then
          query :: extendCombinationQueries maxDegree degree conflicts
            currentDegree combination remaining
        else
          let nextDegree := max currentDegree (degree selector - 1)
          if nextDegree + combination.length + 1 > maxDegree then
            query :: extendCombinationQueries maxDegree degree conflicts
              currentDegree combination remaining
          else
            query :: extendCombinationQueries maxDegree degree conflicts
              nextDegree (combination ++ [selector]) remaining

/-- Conflict questions asked by one reference execution of the full packing. -/
def buildCombinationsQueries {α : Type} (maxDegree : ℕ)
    (degree : α → ℕ) (conflicts : α → α → Bool) :
    ℕ → List α → List (SelectorCombinationQuery α)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, selector :: remaining =>
      let result := extendCombinationWith maxDegree degree conflicts
        (degree selector - 1) [selector] remaining
      extendCombinationQueries maxDegree degree conflicts
          (degree selector - 1) [selector] remaining ++
        buildCombinationsQueries maxDegree degree conflicts fuel result.2

/-- Agreement on the `any` questions asked by the reference execution reproduces
the same inner-loop result. -/
theorem extendCombinationWith_eq_of_queries {α : Type}
    (maxDegree currentDegree : ℕ) (degree : α → ℕ)
    (actual reference : α → α → Bool)
    (combination selectors : List α)
    (hagrees : ∀ query ∈ extendCombinationQueries maxDegree degree reference
      currentDegree combination selectors,
      query.combination.any (actual · query.selector) = query.expected) :
    extendCombinationWith maxDegree degree actual currentDegree
        combination selectors =
      extendCombinationWith maxDegree degree reference currentDegree
        combination selectors := by
  induction selectors generalizing currentDegree combination with
  | nil => rfl
  | cons selector remaining inductionHypothesis =>
      simp only [extendCombinationQueries, extendCombinationWith] at hagrees ⊢
      split at hagrees <;> rename_i hdegreeCapacity
      · simp only [if_pos hdegreeCapacity]
      · simp only [if_neg hdegreeCapacity]
        let query : SelectorCombinationQuery α := {
          combination
          selector
          expected := combination.any (reference · selector) }
        have hcurrent : combination.any (actual · selector) =
            combination.any (reference · selector) := by
          simpa only [query] using hagrees query (by
            by_cases hconflict :
                combination.any (reference · selector) = true
            · rw [if_pos hconflict]
              exact List.mem_cons_self
            · rw [if_neg hconflict]
              split <;> exact List.mem_cons_self)
        rw [hcurrent]
        split at hagrees <;> rename_i hconflict
        · simp only [if_pos hconflict]
          exact congrArg
            (fun result : List α × List α =>
              (result.1, selector :: result.2))
            (inductionHypothesis currentDegree combination (by
              intro recursive hrecursive
              apply hagrees recursive
              exact List.mem_cons_of_mem _ hrecursive))
        · simp only [if_neg hconflict]
          split at hagrees <;> rename_i hnextDegree
          · simp only [if_pos hnextDegree]
            exact congrArg
              (fun result : List α × List α =>
                (result.1, selector :: result.2))
              (inductionHypothesis currentDegree combination (by
                intro recursive hrecursive
                apply hagrees recursive
                exact List.mem_cons_of_mem _ hrecursive))
          · simp only [if_neg hnextDegree]
            apply inductionHypothesis
            intro recursive hrecursive
            apply hagrees recursive
            exact List.mem_cons_of_mem _ hrecursive

/-- Agreement on the finite query trace reproduces the complete greedy packing. -/
theorem buildCombinationsWith_eq_of_queries {α : Type}
    (maxDegree fuel : ℕ) (degree : α → ℕ)
    (actual reference : α → α → Bool) (selectors : List α)
    (hagrees : ∀ query ∈ buildCombinationsQueries maxDegree degree reference
      fuel selectors,
      query.combination.any (actual · query.selector) = query.expected) :
    buildCombinationsWith maxDegree degree actual fuel selectors =
      buildCombinationsWith maxDegree degree reference fuel selectors := by
  induction fuel generalizing selectors with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      cases selectors with
      | nil => rfl
      | cons selector remaining =>
          simp only [buildCombinationsQueries] at hagrees
          have hinner := extendCombinationWith_eq_of_queries maxDegree
            (degree selector - 1) degree actual reference [selector] remaining
            (by
              intro query hquery
              exact hagrees query (List.mem_append_left _ hquery))
          simp only [buildCombinationsWith]
          rw [hinner]
          apply congrArg (List.cons _)
          apply inductionHypothesis
          intro query hquery
          exact hagrees query (List.mem_append_right _ hquery)

end Halo2
