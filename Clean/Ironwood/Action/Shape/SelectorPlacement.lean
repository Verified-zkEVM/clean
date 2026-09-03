import Clean.Halo2.Keygen.FloorPlanner.SelectorConflicts
import Clean.Ironwood.Action.Shape.PlannerTrace

/-!
# Exceptional Action selector placements

V1's shared-column theorem settles all but six selector pairs queried by the
packing proof. This module records exactly those six reduced-placement results.
-/

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

def actionPlacedSelectorActivations : List (ℕ × ℕ) :=
  placeSelectorActivations (V1.starts actionOperations) 0
    (synthesisSummary actionOperations).regionSelectorActivations

def actionActualSelectorConflict (left right : ℕ) : Bool :=
  selectorActivationsConflict actionPlacedSelectorActivations left right

def actionSpecialSeparatedSelectorPairs : List (ℕ × ℕ) :=
  [(4, 16), (5, 16), (6, 16), (7, 16), (16, 18), (16, 19)]

def actionSpecialSelectorConflict (left right : ℕ) : Bool :=
  (left = 7 && right = 16) || (left = 16 && right = 18)

theorem actionActualSelectorConflict_eq_special
    (left right : ℕ)
    (hpair : (left, right) ∈ actionSpecialSeparatedSelectorPairs) :
    actionActualSelectorConflict left right =
      actionSpecialSelectorConflict left right := by
  simp only [actionSpecialSeparatedSelectorPairs, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair | hpair <;>
    obtain ⟨rfl, rfl⟩ := hpair
  all_goals
    unfold actionActualSelectorConflict actionPlacedSelectorActivations
    simp only [actionSpecialSelectorConflict]
  · apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  · apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  · apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  · apply selectorActivationsConflict_eq_true_of_sitesCoincide
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  · apply selectorActivationsConflict_eq_true_of_sitesCoincide
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  · apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel

/-- Pairs in the late packing phase that cannot be separated merely by a
shared measured column. The list covers the whole reduced numerical phase, not
just the pairs observed along one concrete packing trace. -/
private def actionLateExceptionalSelectorPairs22 : List (ℕ × ℕ) :=
  [(22, 26), (22, 27), (22, 28), (23, 28), (24, 28)]

private def actionLateExceptionalSelectorPairs26a : List (ℕ × ℕ) :=
  [(26, 30), (26, 31), (26, 32), (26, 34), (26, 35), (26, 36)]

private def actionLateExceptionalSelectorPairs26b : List (ℕ × ℕ) :=
  [(26, 37), (26, 38), (26, 39), (26, 40), (26, 41)]

private def actionLateExceptionalSelectorPairs27a : List (ℕ × ℕ) :=
  [(27, 31), (27, 30), (27, 32), (27, 34), (27, 35), (27, 36)]

private def actionLateExceptionalSelectorPairs27b : List (ℕ × ℕ) :=
  [(27, 37), (27, 38), (27, 39), (27, 40), (27, 41)]

private def actionLateExceptionalSelectorPairs28 : List (ℕ × ℕ) :=
  [(28, 37), (28, 38), (28, 39), (28, 40), (28, 41)]

def actionLateExceptionalSelectorPairs : List (ℕ × ℕ) :=
  actionLateExceptionalSelectorPairs22 ++
    (actionLateExceptionalSelectorPairs26a ++
      (actionLateExceptionalSelectorPairs26b ++
        (actionLateExceptionalSelectorPairs27a ++
          (actionLateExceptionalSelectorPairs27b ++
            actionLateExceptionalSelectorPairs28))))

/-- The three genuine collisions among the exceptional late-phase pairs. -/
def actionLateExceptionalSelectorConflict (left right : ℕ) : Bool :=
  (left = 22 && right = 26) || (left = 26 && right = 30) ||
    (left = 27 && right = 31)

private theorem actionActualSelectorConflict_eq_lateExceptional22
    (left right : ℕ)
    (hpair : (left, right) ∈ actionLateExceptionalSelectorPairs22) :
    actionActualSelectorConflict left right =
      actionLateExceptionalSelectorConflict left right := by
  simp only [actionLateExceptionalSelectorPairs22, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair <;>
    obtain ⟨rfl, rfl⟩ := hpair
  all_goals
    unfold actionActualSelectorConflict actionPlacedSelectorActivations
    simp [actionLateExceptionalSelectorConflict]
  · apply selectorActivationsConflict_eq_true_of_sitesCoincide actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  all_goals
    apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel

private theorem actionActualSelectorConflict_eq_lateExceptional26a
    (left right : ℕ)
    (hpair : (left, right) ∈ actionLateExceptionalSelectorPairs26a) :
    actionActualSelectorConflict left right =
      actionLateExceptionalSelectorConflict left right := by
  simp only [actionLateExceptionalSelectorPairs26a, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair | hpair <;>
    obtain ⟨rfl, rfl⟩ := hpair
  all_goals
    unfold actionActualSelectorConflict actionPlacedSelectorActivations
    simp [actionLateExceptionalSelectorConflict]
  · apply selectorActivationsConflict_eq_true_of_sitesCoincide actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  all_goals
    apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel

private theorem actionActualSelectorConflict_eq_lateExceptional26b
    (left right : ℕ)
    (hpair : (left, right) ∈ actionLateExceptionalSelectorPairs26b) :
    actionActualSelectorConflict left right =
      actionLateExceptionalSelectorConflict left right := by
  simp only [actionLateExceptionalSelectorPairs26b, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair <;>
    obtain ⟨rfl, rfl⟩ := hpair
  all_goals
    unfold actionActualSelectorConflict actionPlacedSelectorActivations
    simp [actionLateExceptionalSelectorConflict]
  all_goals
    apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel

private theorem actionActualSelectorConflict_eq_lateExceptional27a
    (left right : ℕ)
    (hpair : (left, right) ∈ actionLateExceptionalSelectorPairs27a) :
    actionActualSelectorConflict left right =
      actionLateExceptionalSelectorConflict left right := by
  simp only [actionLateExceptionalSelectorPairs27a, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair | hpair <;>
    obtain ⟨rfl, rfl⟩ := hpair
  all_goals
    unfold actionActualSelectorConflict actionPlacedSelectorActivations
    simp [actionLateExceptionalSelectorConflict]
  · apply selectorActivationsConflict_eq_true_of_sitesCoincide actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  all_goals
    apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel

private theorem actionActualSelectorConflict_eq_lateExceptional27b
    (left right : ℕ)
    (hpair : (left, right) ∈ actionLateExceptionalSelectorPairs27b) :
    actionActualSelectorConflict left right =
      actionLateExceptionalSelectorConflict left right := by
  simp only [actionLateExceptionalSelectorPairs27b, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair <;>
    obtain ⟨rfl, rfl⟩ := hpair
  all_goals
    unfold actionActualSelectorConflict actionPlacedSelectorActivations
    simp [actionLateExceptionalSelectorConflict]
  all_goals
    apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel

private theorem actionActualSelectorConflict_eq_lateExceptional28
    (left right : ℕ)
    (hpair : (left, right) ∈ actionLateExceptionalSelectorPairs28) :
    actionActualSelectorConflict left right =
      actionLateExceptionalSelectorConflict left right := by
  simp only [actionLateExceptionalSelectorPairs28, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair <;>
    obtain ⟨rfl, rfl⟩ := hpair
  all_goals
    unfold actionActualSelectorConflict actionPlacedSelectorActivations
    simp [actionLateExceptionalSelectorConflict]
  all_goals
    apply selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel

theorem actionActualSelectorConflict_eq_lateExceptional
    (left right : ℕ)
    (hpair : (left, right) ∈ actionLateExceptionalSelectorPairs) :
    actionActualSelectorConflict left right =
      actionLateExceptionalSelectorConflict left right := by
  simp only [actionLateExceptionalSelectorPairs, List.mem_append] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair | hpair
  · exact actionActualSelectorConflict_eq_lateExceptional22 left right hpair
  · exact actionActualSelectorConflict_eq_lateExceptional26a left right hpair
  · exact actionActualSelectorConflict_eq_lateExceptional26b left right hpair
  · exact actionActualSelectorConflict_eq_lateExceptional27a left right hpair
  · exact actionActualSelectorConflict_eq_lateExceptional27b left right hpair
  · exact actionActualSelectorConflict_eq_lateExceptional28 left right hpair

private def actionModeledSelectorPairsEarlyA : List (ℕ × ℕ) :=
  [(0, 4), (1, 4), (1, 5), (4, 5), (1, 6)]

private def actionModeledSelectorPairsEarlyB : List (ℕ × ℕ) :=
  [(4, 6), (1, 7), (4, 7), (4, 8)]

private def actionModeledSelectorPairsLateA : List (ℕ × ℕ) :=
  [(23, 26), (23, 27), (24, 26), (24, 27), (28, 30)]

private def actionModeledSelectorPairsLateB : List (ℕ × ℕ) :=
  [(28, 31), (28, 32), (28, 34), (28, 35), (28, 36)]

/-- The placement-dependent pairs retained by the compact Action packing
model. -/
def actionModeledSelectorPairs : List (ℕ × ℕ) :=
  actionModeledSelectorPairsEarlyA ++
    (actionModeledSelectorPairsEarlyB ++
      (actionModeledSelectorPairsLateA ++ actionModeledSelectorPairsLateB))

/-- The reduced placement answers for the compact Action packing model. -/
def actionModeledSelectorConflict (left right : ℕ) : Bool :=
  (left = 4 && right = 5) || (left = 4 && right = 6) ||
    (left = 1 && right = 7) || (left = 4 && right = 7) ||
    (left = 4 && right = 8) || (left = 28 && right = 31) ||
    (left = 28 && right = 32)

private theorem actionActualSelectorConflict_eq_of_placementLaw
    (left right : ℕ)
    (hlaw : if actionModeledSelectorConflict left right then
        SelectorSitesCoincide (V1.starts actionOperations)
          (synthesisSummary actionOperations) left right
      else
        SelectorSitesPlacedApart (V1.starts actionOperations)
          (synthesisSummary actionOperations) left right) :
    actionActualSelectorConflict left right =
      actionModeledSelectorConflict left right := by
  unfold actionActualSelectorConflict actionPlacedSelectorActivations
  cases hmodel : actionModeledSelectorConflict left right
  · simp only [hmodel, Bool.false_eq_true, ↓reduceIte] at hlaw ⊢
    exact selectorActivationsConflict_eq_false_of_sitesPlacedApart
      actionOperations left right hlaw
  · simp only [hmodel, ↓reduceIte] at hlaw ⊢
    exact selectorActivationsConflict_eq_true_of_sitesCoincide
      actionOperations left right hlaw

private theorem actionActualSelectorConflict_eq_modeledEarlyA
    (left right : ℕ)
    (hpair : (left, right) ∈ actionModeledSelectorPairsEarlyA) :
    actionActualSelectorConflict left right =
      actionModeledSelectorConflict left right := by
  apply actionActualSelectorConflict_eq_of_placementLaw
  have hlaws : actionModeledSelectorPairsEarlyA.Forall fun pair =>
      if actionModeledSelectorConflict pair.1 pair.2 then
        SelectorSitesCoincide (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2
      else
        SelectorSitesPlacedApart (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2 := by
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  exact List.forall_iff_forall_mem.mp hlaws (left, right) hpair

private theorem actionActualSelectorConflict_eq_modeledEarlyB
    (left right : ℕ)
    (hpair : (left, right) ∈ actionModeledSelectorPairsEarlyB) :
    actionActualSelectorConflict left right =
      actionModeledSelectorConflict left right := by
  apply actionActualSelectorConflict_eq_of_placementLaw
  have hlaws : actionModeledSelectorPairsEarlyB.Forall fun pair =>
      if actionModeledSelectorConflict pair.1 pair.2 then
        SelectorSitesCoincide (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2
      else
        SelectorSitesPlacedApart (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2 := by
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  exact List.forall_iff_forall_mem.mp hlaws (left, right) hpair

private theorem actionActualSelectorConflict_eq_modeledLateA
    (left right : ℕ)
    (hpair : (left, right) ∈ actionModeledSelectorPairsLateA) :
    actionActualSelectorConflict left right =
      actionModeledSelectorConflict left right := by
  apply actionActualSelectorConflict_eq_of_placementLaw
  have hlaws : actionModeledSelectorPairsLateA.Forall fun pair =>
      if actionModeledSelectorConflict pair.1 pair.2 then
        SelectorSitesCoincide (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2
      else
        SelectorSitesPlacedApart (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2 := by
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  exact List.forall_iff_forall_mem.mp hlaws (left, right) hpair

private theorem actionActualSelectorConflict_eq_modeledLateB
    (left right : ℕ)
    (hpair : (left, right) ∈ actionModeledSelectorPairsLateB) :
    actionActualSelectorConflict left right =
      actionModeledSelectorConflict left right := by
  apply actionActualSelectorConflict_eq_of_placementLaw
  have hlaws : actionModeledSelectorPairsLateB.Forall fun pair =>
      if actionModeledSelectorConflict pair.1 pair.2 then
        SelectorSitesCoincide (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2
      else
        SelectorSitesPlacedApart (V1.starts actionOperations)
          (synthesisSummary actionOperations) pair.1 pair.2 := by
    rw [← actionSynthesisSummary_eq_operations,
      show V1.starts actionOperations =
        TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
      actionRegionStarts_eq_reduced]
    decide +kernel
  exact List.forall_iff_forall_mem.mp hlaws (left, right) hpair

theorem actionActualSelectorConflict_eq_modeled
    (left right : ℕ)
    (hpair : (left, right) ∈ actionModeledSelectorPairs) :
    actionActualSelectorConflict left right =
      actionModeledSelectorConflict left right := by
  simp only [actionModeledSelectorPairs, List.mem_append] at hpair
  rcases hpair with hpair | hpair | hpair | hpair
  · exact actionActualSelectorConflict_eq_modeledEarlyA left right hpair
  · exact actionActualSelectorConflict_eq_modeledEarlyB left right hpair
  · exact actionActualSelectorConflict_eq_modeledLateA left right hpair
  · exact actionActualSelectorConflict_eq_modeledLateB left right hpair

end Zcash.Circuits.Action
