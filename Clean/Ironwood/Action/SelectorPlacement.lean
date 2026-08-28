import Clean.Halo2.Keygen.FloorPlanner.SelectorConflicts
import Clean.Ironwood.Action.PlannerTrace

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

end Zcash.Circuits.Action
