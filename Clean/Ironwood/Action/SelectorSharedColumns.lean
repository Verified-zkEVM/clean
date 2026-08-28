import Clean.Halo2.Keygen.FloorPlanner.SelectorConflicts
import Clean.Ironwood.Action.Compilation

/-!
# Shared selector columns in the Orchard Action circuit

The primary V1 anchor covers most selector pairs. These two compact selector
families record the additional physical advice columns needed by the selector
packing proof. Each selector is reduced once, rather than recomputing pairwise
column intersections.
-/

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

def actionAdviceColumn6Selectors : List ℕ :=
  [0, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20, 21, 22, 23, 24]

def actionLateAdviceColumn6Selectors : List ℕ :=
  [29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
   44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

def actionAdviceColumn9Selectors : List ℕ :=
  [4, 9, 10, 11, 12, 13, 14, 15, 17]

set_option maxRecDepth 10000 in
theorem actionAdviceColumn6Selectors_useColumn :
    actionAdviceColumn6Selectors.Forall fun selector =>
      SelectorUsesColumn actionSynthesisSummary selector
        (.column .advice 6) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem actionLateAdviceColumn6Selectors_useColumn :
    actionLateAdviceColumn6Selectors.Forall fun selector =>
      SelectorUsesColumn actionSynthesisSummary selector
        (.column .advice 6) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem actionAdviceColumn9Selectors_useColumn :
    actionAdviceColumn9Selectors.Forall fun selector =>
      SelectorUsesColumn actionSynthesisSummary selector
        (.column .advice 9) := by
  decide +kernel

def actionAdditionalSharedColumnPairs : List (ℕ × ℕ) :=
  [(0, 1), (11, 16), (12, 16), (14, 16), (15, 16), (4, 9),
   (4, 10), (1, 8), (1, 9), (13, 16), (1, 10), (4, 11), (4, 12),
   (4, 13), (4, 14), (4, 15), (8, 16), (16, 17), (16, 20), (4, 17),
   (1, 11), (13, 21), (17, 21), (20, 21), (13, 22), (17, 22),
   (20, 22), (13, 23), (17, 23), (20, 23), (13, 24), (17, 24),
   (20, 24), (15, 21), (15, 22)]

theorem actionAdditionalSharedColumnPairs_useColumn
    (left right : ℕ)
    (hpair : (left, right) ∈ actionAdditionalSharedColumnPairs) :
    ∃ column,
      SelectorUsesColumn actionSynthesisSummary left column ∧
        SelectorUsesColumn actionSynthesisSummary right column := by
  have hcolumn6 := List.forall_iff_forall_mem.mp
    actionAdviceColumn6Selectors_useColumn
  have hcolumn9 := List.forall_iff_forall_mem.mp
    actionAdviceColumn9Selectors_useColumn
  simp only [actionAdditionalSharedColumnPairs, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq] at hpair
  rcases hpair with hpair | hpair | hpair | hpair | hpair | hpair |
      hpair | hpair | hpair | hpair | hpair | hpair | hpair | hpair |
      hpair | hpair | hpair | hpair | hpair | hpair | hpair | hpair |
      hpair | hpair | hpair | hpair | hpair | hpair | hpair | hpair |
      hpair | hpair | hpair | hpair | hpair <;> obtain ⟨rfl, rfl⟩ := hpair
  all_goals first
    | exact ⟨.column .advice 6,
        hcolumn6 _ (by decide), hcolumn6 _ (by decide)⟩
    | exact ⟨.column .advice 9,
        hcolumn9 _ (by decide), hcolumn9 _ (by decide)⟩

end Zcash.Circuits.Action
