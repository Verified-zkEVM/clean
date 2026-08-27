import Clean.Halo2.Keygen.FloorPlanner.SelectorConflicts
import Clean.Halo2.Keygen.SelectorPackingCorrectness
import Clean.Ironwood.Action.Compilation

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

private def actionNonzeroSelectors : List ℕ :=
  [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37,
   38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
   54, 55]

private theorem actionSelectorDegreePartitions :
    (List.range 56).filter
        (fun selector => actionSelectorDegrees[selector]! = 0) =
      [2, 3, 25, 29] ∧
    (List.range 56).filter
        (fun selector => actionSelectorDegrees[selector]! ≠ 0) =
      actionNonzeroSelectors := by
  unfold actionSelectorDegrees actionNonzeroSelectors
  decide +kernel

/-- The selector pairs whose conflict result is not determined by the compact
region-local separation argument. The packing width is independent of all
nineteen answers. -/
def actionUnresolvedSelectorPairs : List (ℕ × ℕ) :=
  [(0, 4), (1, 4), (1, 5), (4, 5), (1, 6), (4, 6), (1, 7), (4, 7),
   (4, 8), (23, 26), (23, 27), (24, 26), (24, 27), (28, 30),
   (28, 31), (28, 32), (28, 34), (28, 35), (28, 36)]

private def actionSelectorsMayConflict (left right : ℕ) : Bool :=
  actionUnresolvedSelectorPairs.contains (left, right) ||
    actionUnresolvedSelectorPairs.contains (right, left)

private def actionEarlySelectorConflict
    (unknown : BitVec 9) (left right : ℕ) : Bool :=
  match left, right with
  | 0, 4 | 4, 0 => unknown[0]
  | 1, 4 | 4, 1 => unknown[1]
  | 1, 5 | 5, 1 => unknown[2]
  | 4, 5 | 5, 4 => unknown[3]
  | 1, 6 | 6, 1 => unknown[4]
  | 4, 6 | 6, 4 => unknown[5]
  | 1, 7 | 7, 1 => unknown[6]
  | 4, 7 | 7, 4 => unknown[7]
  | 4, 8 | 8, 4 => unknown[8]
  | _, _ => false

private def actionLateSelectorConflict
    (first : Bool) (unknown : BitVec 9) (left right : ℕ) : Bool :=
  match left, right with
  | 23, 26 | 26, 23 => first
  | 23, 27 | 27, 23 => unknown[0]
  | 24, 26 | 26, 24 => unknown[1]
  | 24, 27 | 27, 24 => unknown[2]
  | 28, 30 | 30, 28 => unknown[3]
  | 28, 31 | 31, 28 => unknown[4]
  | 28, 32 | 32, 28 => unknown[5]
  | 28, 34 | 34, 28 => unknown[6]
  | 28, 35 | 35, 28 => unknown[7]
  | 28, 36 | 36, 28 => unknown[8]
  | _, _ => false

private def actionPackingDegree : ℕ → ℕ
  | 0 => 3 | 1 => 2 | 4 => 3 | 5 => 5 | 6 => 4 | 7 => 4 | 8 => 6
  | 9 => 4 | 10 => 4 | 11 => 4 | 12 => 4 | 13 => 4 | 14 => 4
  | 15 => 3 | 16 => 5 | 17 => 3 | 18 => 9 | 19 => 9 | 20 => 3
  | 21 => 5 | 22 => 6 | 23 => 6 | 24 => 2 | 26 => 4 | 27 => 3
  | 28 => 2 | 30 => 4 | 31 => 3 | 32 => 2 | 33 => 3 | 34 => 3
  | 35 => 3 | 36 => 2 | 37 => 3 | 38 => 3 | 39 => 3 | 40 => 3
  | 41 => 2 | 42 => 3 | 43 => 3 | 44 => 3 | 45 => 3 | 46 => 3
  | 47 => 2 | 48 => 3 | 49 => 3 | 50 => 3 | 51 => 3 | 52 => 2
  | 53 => 3 | 54 => 3 | 55 => 3
  | _ => 0

private theorem actionPackingDegree_eq (selector : ℕ)
    (hselector : selector ∈ actionNonzeroSelectors) :
    actionPackingDegree selector = actionSelectorDegrees[selector]! := by
  have hbound : selector ≤ 55 := by
    simp [actionNonzeroSelectors] at hselector
    omega
  interval_cases selector <;> rfl

private def actionPackingRemainderThree : List (List ℕ) :=
  [[16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55],
   [17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55],
   [18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34,
    35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55]]

private def actionPackingRemainderSixFirst : List ℕ :=
  [23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderSixSecond : List ℕ :=
  [24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
   41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderSix : List (List ℕ) :=
  [actionPackingRemainderSixFirst, actionPackingRemainderSixSecond]

private def actionPackingRemainderNine : List (List ℕ) :=
  [[42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55],
   [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55],
   [46, 47, 48, 49, 50, 51, 52, 53, 54, 55]]

private def actionPackingRemainderTen : List (List ℕ) :=
  [[49, 50, 51, 52, 53, 54, 55], [52, 53, 54, 55], [53, 54, 55]]

private theorem actionPackingRemainder_three (unknown : BitVec 9) :
    packingRemainderWith 9 actionPackingDegree
        (actionEarlySelectorConflict unknown) 3 actionNonzeroSelectors ∈
      actionPackingRemainderThree := by
  decide +revert +kernel

private theorem actionPackingRemainder_six
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderThree) :
    packingRemainderWith 9 actionPackingDegree
        (fun _ _ => false) 3 selectors ∈
      actionPackingRemainderSix := by
  simp only [actionPackingRemainderThree, List.mem_cons, List.not_mem_nil,
    or_false]
    at hselectors
  rcases hselectors with rfl | rfl | rfl <;> decide +kernel

private theorem actionPackingRemainder_nine_false_first (unknown : BitVec 9) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict false unknown) 3
        actionPackingRemainderSixFirst ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_false_second (unknown : BitVec 9) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict false unknown) 3
        actionPackingRemainderSixSecond ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_true_first (unknown : BitVec 9) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict true unknown) 3
        actionPackingRemainderSixFirst ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_true_second (unknown : BitVec 9) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict true unknown) 3
        actionPackingRemainderSixSecond ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine (first : Bool)
    (unknown : BitVec 9)
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderSix) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict first unknown) 3 selectors ∈
      actionPackingRemainderNine := by
  simp only [actionPackingRemainderSix, List.mem_cons, List.not_mem_nil,
    or_false] at hselectors
  rcases hselectors with rfl | rfl <;> cases first
  · exact actionPackingRemainder_nine_false_first unknown
  · exact actionPackingRemainder_nine_true_first unknown
  · exact actionPackingRemainder_nine_false_second unknown
  · exact actionPackingRemainder_nine_true_second unknown

private theorem actionPackingRemainder_ten
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderNine) :
    packingRemainderWith 9 actionPackingDegree
        (fun _ _ => false) 1 selectors ∈
      actionPackingRemainderTen := by
  simp only [actionPackingRemainderNine, List.mem_cons, List.not_mem_nil,
    or_false]
    at hselectors
  rcases hselectors with rfl | rfl | rfl <;> decide +kernel

private theorem actionPackingRemainder_eleven
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderTen) :
    packingRemainderWith 9 actionPackingDegree
        (fun _ _ => false) 1 selectors = [] := by
  simp only [actionPackingRemainderTen, List.mem_cons, List.not_mem_nil,
    or_false]
    at hselectors
  rcases hselectors with rfl | rfl | rfl <;> decide +kernel

end Zcash.Circuits.Action
