import Clean.Halo2.Keygen.FloorPlanner

/-! Ordering correctness of the legacy pdqsort implementation. -/

namespace Halo2.FloorPlanner.Pdqsort

private theorem arrayToList_getElem!
    {T : Type} [Inhabited T] (array : Array T) (index : ℕ) :
    array.toList[index]! = array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos array.toList index (by simpa using hindex),
      getElem!_pos array index hindex]
    simp
  · rw [getElem!_neg array.toList index (by simpa using hindex),
      getElem!_neg array index hindex]

def ChildOf (parent child : ℕ) : Prop :=
  child = 2 * parent + 1 ∨ child = 2 * parent + 2

def HeapAt (values : ℕ → ℕ) (bound parent : ℕ) : Prop :=
  ∀ child, ChildOf parent child → child < bound →
    values child ≤ values parent

def HeapExceptFrom
    (values : ℕ → ℕ) (bound start hole : ℕ) : Prop :=
  ∀ parent, start ≤ parent → parent ≠ hole →
    HeapAt values bound parent

def HeapFrom (values : ℕ → ℕ) (bound start : ℕ) : Prop :=
  ∀ parent, start ≤ parent → HeapAt values bound parent

def HoleCeiling
    (values : ℕ → ℕ) (bound start hole : ℕ) : Prop :=
  hole = start ∨
    ∀ child, ChildOf hole child → child < bound →
      values child ≤ values ((hole - 1) / 2)

def RepairInvariant
    (values : ℕ → ℕ) (bound start hole : ℕ) : Prop :=
  start ≤ hole ∧
    HeapExceptFrom values bound start hole ∧
      HoleCeiling values bound start hole

def swapAt (values : ℕ → ℕ) (left right index : ℕ) : ℕ :=
  if index = left then values right
  else if index = right then values left
  else values index

def greaterChild (values : ℕ → ℕ) (bound parent : ℕ) : ℕ :=
  let left := 2 * parent + 1
  let right := 2 * parent + 2
  if right < bound ∧ values left < values right then right else left

theorem greaterChild_childOf (values : ℕ → ℕ) (bound parent : ℕ) :
    ChildOf parent (greaterChild values bound parent) := by
  simp only [greaterChild]
  split <;> simp [ChildOf]

theorem child_le_greaterChild
    (values : ℕ → ℕ) (bound parent child : ℕ)
    (hchild : ChildOf parent child) (hchildBound : child < bound)
    : values child ≤ values (greaterChild values bound parent) := by
  rcases hchild with rfl | rfl
  · simp only [greaterChild]
    split
    · omega
    · exact Nat.le_refl _
  · simp only [greaterChild]
    split
    · exact Nat.le_refl _
    · rename_i hnotGreater
      simp only [not_and_or, not_lt] at hnotGreater
      rcases hnotGreater with hrightOut | horder
      · omega
      · exact horder

theorem child_parent_unique
    {first second child : ℕ}
    (hfirst : ChildOf first child) (hsecond : ChildOf second child) :
    first = second := by
  rcases hfirst with rfl | rfl <;>
    rcases hsecond with h | h <;> omega

theorem child_gt_parent {parent child : ℕ}
    (hchild : ChildOf parent child) : parent < child := by
  rcases hchild with rfl | rfl <;> omega

theorem child_parent_eq {parent child : ℕ}
    (hchild : ChildOf parent child) : (child - 1) / 2 = parent := by
  rcases hchild with rfl | rfl <;> omega

theorem heapAt_of_greaterChild_out
    (values : ℕ → ℕ) (bound parent : ℕ)
    (hout : bound ≤ greaterChild values bound parent) :
    HeapAt values bound parent := by
  intro child hchild hbound
  rcases hchild with rfl | rfl
  · simp only [greaterChild] at hout
    split at hout <;> omega
  · simp only [greaterChild] at hout
    split at hout <;> omega

theorem heapAt_of_greaterChild_le
    (values : ℕ → ℕ) (bound parent : ℕ)
    (hgreaterLe : values (greaterChild values bound parent) ≤ values parent) :
    HeapAt values bound parent := by
  intro child hchild hchildBound
  exact (child_le_greaterChild values bound parent child
    hchild hchildBound).trans hgreaterLe

theorem RepairInvariant.finish
    (values : ℕ → ℕ) (bound start hole : ℕ)
    (hinvariant : RepairInvariant values bound start hole)
    (hhole : HeapAt values bound hole) :
    HeapFrom values bound start := by
  intro parent hstart
  by_cases heq : parent = hole
  · simpa [heq] using hhole
  · exact hinvariant.2.1 parent hstart heq

theorem repairInvariant_swap
    (values : ℕ → ℕ) (bound start hole : ℕ)
    (hinvariant : RepairInvariant values bound start hole)
    (hgreater : greaterChild values bound hole < bound)
    (hviolation : values hole ≤ values (greaterChild values bound hole)) :
    RepairInvariant
      (swapAt values hole (greaterChild values bound hole))
      bound start (greaterChild values bound hole) := by
  let greater := greaterChild values bound hole
  have hgreaterBound : greater < bound := by simpa only [greater] using hgreater
  have hviolation' : values hole ≤ values greater := by
    simpa only [greater] using hviolation
  suffices RepairInvariant (swapAt values hole greater) bound start greater by
    simpa only [greater] using this
  have hchild : ChildOf hole greater := greaterChild_childOf values bound hole
  have hholeGreater : hole < greater := child_gt_parent hchild
  have hparent : (greater - 1) / 2 = hole := child_parent_eq hchild
  have hstartHole := hinvariant.1
  have hgreaterHeap : HeapAt values bound greater :=
    hinvariant.2.1 greater (by omega) (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · intro parent hstart hnotHole child hparentChild hchildBound
    by_cases hparentOldHole : parent = hole
    · subst parent
      have hchildLe : values child ≤ values greater := by
        have hbound := child_le_greaterChild values bound hole child
          hparentChild hchildBound
        simpa only [greater] using hbound
      by_cases hchildGreater : child = greater
      · simp [swapAt, hchildGreater, hholeGreater.ne', hviolation']
      · have hchildNotHole : child ≠ hole :=
          (child_gt_parent hparentChild).ne'
        simp [swapAt, hchildNotHole, hchildGreater, hchildLe]
    · have holdHeap := hinvariant.2.1 parent hstart hparentOldHole
      have hold := holdHeap child hparentChild hchildBound
      have hparentNotGreater : parent ≠ greater := hnotHole
      have hparentNotHole := hparentOldHole
      by_cases hchildOldHole : child = hole
      ·
        have hholeNotStart : hole ≠ start := by
          intro heq
          have hparentBefore := child_gt_parent hparentChild
          rw [hchildOldHole, heq] at hparentBefore
          omega
        rcases hinvariant.2.2 with heq | hceiling
        · exact (hholeNotStart heq).elim
        · have hparentEq : parent = (hole - 1) / 2 := by
            have := child_parent_eq hparentChild
            rw [hchildOldHole] at this
            omega
          have hgreaterLe := hceiling greater hchild hgreaterBound
          have hparentBefore := child_gt_parent hparentChild
          rw [hchildOldHole] at hparentBefore
          have hceilingNotHole : (hole - 1) / 2 ≠ hole := by
            rw [← hparentEq]
            omega
          have hceilingNotGreater : (hole - 1) / 2 ≠ greater := by
            rw [← hparentEq]
            omega
          rw [hparentEq]
          simpa [swapAt, hchildOldHole, hceilingNotHole,
            hceilingNotGreater] using hgreaterLe
      · have hchildNotGreater : child ≠ greater := by
          intro heq
          subst child
          exact hparentOldHole (child_parent_unique hparentChild hchild)
        simp [swapAt, hparentNotHole, hparentNotGreater,
          hchildOldHole, hchildNotGreater, hold]
  · right
    intro child hgreaterChild hchildBound
    have hold := hgreaterHeap child hgreaterChild hchildBound
    have hchildAfterGreater := child_gt_parent hgreaterChild
    have hchildNotHole : child ≠ hole := by omega
    have hchildNotGreater : child ≠ greater := by omega
    simp [swapAt, hchildNotHole, hchildNotGreater, hparent, hold]

theorem swp_values
    {T : Type} [Inhabited T] (key : T → ℕ)
    (array : Array T) (left right : ℕ)
    (hleft : left < array.size) (hright : right < array.size) :
    (fun index => key (swp array left right)[index]!) =
      swapAt (fun index => key array[index]!) left right := by
  funext index
  by_cases hindex : index < array.size
  · rw [getElem!_pos _ _ (by simpa [swp] using hindex)]
    simp only [swp, Array.set!, swapAt]
    rw [Array.getElem_setIfInBounds (xs := array.setIfInBounds left array[right]!)
      (by simpa using hindex)]
    by_cases hindexRight : right = index
    · rw [if_pos hindexRight]
      subst index
      by_cases heq : right = left
      · subst left
        simp
      · simp [heq]
    · rw [if_neg hindexRight,
        Array.getElem_setIfInBounds hindex]
      by_cases hindexLeft : left = index
      · rw [if_pos hindexLeft]
        subst index
        simp
      · rw [if_neg hindexLeft]
        have hleftIndex : index ≠ left := Ne.symm hindexLeft
        have hrightIndex : index ≠ right := Ne.symm hindexRight
        simp [hleftIndex, hrightIndex,
          getElem!_pos array index hindex]
  · have hindexLeft : index ≠ left := by
      intro heq
      subst index
      exact hindex hleft
    have hindexRight : index ≠ right := by
      intro heq
      subst index
      exact hindex hright
    rw [getElem!_neg _ _ (by simpa [swp] using hindex)]
    simp [swapAt, hindexLeft, hindexRight,
      getElem!_neg array index hindex]

theorem RepairInvariant.initial
    (values : ℕ → ℕ) (bound start : ℕ)
    (hheap : HeapFrom values bound (start + 1)) :
    RepairInvariant values bound start start := by
  exact ⟨Nat.le_refl _, by
    intro parent hstart hne
    exact hheap parent (by omega), Or.inl rfl⟩

theorem siftDown_loop_heap
    {T : Type} [Inhabited T] (key : T → ℕ) :
    ∀ (indices : List ℕ) (node : ℕ) (array : Array T) (start : ℕ),
      array.size - node + 1 ≤ indices.length →
      node < array.size →
      RepairInvariant (fun index => key array[index]!)
        array.size start node →
      let result : MProd ℕ (Array T) := Id.run <|
        forIn indices (⟨node, array⟩ : MProd ℕ (Array T))
          fun _ (result : MProd ℕ (Array T)) =>
            let left := 2 * result.fst + 1
            let right := 2 * result.fst + 2
            let greater := if right < result.snd.size &&
                lessBy key (result.snd[left]!) (result.snd[right]!)
              then right else left
            if greater ≥ result.snd.size ||
                !lessBy key (result.snd[result.fst]!)
                  (result.snd[greater]!) then
              pure (.done ⟨result.fst, result.snd⟩)
            else
              pure (.yield ⟨greater,
                swp result.snd result.fst greater⟩)
      HeapFrom (fun index => key result.snd[index]!)
        result.snd.size start := by
  intro indices
  induction indices with
  | nil =>
      intro node array start hfuel hnode _
      simp only [List.length_nil] at hfuel
      omega
  | cons _ indices inductionHypothesis =>
      intro node array start hfuel hnode hinvariant
      simp only [List.forIn_cons]
      let greater := greaterChild (fun index => key array[index]!)
        array.size node
      have hgreaterEq : greater =
          (if 2 * node + 2 < array.size &&
              lessBy key (array[2 * node + 1]!) (array[2 * node + 2]!)
            then 2 * node + 2 else 2 * node + 1) := by
        simp [greater, greaterChild, lessBy]
      rw [← hgreaterEq]
      split
      · rename_i hstop
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hstop
        rcases hstop with hgreaterOut | hordered
        · exact RepairInvariant.finish _ _ _ _ hinvariant
            (heapAt_of_greaterChild_out _ _ _ hgreaterOut)
        · have hgreaterLe :
              key array[greater]! ≤ key array[node]! := by
            simpa [lessBy] using hordered
          exact RepairInvariant.finish _ _ _ _ hinvariant
            (heapAt_of_greaterChild_le _ _ _ hgreaterLe)
      · rename_i hcontinue
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcontinue
        have hgreaterBound : greater < array.size := by omega
        have hless : lessBy key array[node]! array[greater]! = true := by
          cases hcomparison : lessBy key array[node]! array[greater]! with
          | false =>
              exfalso
              apply hcontinue
              exact Or.inr (by simp [hcomparison])
          | true => rfl
        have hviolation : key array[node]! ≤ key array[greater]! :=
          (lessBy_eq_true_iff _ _ _ |>.mp hless).le
        have hnextInvariantRaw := repairInvariant_swap
          (fun index => key array[index]!) array.size start node
          hinvariant (by simpa only [greater] using hgreaterBound)
          (by simpa only [greater] using hviolation)
        have hnextInvariant : RepairInvariant
            (swapAt (fun index => key array[index]!) node greater)
            array.size start greater := by
          simpa only [greater] using hnextInvariantRaw
        have hvalues := swp_values key array node greater hnode hgreaterBound
        rw [← hvalues] at hnextInvariant
        have hrecursive := inductionHypothesis greater
          (swp array node greater) start (by
          simp only [List.length_cons] at hfuel
          have hchild := greaterChild_childOf
            (fun index => key array[index]!) array.size node
          have hnodeGreater : node < greater := by
            simpa only [greater] using child_gt_parent hchild
          simp [swp]
          omega) (by simpa [swp] using hgreaterBound)
          (by simpa [swp] using hnextInvariant)
        simpa using hrecursive

theorem siftDown_heapFrom
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ) (node : ℕ)
    (hnode : node < array.size)
    (hheap : HeapFrom (fun index => key array[index]!)
      array.size (node + 1)) :
    HeapFrom (fun index => key (siftDown array (lessBy key) node)[index]!)
      (siftDown array (lessBy key) node).size node := by
  have hresult := siftDown_loop_heap key (List.range' 0 (array.size + 1))
    node array node (by simp) hnode
    (RepairInvariant.initial _ _ _ hheap)
  simpa [siftDown] using hresult

theorem heapFrom_half (values : ℕ → ℕ) (bound : ℕ) :
    HeapFrom values bound (bound / 2) := by
  intro parent hparent child hchild hchildBound
  rcases hchild with rfl | rfl <;> omega

theorem childOf_parent (index : ℕ) (hindex : 0 < index) :
    ChildOf ((index - 1) / 2) index := by
  unfold ChildOf
  omega

theorem HeapFrom.root_max
    (values : ℕ → ℕ) (bound index : ℕ)
    (hheap : HeapFrom values bound 0) (hindex : index < bound) :
    values index ≤ values 0 := by
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
      by_cases hzero : index = 0
      · subst index
        exact Nat.le_refl _
      · let parent := (index - 1) / 2
        have hpositive : 0 < index := Nat.zero_lt_of_ne_zero hzero
        have hparentBefore : parent < index := by
          simp [parent]
          omega
        have hchild : ChildOf parent index := childOf_parent index hpositive
        have hedge := hheap parent (by omega) index hchild hindex
        exact hedge.trans (inductionHypothesis parent hparentBefore (by omega))

theorem HeapFrom.after_root_swap
    (values : ℕ → ℕ) (boundary : ℕ)
    (hheap : HeapFrom values (boundary + 1) 0) :
    HeapFrom (swapAt values 0 boundary) boundary 1 := by
  intro parent hparent child hchild hchildBound
  have hparentBefore := child_gt_parent hchild
  have hold := hheap parent (by omega) child hchild (by omega)
  have hparentZero : parent ≠ 0 := by omega
  have hparentBoundary : parent ≠ boundary := by omega
  have hchildZero : child ≠ 0 := by omega
  have hchildBoundary : child ≠ boundary := by omega
  simpa [swapAt, hparentZero, hparentBoundary,
    hchildZero, hchildBoundary] using hold

theorem heapsort_repairedPrefix_heap
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ)
    (boundary : ℕ) (hboundary : 0 < boundary)
    (hfit : boundary < array.size)
    (hheap : HeapFrom (fun index => key array[index]!)
      (boundary + 1) 0) :
    let swapped := swp array 0 boundary
    let prefixArray := swapped.extract 0 boundary
    let repaired := siftDown prefixArray (lessBy key) 0
    HeapFrom (fun index => key repaired[index]!) repaired.size 0 := by
  let swapped := swp array 0 boundary
  let prefixArray := swapped.extract 0 boundary
  have hswappedValues := swp_values key array 0 boundary (by omega) hfit
  have hswappedHeap := hheap.after_root_swap
  rw [← hswappedValues] at hswappedHeap
  have hprefixSize : prefixArray.size = boundary := by
    simp [prefixArray, swapped, swp]
    omega
  have hprefixRead (index : ℕ) (hindex : index < boundary) :
      prefixArray[index]! = swapped[index]! := by
    rw [getElem!_pos prefixArray index (by omega),
      getElem!_pos swapped index (by simp [swapped, swp]; omega)]
    simp [prefixArray, Array.getElem_extract]
  have hprefixHeap : HeapFrom (fun index => key prefixArray[index]!)
      prefixArray.size 1 := by
    intro parent hparent child hchild hchildBound
    have hparentBefore := child_gt_parent hchild
    have hold := hswappedHeap parent hparent child hchild (by omega)
    dsimp only at hold ⊢
    rw [hprefixRead parent (by omega), hprefixRead child (by omega)]
    exact hold
  exact siftDown_heapFrom prefixArray key 0 (by omega) hprefixHeap

theorem swp_drop
    {T : Type} [Inhabited T] (array : Array T) (boundary : ℕ)
    (hboundary : 0 < boundary) (hfit : boundary < array.size) :
    (swp array 0 boundary).toList.drop boundary =
      array[0]! :: array.toList.drop (boundary + 1) := by
  simp only [swp, Array.set!, Array.toList_setIfInBounds]
  rw [List.set_eq_take_cons_drop array[0]! (by simp; omega)]
  rw [List.set_eq_take_cons_drop array[boundary]! (by simp; omega)]
  simp only [List.take_zero, List.nil_append, Nat.zero_add]
  rw [List.drop_append]
  have hmin : min boundary (array.size - 1 + 1) = boundary := by
    rw [Nat.min_eq_left]
    omega
  simp [List.length_take, hmin]

theorem heapsort_step_drop
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ)
    (boundary : ℕ) (hboundary : 0 < boundary)
    (hfit : boundary < array.size) :
    let swapped := swp array 0 boundary
    let prefixArray := swapped.extract 0 boundary
    let repaired := siftDown prefixArray (lessBy key) 0
    let next := overwrite swapped 0 repaired
    next.toList.drop boundary =
      array[0]! :: array.toList.drop (boundary + 1) := by
  let swapped := swp array 0 boundary
  let prefixArray := swapped.extract 0 boundary
  let repaired := siftDown prefixArray (lessBy key) 0
  let next := overwrite swapped 0 repaired
  suffices next.toList.drop boundary =
      array[0]! :: array.toList.drop (boundary + 1) by
    simpa [next, repaired, prefixArray, swapped] using this
  have hprefixSize : prefixArray.size = boundary := by
    simp [prefixArray, swapped, swp]
    omega
  have hrepairedSize : repaired.size = boundary := by
    have hperm := siftDown_perm prefixArray (lessBy key) 0 (by omega)
    simpa [hprefixSize] using hperm.length_eq
  have hoverwrite := overwrite_toList swapped 0 repaired (by
    simp [swapped, swp, hrepairedSize]
    omega)
  simp only [List.take_zero, List.nil_append, Nat.zero_add] at hoverwrite
  rw [hoverwrite, List.drop_append]
  simp [hrepairedSize, swapped, swp_drop array boundary hboundary hfit]

theorem heapsort_step_heap
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ)
    (boundary : ℕ) (hboundary : 0 < boundary)
    (hfit : boundary < array.size)
    (hheap : HeapFrom (fun index => key array[index]!)
      (boundary + 1) 0) :
    let swapped := swp array 0 boundary
    let prefixArray := swapped.extract 0 boundary
    let repaired := siftDown prefixArray (lessBy key) 0
    let next := overwrite swapped 0 repaired
    HeapFrom (fun index => key next[index]!) boundary 0 := by
  let swapped := swp array 0 boundary
  let prefixArray := swapped.extract 0 boundary
  let repaired := siftDown prefixArray (lessBy key) 0
  let next := overwrite swapped 0 repaired
  suffices HeapFrom (fun index => key next[index]!) boundary 0 by
    simpa [next, repaired, prefixArray, swapped] using this
  have hrepairedHeap := heapsort_repairedPrefix_heap
    array key boundary hboundary hfit hheap
  dsimp only at hrepairedHeap
  have hprefixSize : prefixArray.size = boundary := by
    simp [prefixArray, swapped, swp]
    omega
  have hrepairedSize : repaired.size = boundary := by
    have hperm := siftDown_perm prefixArray (lessBy key) 0 (by omega)
    simpa [hprefixSize] using hperm.length_eq
  have hnextSize : next.size = array.size := by
    simp [next, overwrite_size, swapped, swp]
  have hoverwrite := overwrite_toList swapped 0 repaired (by
    simp [swapped, swp, hrepairedSize]
    omega)
  simp only [List.take_zero, List.nil_append, Nat.zero_add] at hoverwrite
  have hprefixList : next.toList.take boundary = repaired.toList := by
    rw [hoverwrite, List.take_append_of_le_length]
    · simp [hrepairedSize]
    · simp [hrepairedSize]
  have hread (index : ℕ) (hindex : index < boundary) :
      next[index]! = repaired[index]! := by
    have hlistRead := congrArg (fun items : List T => items[index]!) hprefixList
    dsimp only at hlistRead
    rw [← arrayToList_getElem! next index,
      ← arrayToList_getElem! repaired index]
    have htake : (next.toList.take boundary)[index]! =
        next.toList[index]! := by
      rw [getElem!_pos _ index (by
          simp [hnextSize]
          omega),
        getElem!_pos _ index (by simp [hnextSize]; omega)]
      exact List.getElem_take
    rw [htake] at hlistRead
    exact hlistRead
  intro parent hparent child hchild hchildBound
  have hparentBefore := child_gt_parent hchild
  have hold := hrepairedHeap parent hparent child hchild (by
    rw [hrepairedSize]
    exact hchildBound)
  dsimp only at hold ⊢
  rw [hread parent (by omega), hread child hchildBound]
  exact hold

theorem heapsort_step_prefix_le_root
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ)
    (boundary : ℕ) (hboundary : 0 < boundary)
    (hfit : boundary < array.size)
    (hheap : HeapFrom (fun index => key array[index]!)
      (boundary + 1) 0) :
    let swapped := swp array 0 boundary
    let prefixArray := swapped.extract 0 boundary
    let repaired := siftDown prefixArray (lessBy key) 0
    let next := overwrite swapped 0 repaired
    KeysLE key (next.toList.take boundary) (key array[0]!) := by
  let swapped := swp array 0 boundary
  let prefixArray := swapped.extract 0 boundary
  let repaired := siftDown prefixArray (lessBy key) 0
  let next := overwrite swapped 0 repaired
  suffices KeysLE key (next.toList.take boundary) (key array[0]!) by
    simpa [next, repaired, prefixArray, swapped] using this
  have hprefixSize : prefixArray.size = boundary := by
    simp [prefixArray, swapped, swp]
    omega
  have hrepairedSize : repaired.size = boundary := by
    have hperm := siftDown_perm prefixArray (lessBy key) 0 (by omega)
    simpa [hprefixSize] using hperm.length_eq
  have hoverwrite := overwrite_toList swapped 0 repaired (by
    simp [swapped, swp, hrepairedSize]
    omega)
  simp only [List.take_zero, List.nil_append, Nat.zero_add] at hoverwrite
  have hprefixList : next.toList.take boundary = repaired.toList := by
    rw [hoverwrite, List.take_append_of_le_length]
    · simp [hrepairedSize]
    · simp [hrepairedSize]
  rw [hprefixList]
  have hperm := siftDown_perm prefixArray (lessBy key) 0 (by omega)
  apply KeysLE.perm key hperm.symm
  intro item hitem
  obtain ⟨position, hposition⟩ := List.get_of_mem hitem
  have hpositionBound : position.val < boundary := by
    have := position.isLt
    simpa [hprefixSize] using this
  have hprefixRead : prefixArray[position.val]! = swapped[position.val]! := by
    rw [getElem!_pos prefixArray _ (by omega),
      getElem!_pos swapped _ (by simp [swapped, swp]; omega)]
    simp [prefixArray, Array.getElem_extract]
  have hitemEq : item = prefixArray[position.val]! := by
    rw [← arrayToList_getElem!]
    simpa [getElem!_pos prefixArray.toList position.val position.isLt,
      List.get_eq_getElem] using hposition.symm
  rw [hitemEq, hprefixRead]
  by_cases hzero : position.val = 0
  · rw [hzero]
    have hread := congrFun (swp_values key array 0 boundary (by omega) hfit) 0
    rw [hread]
    simpa [swapAt, hboundary.ne'] using
      hheap.root_max _ _ boundary (by omega)
  · have hnotBoundary : position.val ≠ boundary := by omega
    have hread := congrFun (swp_values key array 0 boundary (by omega) hfit)
      position.val
    rw [hread]
    simp only [swapAt, if_neg hzero, if_neg hnotBoundary]
    exact hheap.root_max _ _ position.val (by omega)

def CrossBoundary {T : Type}
    (key : T → ℕ) (items : List T) (boundary : ℕ) : Prop :=
  ∀ left ∈ items.take boundary, ∀ right ∈ items.drop boundary,
    key left ≤ key right

def ExtractionInvariant {T : Type}
    [Inhabited T] (key : T → ℕ) (array : Array T) (boundary : ℕ) : Prop :=
  HeapFrom (fun index => key array[index]!) boundary 0 ∧
    KeySorted key (array.toList.drop boundary) ∧
      CrossBoundary key array.toList boundary

theorem ExtractionInvariant.step
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ)
    (boundary : ℕ) (hboundary : 0 < boundary)
    (hfit : boundary < array.size)
    (hinvariant : ExtractionInvariant key array (boundary + 1)) :
    let swapped := swp array 0 boundary
    let prefixArray := swapped.extract 0 boundary
    let repaired := siftDown prefixArray (lessBy key) 0
    let next := overwrite swapped 0 repaired
    ExtractionInvariant key next boundary := by
  let swapped := swp array 0 boundary
  let prefixArray := swapped.extract 0 boundary
  let repaired := siftDown prefixArray (lessBy key) 0
  let next := overwrite swapped 0 repaired
  suffices ExtractionInvariant key next boundary by
    simpa [next, repaired, prefixArray, swapped] using this
  have hnextHeap := heapsort_step_heap array key boundary hboundary hfit
    hinvariant.1
  have hnextDrop := heapsort_step_drop array key boundary hboundary hfit
  have hnextPrefix := heapsort_step_prefix_le_root
    array key boundary hboundary hfit hinvariant.1
  dsimp only at hnextHeap hnextDrop hnextPrefix
  have hrootMem : array[0]! ∈ array.toList.take (boundary + 1) := by
    rw [getElem!_pos array 0 (by omega)]
    have hzero : 0 < (array.toList.take (boundary + 1)).length := by
      simp
      omega
    have hmem : (array.toList.take (boundary + 1))[0]'hzero ∈
        array.toList.take (boundary + 1) := List.getElem_mem hzero
    simpa [List.getElem_take] using hmem
  have hrootToOldSuffix : KeysGE key
      (array.toList.drop (boundary + 1)) (key array[0]!) := by
    intro item hitem
    exact hinvariant.2.2 array[0]! hrootMem item hitem
  refine ⟨hnextHeap, ?_, ?_⟩
  · rw [hnextDrop, KeySorted, List.map_cons,
      List.sortedLE_iff_pairwise, List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨item, hitem, rfl⟩ := hvalue
      exact hrootToOldSuffix item hitem
    · simpa [KeySorted, List.sortedLE_iff_pairwise] using hinvariant.2.1
  · intro left hleft right hright
    rw [hnextDrop] at hright
    rw [List.mem_cons] at hright
    rcases hright with rfl | hright
    · exact hnextPrefix left hleft
    · exact (hnextPrefix left hleft).trans
        (hrootToOldSuffix right hright)

theorem ExtractionInvariant.initial
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ)
    (hheap : HeapFrom (fun index => key array[index]!) array.size 0) :
    ExtractionInvariant key array array.size := by
  refine ⟨hheap, ?_, ?_⟩
  · rw [show array.toList.drop array.size = [] by simp]
    exact KeySorted.nil key
  · intro _ _ right hright
    rw [show array.toList.drop array.size = [] by simp] at hright
    exact (List.not_mem_nil hright).elim

private theorem extraction_reverse_sorted
    {T : Type} [Inhabited T] (key : T → ℕ) :
    ∀ (count : ℕ) (array : Array T),
      count ≤ array.size →
      ExtractionInvariant key array count →
      KeySorted key
        ((List.range count).reverse.foldl (fun current boundary =>
          if boundary ≥ 1 then
            let swapped := swp current 0 boundary
            let prefixArray := swapped.extract 0 boundary
            let repaired := siftDown prefixArray (lessBy key) 0
            overwrite swapped 0 repaired
          else current) array).toList := by
  intro count
  induction count with
  | zero =>
      intro array _ hinvariant
      simpa using hinvariant.2.1
  | succ count inductionHypothesis =>
      intro array hcount hinvariant
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons]
      by_cases hzero : count = 0
      · subst count
        simp only [ge_iff_le, Nat.reduceLeDiff, List.range_zero,
          List.reverse_nil, List.foldl_nil]
        have hleftSorted : KeySorted key (array.toList.take 1) := by
          rw [KeySorted, List.sortedLE_iff_pairwise,
            List.pairwise_map, List.pairwise_iff_get]
          intro left right horder
          have hleft := left.isLt
          have hright := right.isLt
          simp only [List.length_take] at hleft hright
          omega
        have hresult := KeySorted.append key (array.toList.take 1)
          (array.toList.drop 1) hleftSorted hinvariant.2.1
          hinvariant.2.2
        rw [List.take_append_drop] at hresult
        exact hresult
      · have hpositive : 0 < count := Nat.zero_lt_of_ne_zero hzero
        simp only [ge_iff_le, show 1 ≤ count by omega, if_true]
        let swapped := swp array 0 count
        let prefixArray := swapped.extract 0 count
        let repaired := siftDown prefixArray (lessBy key) 0
        let next := overwrite swapped 0 repaired
        have hnextInvariant := hinvariant.step array key count hpositive
          (by omega)
        dsimp only at hnextInvariant
        have hnextSize : next.size = array.size := by
          simp [next, overwrite_size, swapped, swp]
        have hresult := inductionHypothesis next (by omega) hnextInvariant
        simpa [next, repaired, prefixArray, swapped] using hresult

private theorem heapify_reverse
    {T : Type} [Inhabited T] (key : T → ℕ) :
    ∀ (count : ℕ) (array : Array T),
      count ≤ array.size →
      HeapFrom (fun index => key array[index]!) array.size count →
      let result := (List.range count).reverse.foldl
        (fun current node => siftDown current (lessBy key) node) array
      HeapFrom (fun index => key result[index]!) result.size 0 := by
  intro count
  induction count with
  | zero =>
      intro array _ hheap
      simpa using hheap
  | succ count inductionHypothesis =>
      intro array hcount hheap
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons]
      have hnode : count < array.size := by omega
      let next := siftDown array (lessBy key) count
      have hnextHeap : HeapFrom (fun index => key next[index]!)
          next.size count :=
        siftDown_heapFrom array key count hnode hheap
      have hnextSize : next.size = array.size := by
        have hperm := siftDown_perm array (lessBy key) count hnode
        simpa using hperm.length_eq
      have hresult := inductionHypothesis next (by omega) hnextHeap
      simpa [next] using hresult

/-- Bottom-up heap construction produces a max-heap. -/
theorem heapify
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ) :
    let result := (List.range (array.size / 2)).reverse.foldl
      (fun current node => siftDown current (lessBy key) node) array
    HeapFrom (fun index => key result[index]!) result.size 0 := by
  apply heapify_reverse key (array.size / 2) array
  · exact Nat.div_le_self _ _
  · exact heapFrom_half _ _

private theorem heapify_reverse_size
    {T : Type} [Inhabited T] (key : T → ℕ) :
    ∀ (count : ℕ) (array : Array T),
      count ≤ array.size →
      ((List.range count).reverse.foldl
        (fun current node => siftDown current (lessBy key) node) array).size =
        array.size := by
  intro count
  induction count with
  | zero => intro; simp
  | succ count inductionHypothesis =>
      intro array hcount
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.foldl_cons]
      have hnode : count < array.size := by omega
      have hnextSize : (siftDown array (lessBy key) count).size = array.size := by
        have hperm := siftDown_perm array (lessBy key) count hnode
        simpa using hperm.length_eq
      rw [inductionHypothesis (siftDown array (lessBy key) count) (by omega),
        hnextSize]

/-- Bottom-up heap construction preserves the array length. -/
theorem heapify_size
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ) :
    ((List.range (array.size / 2)).reverse.foldl
      (fun current node => siftDown current (lessBy key) node) array).size =
      array.size :=
  heapify_reverse_size key (array.size / 2) array (Nat.div_le_self _ _)

private theorem forIn_yield_eq_foldl
    {State Item : Type} (items : List Item) (initial : State)
    (step : State → Item → State) :
    Id.run (forIn items initial fun item state =>
      pure (.yield (step state item))) = items.foldl step initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items inductionHypothesis =>
      simp only [List.forIn_cons, List.foldl_cons]
      exact inductionHypothesis _

private theorem forIn_yield_eq_pure_foldl
    {State Item : Type} (items : List Item) (initial : State)
    (step : State → Item → State) :
    forIn items initial (fun item state =>
      (pure (.yield (step state item)) : Id (ForInStep State))) =
      (pure (items.foldl step initial) : Id State) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items inductionHypothesis =>
      simp only [List.forIn_cons]
      exact inductionHypothesis _

private theorem forIn_if_yield_eq_pure_foldl
    {State Item : Type} (items : List Item) (initial : State)
    (condition : Item → Prop) [DecidablePred condition]
    (yes no : State → Item → State) :
    forIn items initial (fun item state =>
      if condition item then (pure (.yield (yes state item)) : Id (ForInStep State))
      else (pure (.yield (no state item)) : Id (ForInStep State))) =
      (pure (items.foldl (fun state item =>
        if condition item then yes state item else no state item) initial) : Id State) := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items inductionHypothesis =>
      simp only [List.forIn_cons, List.foldl_cons]
      by_cases hcondition : condition item
      · rw [if_pos hcondition, if_pos hcondition]
        simp only [pure_bind]
        exact inductionHypothesis _
      · rw [if_neg hcondition, if_neg hcondition]
        simp only [pure_bind]
        exact inductionHypothesis _

/-- The legacy heapsort fallback orders its output by the supplied key. -/
theorem heapsort_sorted
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ) :
    KeySorted key (heapsort array (lessBy key)).toList := by
  let heapified := (List.range (array.size / 2)).reverse.foldl
    (fun current node => siftDown current (lessBy key) node) array
  have hheap : HeapFrom (fun index => key heapified[index]!)
      heapified.size 0 := heapify array key
  have hheapifiedSize : heapified.size = array.size := heapify_size array key
  have hinvariant := ExtractionInvariant.initial heapified key hheap
  rw [hheapifiedSize] at hinvariant
  have hsorted := extraction_reverse_sorted key array.size heapified
    (by omega) hinvariant
  have hdefinition :
      heapsort array (lessBy key) =
        (List.range array.size).reverse.foldl (fun current boundary =>
          if boundary ≥ 1 then
            let swapped := swp current 0 boundary
            let prefixArray := swapped.extract 0 boundary
            let repaired := siftDown prefixArray (lessBy key) 0
            overwrite swapped 0 repaired
          else current) heapified := by
    simp only [heapsort]
    simp only [pure_bind]
    rw [forIn_yield_eq_pure_foldl]
    simp only [pure_bind]
    rw [forIn_if_yield_eq_pure_foldl]
    simp [heapified]
  rw [hdefinition]
  exact hsorted

private def orderingContracts
    {T : Type} [Inhabited T] (key : T → ℕ) :
    OrderingContracts T key where
  heapsort_sorted := fun array => heapsort_sorted array key
  partialInsertionSort_sorted := fun array =>
    partialInsertionSort_sorted array key

/-- The complete legacy pdqsort implementation orders its output by the
natural-number key used by V1 region placement. -/
theorem quicksort_sorted
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ) :
    KeySorted key (quicksort array (lessBy key)).toList :=
  quicksort_sorted_of_contracts (orderingContracts key) array

/-- The key sequence produced by legacy pdqsort is the canonical sorted key
sequence. This deliberately forgets the unstable ordering of elements with equal
keys, while retaining everything determined by the comparator. -/
theorem quicksort_keys_eq_mergeSort
    {T : Type} [Inhabited T] (array : Array T) (key : T → ℕ) :
    (quicksort array (lessBy key)).toList.map key =
      (array.toList.map key).mergeSort (· ≤ ·) := by
  apply List.Perm.eq_of_sortedLE
    (quicksort_sorted array key)
    List.sortedLE_mergeSort
  exact (quicksort_perm array (lessBy key)).map key |>.trans
    (List.mergeSort_perm (array.toList.map key) (· ≤ ·)).symm

/-- Stable canonical ordering of index-free V1 region summaries. -/
def stableRegionSort (summaries : List RegionShapeSummary) :
    List RegionShapeSummary :=
  summaries.mergeSort fun left right => left.key ≤ right.key

/-- Legacy pdqsort and the stable canonical region sort have the same exact V1
endpoint whenever tied summaries are placement-equivalent or column-disjoint. -/
theorem V1.slotSummaryEndFromWith_quicksort_eq_stableRegionSort_interchangeable
    (summaries : List RegionShapeSummary)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ summaries →
      ∀ second, second ∈ summaries →
      first.key = second.key →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    let actual :=
      (quicksort summaries.toArray
        (lessBy RegionShapeSummary.key)).reverse.toList
    let canonical := (stableRegionSort summaries).reverse
    V1.slotSummaryEndFromWith initial (actual ++ tail) allocations =
      V1.slotSummaryEndFromWith initial (canonical ++ tail) allocations := by
  let actualAscending :=
    (quicksort summaries.toArray (lessBy RegionShapeSummary.key)).toList
  let canonicalAscending := stableRegionSort summaries
  have hactualPerm : actualAscending.Perm summaries := by
    exact quicksort_perm summaries.toArray
      (lessBy RegionShapeSummary.key)
  have hcanonicalPerm : canonicalAscending.Perm summaries := by
    exact List.mergeSort_perm summaries
      (fun left right => left.key ≤ right.key)
  have hcanonicalKeys :
      canonicalAscending.map RegionShapeSummary.key =
        (summaries.map RegionShapeSummary.key).mergeSort (· ≤ ·) := by
    apply List.map_mergeSort
    intro left hleft right hright
    rfl
  have hactualSorted :
      (actualAscending.reverse.map
        (fun summary => (summary.key : OrderDual ℕ))).SortedLE := by
    have hsorted := quicksort_sorted summaries.toArray
      RegionShapeSummary.key |>.reverse
    simpa only [List.map_reverse] using hsorted
  have hcanonicalSorted :
      (canonicalAscending.reverse.map
        (fun summary => (summary.key : OrderDual ℕ))).SortedLE := by
    have hsorted :
        (canonicalAscending.map RegionShapeSummary.key).SortedLE := by
      rw [hcanonicalKeys]
      exact List.sortedLE_mergeSort
    have hreverse := hsorted.reverse
    simpa only [List.map_reverse] using hreverse
  have hactualReversePerm :
      actualAscending.reverse.Perm summaries.reverse :=
    (List.reverse_perm actualAscending).trans
      (hactualPerm.trans (List.reverse_perm summaries).symm)
  have hcanonicalReversePerm :
      canonicalAscending.reverse.Perm summaries.reverse :=
    (List.reverse_perm canonicalAscending).trans
      (hcanonicalPerm.trans (List.reverse_perm summaries).symm)
  have hactualWellFormed :
      actualAscending.reverse.Forall RegionShapeSummary.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp hwellFormed summary
      (hactualPerm.mem_iff.mp (List.mem_reverse.mp hsummary))
  have hactualTies : ∀ first, first ∈ actualAscending.reverse →
      ∀ second, second ∈ actualAscending.reverse →
      first.key = second.key →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns := by
    intro first hfirst second hsecond hkey
    exact hties first
      (hactualPerm.mem_iff.mp (List.mem_reverse.mp hfirst)) second
      (hactualPerm.mem_iff.mp (List.mem_reverse.mp hsecond)) hkey
  have hresult :=
    V1.slotSummaryEndFromWith_eq_of_sorted_perm_interchangeable
    (key := fun summary : RegionShapeSummary =>
      (show OrderDual ℕ from summary.key))
    (hactualReversePerm.trans hcanonicalReversePerm.symm)
    hactualSorted hcanonicalSorted hactualWellFormed hactualTies
    initial allocations hvalid tail hwellTail
  simpa only [actualAscending, canonicalAscending, stableRegionSort,
    Array.toList_reverse] using hresult

/-- The common specialization where tied summaries are literally equal or
column-disjoint. -/
theorem V1.slotSummaryEndFromWith_quicksort_eq_stableRegionSort
    (summaries : List RegionShapeSummary)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ summaries →
      ∀ second, second ∈ summaries →
      first.key = second.key →
        first = second ∨ List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    let actual :=
      (quicksort summaries.toArray
        (lessBy RegionShapeSummary.key)).reverse.toList
    let canonical := (stableRegionSort summaries).reverse
    V1.slotSummaryEndFromWith initial (actual ++ tail) allocations =
      V1.slotSummaryEndFromWith initial (canonical ++ tail) allocations := by
  exact
    V1.slotSummaryEndFromWith_quicksort_eq_stableRegionSort_interchangeable
      summaries hwellFormed (by
        intro first hfirst second hsecond hkey
        rcases hties first hfirst second hsecond hkey with rfl | hdisjoint
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr hdisjoint)
      initial allocations hvalid tail hwellTail

end Halo2.FloorPlanner.Pdqsort

namespace Halo2.FloorPlanner.V1

/-- The reduced summary stream consumed by V1 is sorted by descending advice
area, independently of any concrete circuit. -/
theorem sortedSummaryOrder_key_sorted {F : Type} (ops : Operations F) :
    ((sortedSummaryOrder ops).map fun summary =>
      (summary.key : OrderDual ℕ)).SortedLE := by
  let shapes := measureRegions ops
  have hsorted :
      ((Pdqsort.quicksort shapes.toArray
        (Pdqsort.lessBy RegionShape.key)).toList.reverse.map fun shape =>
          (shape.key : OrderDual ℕ)).SortedLE := by
    have hascending :=
      Pdqsort.quicksort_sorted shapes.toArray RegionShape.key |>.reverse
    simpa only [List.map_reverse] using hascending
  simpa only [sortedSummaryOrder, shapes, List.map_map,
    Array.toList_reverse, RegionShape.toSummary_key, Pdqsort.lessBy] using hsorted

end Halo2.FloorPlanner.V1
