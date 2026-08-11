import Clean.Halo2.Keygen.FloorPlanner

/-! Ordering correctness of the legacy pdqsort implementation. -/

namespace Halo2.FloorPlanner.Pdqsort

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

end Halo2.FloorPlanner.Pdqsort
