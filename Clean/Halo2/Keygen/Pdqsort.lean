import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop

namespace Halo2.FloorPlanner

/-! ## Legacy pdqsort (`floor-planner-v1-legacy-pdqsort`)

The Action circuit shapes have MANY tied sort keys (e.g. every "witness message piece"
region shares a shape), and V1 sorts by that key before reversing and slotting
(`strategy.rs:198-242`). With the `floor-planner-v1-legacy-pdqsort` feature — which orchard
enables — pinning the VK against the sort order, the sort is
`halo2_legacy_pdqsort::sort::quicksort`, a byte-for-byte copy of Rust 1.56.1's std
unstable pdqsort (fixed to its 64-bit behaviour). Because the keys tie, that exact
tie-breaking permutation is VK-consensus-critical, so we port the algorithm faithfully
rather than using a stable sort.

The port mirrors `halo2_legacy_pdqsort-0.1.0/src/sort.rs` function-for-function; the sole
representation change is pointers → `Array` indices (`width(l,r) = r - l`). The comparator
is `is_less a b = key a < key b`. -/

namespace Pdqsort

variable {T : Type} [Inhabited T]

/-! ### Ordering vocabulary

The legacy implementation receives a Boolean comparator.  Its floor-planner use is
always a comparison through a natural-number key, so state the semantic contract at
that exact level: this avoids manufacturing an unrelated non-strict order from an
arbitrary Boolean function while remaining generic in the element type and key.
-/

/-- The comparator used by the verified ordering interface. -/
def lessBy (key : T → ℕ) (left right : T) : Bool :=
  decide (key left < key right)

omit [Inhabited T] in
theorem lessBy_eq_true_iff (key : T → ℕ) (left right : T) :
    lessBy key left right = true ↔ key left < key right := by
  simp [lessBy]

omit [Inhabited T] in
theorem lessBy_eq_false_iff (key : T → ℕ) (left right : T) :
    lessBy key left right = false ↔ key right ≤ key left := by
  simp [lessBy]

/-- A list is nondecreasing in the supplied natural-number key. -/
def KeySorted (key : T → ℕ) (items : List T) : Prop :=
  (items.map key).SortedLE

/-- Every key in `items` is at most `bound`. -/
def KeysLE (key : T → ℕ) (items : List T) (bound : ℕ) : Prop :=
  ∀ item ∈ items, key item ≤ bound

/-- Every key in `items` is at least `bound`. -/
def KeysGE (key : T → ℕ) (items : List T) (bound : ℕ) : Prop :=
  ∀ item ∈ items, bound ≤ key item

/-- A pointwise predicate over the half-open array interval `[start, stop)`. -/
def RangeAll (array : Array T) (start stop : ℕ) (predicate : T → Prop) : Prop :=
  ∀ index, start ≤ index → index < stop → predicate array[index]!

theorem RangeAll.mono
    {array : Array T} {outerStart outerStop innerStart innerStop : ℕ}
    {predicate : T → Prop}
    (h : RangeAll array outerStart outerStop predicate)
    (hstart : outerStart ≤ innerStart) (hstop : innerStop ≤ outerStop) :
    RangeAll array innerStart innerStop predicate := by
  intro index hindexStart hindexStop
  exact h index (hstart.trans hindexStart) (hindexStop.trans_le hstop)

theorem RangeAll.empty
    (array : Array T) (index : ℕ) (predicate : T → Prop) :
    RangeAll array index index predicate := by
  intro _ _ h
  omega

theorem RangeAll.append
    {array : Array T} {start middle stop : ℕ}
    {predicate : T → Prop}
    (hleft : RangeAll array start middle predicate)
    (hright : RangeAll array middle stop predicate) :
    RangeAll array start stop predicate := by
  intro index hstart hstop
  by_cases hmiddle : index < middle
  · exact hleft index hstart hmiddle
  · exact hright index (by omega) hstop

theorem RangeAll.transfer
    {before after : Array T} {start stop : ℕ}
    {predicate : T → Prop}
    (hbefore : RangeAll before start stop predicate)
    (heq : ∀ index, start ≤ index → index < stop →
      after[index]! = before[index]!) :
    RangeAll after start stop predicate := by
  intro index hstart hstop
  rw [heq index hstart hstop]
  exact hbefore index hstart hstop

/-- A range predicate applies to every member of the corresponding extracted
array. -/
theorem RangeAll.forall_mem_extract
    {array : Array T} {start stop : ℕ} {predicate : T → Prop}
    (h : RangeAll array start stop predicate)
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    ∀ item ∈ (array.extract start stop).toList, predicate item := by
  intro item hitem
  obtain ⟨position, hposition⟩ := List.get_of_mem hitem
  have hpositionBound : position.val < stop - start := by
    have := position.isLt
    have hbounds : position.val < stop - start ∧
        position.val < array.size - start := by
      simpa [Array.size_extract, Nat.min_eq_left hstop] using this
    exact hbounds.1
  have hitemValue : item = array[start + position.val]! := by
    rw [← hposition, List.get_eq_getElem,
      Array.getElem_toList position.isLt,
      Array.getElem_extract position.isLt]
    rw [getElem!_pos array (start + position.val) (by omega)]
  rw [hitemValue]
  exact h (start + position.val) (by omega) (by omega)

theorem RangeAll.keysLE_extract
    (key : T → ℕ) (array : Array T) (start stop bound : ℕ)
    (h : RangeAll array start stop (fun item => key item ≤ bound))
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    KeysLE key (array.extract start stop).toList bound :=
  h.forall_mem_extract hstart hstop

theorem RangeAll.keysGE_extract
    (key : T → ℕ) (array : Array T) (start stop bound : ℕ)
    (h : RangeAll array start stop (fun item => bound ≤ key item))
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    KeysGE key (array.extract start stop).toList bound :=
  h.forall_mem_extract hstart hstop

omit [Inhabited T] in
theorem KeySorted.of_constant
    (key : T → ℕ) (items : List T) (value : ℕ)
    (h : ∀ item ∈ items, key item = value) :
    KeySorted key items := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map]
  induction items with
  | nil => exact List.Pairwise.nil
  | cons head rest inductionHypothesis =>
      rw [List.pairwise_cons]
      refine ⟨?_, inductionHypothesis (by
        intro item hitem
        exact h item (by simp [hitem]))⟩
      intro item hitem
      rw [h head (by simp), h item (by simp [hitem])]

omit [Inhabited T] in
theorem KeySorted.nil (key : T → ℕ) : KeySorted key [] := by
  rw [KeySorted, List.sortedLE_iff_pairwise]
  exact List.Pairwise.nil

omit [Inhabited T] in
theorem KeySorted.singleton (key : T → ℕ) (item : T) :
    KeySorted key [item] := by
  rw [KeySorted, List.sortedLE_iff_pairwise]
  exact List.Pairwise.cons (by simp) List.Pairwise.nil

omit [Inhabited T] in
theorem KeySorted.append
    (key : T → ℕ) (left right : List T)
    (hleft : KeySorted key left) (hright : KeySorted key right)
    (hcross : ∀ a ∈ left, ∀ b ∈ right, key a ≤ key b) :
    KeySorted key (left ++ right) := by
  rw [KeySorted, List.map_append, List.sortedLE_iff_pairwise] at *
  exact List.pairwise_append.mpr ⟨hleft, hright, by
    intro a ha b hb
    rw [List.mem_map] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact hcross a ha b hb⟩

omit [Inhabited T] in
theorem KeysLE.perm
    (key : T → ℕ) {left right : List T}
    (hperm : left.Perm right) {bound : ℕ}
    (h : KeysLE key left bound) : KeysLE key right bound := by
  intro item hitem
  exact h item (hperm.mem_iff.mpr hitem)

omit [Inhabited T] in
theorem KeysGE.perm
    (key : T → ℕ) {left right : List T}
    (hperm : left.Perm right) {bound : ℕ}
    (h : KeysGE key left bound) : KeysGE key right bound := by
  intro item hitem
  exact h item (hperm.mem_iff.mpr hitem)

theorem KeysGE.get!
    (key : T → ℕ) (array : Array T) (bound index : ℕ)
    (h : KeysGE key array.toList bound) (hindex : index < array.size) :
    bound ≤ key array[index]! := by
  apply h array[index]!
  rw [getElem!_pos array index hindex]
  have hlistIndex : index < array.toList.length := by simpa using hindex
  have hmem := List.getElem_mem (l := array.toList) (n := index) hlistIndex
  simpa only [Array.getElem_toList hindex] using hmem

theorem KeysGE.extract
    (key : T → ℕ) (array : Array T) (start stop bound : ℕ)
    (h : KeysGE key array.toList bound)
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    KeysGE key (array.extract start stop).toList bound := by
  apply RangeAll.keysGE_extract key array start stop bound _ hstart hstop
  intro index _ hindex
  exact KeysGE.get! key array bound index h (by omega)

omit [Inhabited T] in
theorem KeySorted.append_pivot
    (key : T → ℕ) (left : List T) (pivot : T) (right : List T)
    (hleft : KeySorted key left) (hright : KeySorted key right)
    (hleftBound : KeysLE key left (key pivot))
    (hrightBound : KeysGE key right (key pivot)) :
    KeySorted key (left ++ pivot :: right) := by
  apply KeySorted.append key left (pivot :: right) hleft
  · rw [KeySorted, List.map_cons, List.sortedLE_iff_pairwise,
      List.pairwise_cons]
    exact ⟨by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨item, hitem, rfl⟩ := hvalue
      exact hrightBound item hitem, hright.pairwise⟩
  · intro leftItem hleftItem rightItem hrightItem
    rw [List.mem_cons] at hrightItem
    rcases hrightItem with rfl | hrightItem
    · exact hleftBound leftItem hleftItem
    · exact (hleftBound leftItem hleftItem).trans
        (hrightBound rightItem hrightItem)

private theorem array_toList_getElem! (array : Array T) (index : ℕ) :
    array.toList[index]! = array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos array.toList index (by simpa using hindex),
      getElem!_pos array index hindex]
    simp
  · rw [getElem!_neg array.toList index (by simpa using hindex),
      getElem!_neg array index hindex]

theorem KeySorted.keysLE_take_succ
    (key : T → ℕ) (items : List T) (index : ℕ)
    (hsorted : KeySorted key items) (hindex : index < items.length) :
    KeysLE key (items.take (index + 1)) (key items[index]!) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted
  intro item hitem
  obtain ⟨position, hposition⟩ := List.get_of_mem hitem
  have hpositionLe : position.val ≤ index := by
    have := position.isLt
    simp only [List.length_take,
      Nat.min_eq_left (show index + 1 ≤ items.length by omega)] at this
    omega
  have hrelation := hsorted.rel_get_of_le
    (a := ⟨position.val, hpositionLe.trans_lt hindex⟩)
    (b := ⟨index, hindex⟩) hpositionLe
  rw [List.get_eq_getElem, List.get_eq_getElem] at hrelation
  rw [← hposition]
  simpa only [List.get_eq_getElem, List.getElem_take,
    getElem!_pos items index hindex] using hrelation

theorem KeySorted.keysGE_drop_succ
    (key : T → ℕ) (items : List T) (index : ℕ)
    (hsorted : KeySorted key items) (hindex : index < items.length) :
    KeysGE key (items.drop (index + 1)) (key items[index]!) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted
  intro item hitem
  obtain ⟨position, hposition⟩ := List.get_of_mem hitem
  have horiginalLt : index + 1 + position.val < items.length := by
    have := position.isLt
    simp only [List.length_drop] at this
    omega
  have hrelation := hsorted.rel_get_of_lt
    (a := ⟨index, hindex⟩)
    (b := ⟨index + 1 + position.val, horiginalLt⟩) (by
      simp only [Fin.mk_lt_mk]
      omega)
  rw [List.get_eq_getElem, List.get_eq_getElem] at hrelation
  rw [← hposition]
  simpa only [List.get_eq_getElem, List.getElem_drop,
    getElem!_pos items index hindex] using hrelation

omit [Inhabited T] in
theorem KeySorted.take (key : T → ℕ) (items : List T) (count : ℕ)
    (h : KeySorted key items) : KeySorted key (items.take count) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at h ⊢
  exact h.take

omit [Inhabited T] in
theorem KeySorted.drop (key : T → ℕ) (items : List T) (count : ℕ)
    (h : KeySorted key items) : KeySorted key (items.drop count) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at h ⊢
  exact h.drop

omit [Inhabited T] in
theorem KeySorted.set
    (key : T → ℕ) (items : List T) (index : ℕ) (item : T)
    (hsorted : KeySorted key items) (hindex : index < items.length)
    (hprefix : KeysLE key (items.take index) (key item))
    (hsuffix : KeysGE key (items.drop (index + 1)) (key item)) :
    KeySorted key (items.set index item) := by
  rw [List.set_eq_take_cons_drop item hindex]
  exact KeySorted.append_pivot key _ item _
    (KeySorted.take key items index hsorted)
    (KeySorted.drop key items (index + 1) hsorted)
    hprefix hsuffix

private theorem take_append_last (items : List T) (hitems : 0 < items.length) :
    items.take (items.length - 1) ++ [items[items.length - 1]!] = items := by
  rw [← List.dropLast_eq_take,
    getElem!_pos items (items.length - 1) (by omega),
    ← List.getLast_eq_getElem]
  exact List.dropLast_append_getLast (by
    intro hnil
    simp [hnil] at hitems)

theorem KeySorted.keysLE_last
    (key : T → ℕ) (items : List T)
    (hsorted : KeySorted key items) (hitems : 0 < items.length) :
    KeysLE key items (key items[items.length - 1]!) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted
  intro item hitem
  have hrelation := hsorted.rel_getLast hitem
  rw [List.getLast_eq_getElem (by
    intro hnil
    simp [hnil] at hitems)] at hrelation
  simpa [getElem!_pos items (items.length - 1) (by omega)] using hrelation

/-- Stable insertion used to state the pure semantics of pdqsort's shifting
insertion-sort primitive. Equal keys remain in their original order. -/
def insertByKey (key : T → ℕ) (item : T) : List T → List T
  | [] => [item]
  | head :: rest =>
      if key item < key head then
        item :: head :: rest
      else
        head :: insertByKey key item rest

omit [Inhabited T] in
theorem mem_insertByKey_iff
    (key : T → ℕ) (item candidate : T) (items : List T) :
    candidate ∈ insertByKey key item items ↔
      candidate = item ∨ candidate ∈ items := by
  induction items with
  | nil => simp [insertByKey]
  | cons head rest inductionHypothesis =>
      simp only [insertByKey]
      split <;> simp_all [or_left_comm]

omit [Inhabited T] in
theorem insertByKey_perm
    (key : T → ℕ) (item : T) (items : List T) :
    (insertByKey key item items).Perm (item :: items) := by
  induction items with
  | nil => exact .refl _
  | cons head rest inductionHypothesis =>
      simp only [insertByKey]
      split
      · exact .refl _
      · exact (inductionHypothesis.cons head).trans (.swap _ _ _)

omit [Inhabited T] in
theorem insertByKey_eq_append
    (key : T → ℕ) (item : T) (items : List T)
    (hbound : KeysLE key items (key item)) :
    insertByKey key item items = items ++ [item] := by
  induction items with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      have hhead := hbound head (by simp)
      have hnotBefore : ¬key item < key head := by omega
      rw [Pdqsort.insertByKey, if_neg hnotBefore,
        inductionHypothesis (by
          intro candidate hcandidate
          exact hbound candidate (by simp [hcandidate])),
        List.cons_append]

omit [Inhabited T] in
theorem KeySorted.insertByKey
    (key : T → ℕ) (item : T) (items : List T)
    (hitems : KeySorted key items) :
    KeySorted key (insertByKey key item items) := by
  rw [KeySorted, List.sortedLE_iff_pairwise] at hitems ⊢
  induction items with
  | nil =>
      exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons head rest inductionHypothesis =>
      change List.Pairwise (fun left right : ℕ => left ≤ right)
        (key head :: rest.map key) at hitems
      rw [List.pairwise_cons] at hitems
      by_cases hbefore : key item < key head
      · rw [Pdqsort.insertByKey, if_pos hbefore, List.map_cons, List.map_cons,
          List.pairwise_cons]
        exact ⟨by
          intro value hvalue
          rw [List.mem_cons] at hvalue
          rcases hvalue with rfl | hvalue
          · exact hbefore.le
          · exact hbefore.le.trans (hitems.1 value hvalue),
          List.Pairwise.cons hitems.1 hitems.2⟩
      · rw [Pdqsort.insertByKey, if_neg hbefore, List.map_cons, List.pairwise_cons]
        have hrestSorted := inductionHypothesis hitems.2
        refine ⟨?_, hrestSorted⟩
        intro value hvalue
        rw [List.mem_map] at hvalue
        obtain ⟨candidate, hcandidate, rfl⟩ := hvalue
        rw [mem_insertByKey_iff] at hcandidate
        rcases hcandidate with rfl | hcandidate
        · omega
        · exact hitems.1 (key candidate) (by
            rw [List.mem_map]
            exact ⟨_, hcandidate, rfl⟩)

/-- Pure left-to-right insertion sort matching the small-slice path's stable
equal-key behavior. -/
def insertionSortByKey (key : T → ℕ) (items : List T) : List T :=
  items.foldl (fun sorted item => insertByKey key item sorted) []

omit [Inhabited T] in
theorem insertionSortByKey_sorted (key : T → ℕ) (items : List T) :
    KeySorted key (insertionSortByKey key items) := by
  unfold insertionSortByKey
  generalize hsorted : ([] : List T) = sorted
  have hinitial : KeySorted key sorted := by
    rw [← hsorted]
    exact KeySorted.nil key
  clear hsorted
  induction items generalizing sorted with
  | nil => exact hinitial
  | cons item rest inductionHypothesis =>
      simp only [List.foldl_cons]
      exact inductionHypothesis _
        (KeySorted.insertByKey key item sorted hinitial)

omit [Inhabited T] in
theorem insertionSortByKey_perm (key : T → ℕ) (items : List T) :
    (insertionSortByKey key items).Perm items := by
  unfold insertionSortByKey
  have hfold : ∀ (remaining accumulator : List T),
      (remaining.foldl
        (fun sorted item => insertByKey key item sorted) accumulator).Perm
        (remaining.reverse ++ accumulator) := by
    intro remaining
    induction remaining with
    | nil => intro accumulator; exact .refl _
    | cons item rest inductionHypothesis =>
        intro accumulator
        simp only [List.foldl_cons, List.reverse_cons, List.append_assoc]
        exact (inductionHypothesis (insertByKey key item accumulator)).trans
          ((List.Perm.refl rest.reverse).append
            (insertByKey_perm key item accumulator))
  have hresult := hfold items []
  rw [List.append_nil] at hresult
  exact hresult.trans (List.reverse_perm items)

/-- Swap two array entries by index (`slice::swap`). -/
@[inline] def swp (a : Array T) (i j : ℕ) : Array T :=
  let x := a[i]!
  let y := a[j]!
  (a.set! i y).set! j x

theorem swp_size (array : Array T) (left right : ℕ) :
    (swp array left right).size = array.size := by
  simp [swp, Array.set!]

theorem swp_get!
    (array : Array T) (left right index : ℕ)
    (hleft : left < array.size) (hright : right < array.size) :
    (swp array left right)[index]! =
      if index = left then array[right]!
      else if index = right then array[left]!
      else array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos _ _ (by simpa [swp_size] using hindex)]
    simp only [swp, Array.set!]
    rw [Array.getElem_setIfInBounds (xs :=
      array.setIfInBounds left array[right]!) (by simpa using hindex)]
    by_cases hindexRight : right = index
    · rw [if_pos hindexRight]
      subst index
      by_cases heq : right = left
      · subst left
        simp
      · simp [heq]
    · rw [if_neg hindexRight, Array.getElem_setIfInBounds hindex]
      by_cases hindexLeft : left = index
      · rw [if_pos hindexLeft]
        subst index
        simp
      · rw [if_neg hindexLeft]
        simp [Ne.symm hindexLeft, Ne.symm hindexRight,
          getElem!_pos array index hindex]
  · have hindexLeft : index ≠ left := by
      intro heq
      subst index
      exact hindex hleft
    have hindexRight : index ≠ right := by
      intro heq
      subst index
      exact hindex hright
    rw [getElem!_neg _ _ (by simpa [swp_size] using hindex)]
    simp [hindexLeft, hindexRight,
      getElem!_neg array index hindex]

theorem set!_get!
    (array : Array T) (target index : ℕ) (value : T)
    (htarget : target < array.size) :
    (array.set! target value)[index]! =
      if index = target then value else array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos _ _ (by simpa [Array.set!] using hindex)]
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds (by simpa using hindex)]
    by_cases heq : target = index
    · rw [if_pos heq]
      subst index
      simp
    · rw [if_neg heq]
      simp [Ne.symm heq, getElem!_pos array index hindex]
  · have hne : index ≠ target := by
      intro heq
      subst index
      exact hindex htarget
    rw [getElem!_neg _ _ (by simpa [Array.set!] using hindex)]
    simp [hne, getElem!_neg array index hindex]

theorem RangeAll.swp
    (array : Array T) (left right start stop : ℕ)
    (predicate : T → Prop)
    (hleft : left < array.size) (hright : right < array.size)
    (h : RangeAll array start stop predicate)
    (hleftValue : start ≤ left → left < stop → predicate array[right]!)
    (hrightValue : start ≤ right → right < stop → predicate array[left]!) :
    RangeAll (swp array left right) start stop predicate := by
  intro index hindexStart hindexStop
  rw [swp_get! array left right index hleft hright]
  by_cases hindexLeft : index = left
  · rw [if_pos hindexLeft]
    exact hleftValue (hindexLeft ▸ hindexStart) (hindexLeft ▸ hindexStop)
  · rw [if_neg hindexLeft]
    by_cases hindexRight : index = right
    · rw [if_pos hindexRight]
      exact hrightValue (hindexRight ▸ hindexStart)
        (hindexRight ▸ hindexStop)
    · rw [if_neg hindexRight]
      exact h index hindexStart hindexStop

/-- Write `sub` back into `a` starting at `start` (reflecting a mutated sub-slice). -/
def overwrite (a : Array T) (start : ℕ) (sub : Array T) : Array T := Id.run do
  let mut a := a
  for i in [0:sub.size] do
    a := a.set! (start + i) (sub[i]!)
  return a

/-- `shift_tail` (`sort.rs:81-123`): shift the last element left to its sorted position. -/
def shiftTail (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let len := v.size
  if len < 2 then return v
  if !isLess (v[len-1]!) (v[len-2]!) then return v
  let mut v := v
  let tmp := v[len-1]!
  let mut hole := len - 2
  v := v.set! (len-1) (v[len-2]!)
  for i in (List.range (len-2)).reverse do
    if !isLess tmp (v[i]!) then break
    v := v.set! (i+1) (v[i]!)
    hole := i
  v := v.set! hole tmp
  return v

private theorem shiftTail_loop_sorted
    (tmp : T) (key : T → ℕ) :
    ∀ (n : ℕ) (array : Array T),
      n < array.size →
      KeySorted key array.toList →
      KeysGE key (array.toList.drop (n + 1)) (key tmp) →
      let output : Array T := Id.run do
        pure PUnit.unit
        pure PUnit.unit
        let result ← forIn (List.range n).reverse
          (⟨n, array⟩ : MProd ℕ (Array T))
          fun index (result : MProd ℕ (Array T)) =>
            if !lessBy key tmp (result.snd[index]!) then
              pure (.done ⟨result.fst, result.snd⟩)
            else do
              pure PUnit.unit
              pure PUnit.unit
              pure (.yield ⟨index,
                result.snd.set! (index + 1) (result.snd[index]!)⟩)
        pure (result.snd.set! result.fst tmp)
      KeySorted key output.toList := by
  intro n
  induction n with
  | zero =>
      intro array hindex hsorted hsuffix
      have hresult := KeySorted.set key array.toList 0 tmp hsorted
        (by simpa using hindex) (by simp [KeysLE]) (by simpa using hsuffix)
      simpa [Array.set!] using hresult
  | succ n inductionHypothesis =>
      intro array hindex hsorted hsuffix
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.forIn_cons]
      split
      · have hn : n < array.size :=
          Nat.lt_trans (Nat.lt_succ_self n) hindex
        have hbound := KeySorted.keysLE_take_succ key array.toList n hsorted
          (by simpa using hn)
        rw [array_toList_getElem!] at hbound
        have hcompare : key array[n]! ≤ key tmp := by
          simpa [lessBy] using (show (!lessBy key tmp array[n]!) = true from ‹_›)
        have hresult := KeySorted.set key array.toList (n + 1) tmp hsorted
          (by simpa using hindex) (by
            intro item hitem
            exact (hbound item hitem).trans hcompare)
          (by simpa [Nat.add_assoc] using hsuffix)
        simpa [Array.set!] using hresult
      · let shifted := array.set! (n + 1) array[n]!
        have hn : n < array.size := Nat.lt_trans (Nat.lt_succ_self n) hindex
        have hshiftedSorted : KeySorted key shifted.toList := by
          simp only [shifted, Array.set!, Array.toList_setIfInBounds]
          apply KeySorted.set key array.toList (n + 1) array[n]! hsorted
              (by simpa using hindex)
          · have hbound :=
              KeySorted.keysLE_take_succ key array.toList n hsorted hn
            rw [array_toList_getElem!] at hbound
            exact hbound
          · have htail :=
              KeySorted.keysGE_drop_succ key array.toList n hsorted hn
            rw [array_toList_getElem!] at htail
            intro item hitem
            apply htail item
            have hdrop : array.toList.drop (n + 1 + 1) =
                (array.toList.drop (n + 1)).drop 1 := by
              rw [List.drop_drop]
            rw [hdrop] at hitem
            exact List.drop_subset 1 _ hitem
        have hshiftedSize : shifted.size = array.size := by
          simp [shifted]
        have hshiftedAt : shifted[n]! = array[n]! := by
          simp [shifted, hn]
        have hshiftedSuffix :
            KeysGE key (shifted.toList.drop (n + 1)) (key tmp) := by
          have htail := KeySorted.keysGE_drop_succ key shifted.toList n
            hshiftedSorted (by simpa [hshiftedSize] using hn)
          rw [array_toList_getElem!] at htail
          intro item hitem
          have hcompare : key tmp ≤ key shifted[n]! := by
            have hless : key tmp < key array[n]! := by
              simpa [lessBy] using
                (show ¬(!lessBy key tmp array[n]!) = true from ‹_›)
            simpa [hshiftedAt] using hless.le
          exact hcompare.trans (htail item hitem)
        simpa [shifted] using inductionHypothesis shifted
          (by simpa [hshiftedSize] using hn) hshiftedSorted hshiftedSuffix

/-- `shiftTail` preserves ordering when its initial prefix is already ordered. -/
theorem shiftTail_sorted
    (array : Array T) (key : T → ℕ)
    (hprefix : KeySorted key
      (array.toList.take (array.size - 1))) :
    KeySorted key (shiftTail array (lessBy key)).toList := by
  simp only [shiftTail]
  split
  · have hsize : array.size ≤ 1 := by omega
    have hsmall : KeySorted key array.toList := by
      rw [KeySorted, List.sortedLE_iff_pairwise,
        List.pairwise_map, List.pairwise_iff_get]
      intro left right horder
      have hleft := left.isLt
      have hright := right.isLt
      simp only [Array.length_toList] at hleft hright
      omega
    simpa using hsmall
  split
  · have hsize : 2 ≤ array.size := by omega
    have hbound := KeySorted.keysLE_last key
      (array.toList.take (array.size - 1)) hprefix (by simp; omega)
    have hlast :
        (array.toList.take (array.size - 1))[
          (array.toList.take (array.size - 1)).length - 1]! =
          array[array.size - 2]! := by
      rw [getElem!_pos _ _ (by simp; omega), getElem!_pos array _ (by omega)]
      simp [List.getElem_take]
      congr 1
    rw [hlast] at hbound
    have hcompare : key array[array.size - 2]! ≤
        key array[array.size - 1]! := by
      simpa [lessBy] using
        (show (!lessBy key array[array.size - 1]!
          array[array.size - 2]!) = true from ‹_›)
    have hprefixBound : KeysLE key
        (array.toList.take (array.size - 1))
        (key array[array.size - 1]!) := by
      intro item hitem
      exact (hbound item hitem).trans hcompare
    have hresult := KeySorted.append_pivot key _ array[array.size - 1]! []
      hprefix (KeySorted.nil key) hprefixBound (by simp [KeysGE])
    have hdecomposition :
        array.toList.take (array.size - 1) ++
          [array[array.size - 1]!] = array.toList := by
      have hdecomposition := take_append_last array.toList (by simp; omega)
      simp only [Array.length_toList] at hdecomposition
      rw [array_toList_getElem!] at hdecomposition
      exact hdecomposition
    rw [hdecomposition] at hresult
    simpa using hresult
  · have hsize : 2 ≤ array.size := by omega
    let shifted := array.set! (array.size - 1) array[array.size - 2]!
    have hshiftedSorted : KeySorted key shifted.toList := by
      simp only [shifted, Array.set!, Array.toList_setIfInBounds]
      rw [List.set_eq_take_cons_drop array[array.size - 2]!
        (by simp; omega)]
      have hdrop : array.toList.drop (array.size - 1 + 1) = [] := by
        simp
        omega
      rw [hdrop]
      have hbound := KeySorted.keysLE_last key
        (array.toList.take (array.size - 1)) hprefix (by simp; omega)
      have hlast :
          (array.toList.take (array.size - 1))[
            (array.toList.take (array.size - 1)).length - 1]! =
            array[array.size - 2]! := by
        rw [getElem!_pos _ _ (by simp; omega), getElem!_pos array _ (by omega)]
        simp [List.getElem_take]
        congr 1
      rw [hlast] at hbound
      exact KeySorted.append_pivot key _ array[array.size - 2]! []
        hprefix (KeySorted.nil key) hbound (by simp [KeysGE])
    have hshiftedSuffix : KeysGE key
        (shifted.toList.drop (array.size - 2 + 1))
        (key array[array.size - 1]!) := by
      have htail := KeySorted.keysGE_drop_succ key shifted.toList
        (array.size - 2) hshiftedSorted (by simp [shifted]; omega)
      rw [array_toList_getElem!] at htail
      have hshiftedAt : shifted[array.size - 2]! =
          array[array.size - 2]! := by
        have hne : array.size - 2 ≠ array.size - 1 := by omega
        unfold shifted
        rw [getElem!_pos _ _ (by simp; omega),
          getElem!_pos array _ (by omega)]
        simp only [Array.set!]
        rw [Array.getElem_setIfInBounds (by omega), if_neg hne.symm,
          ← getElem!_pos array _ (by omega)]
      rw [hshiftedAt] at htail
      have hless : key array[array.size - 1]! <
          key array[array.size - 2]! := by
        simpa [lessBy] using
          (show ¬(!lessBy key array[array.size - 1]!
            array[array.size - 2]!) = true from ‹_›)
      intro item hitem
      exact hless.le.trans (htail item hitem)
    simpa [shifted] using shiftTail_loop_sorted array[array.size - 1]! key
      (array.size - 2) shifted (by simp [shifted]; omega)
      hshiftedSorted hshiftedSuffix

/-- `shift_head` (`sort.rs:35-78`): shift the first element right to its sorted position. -/
def shiftHead (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let len := v.size
  if len < 2 then return v
  if !isLess (v[1]!) (v[0]!) then return v
  let mut v := v
  let tmp := v[0]!
  let mut hole := 1
  v := v.set! 0 (v[1]!)
  for i in [2:len] do
    if !isLess (v[i]!) tmp then break
    v := v.set! (i-1) (v[i]!)
    hole := i
  v := v.set! hole tmp
  return v

/-- `insertion_sort` (`sort.rs:175-182`). -/
def insertionSort (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let mut v := v
  for i in [1:v.size] do
    v := overwrite v 0 (shiftTail (v.extract 0 (i+1)) isLess)
  return v

/-- One `sift_down` step of `heapsort` (`sort.rs:191-210`). -/
def siftDown (v : Array T) (isLess : T → T → Bool) (node0 : ℕ) : Array T := Id.run do
  let mut v := v
  let mut node := node0
  for _ in [0:v.size+1] do
    let left := 2*node + 1
    let right := 2*node + 2
    let greater := if right < v.size && isLess (v[left]!) (v[right]!) then right else left
    if greater ≥ v.size || !isLess (v[node]!) (v[greater]!) then break
    v := swp v node greater
    node := greater
  return v

/-- `heapsort` (`sort.rs:186-222`). -/
def heapsort (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let mut v := v
  let n := v.size
  for i in (List.range (n/2)).reverse do
    v := siftDown v isLess i
  for i in (List.range n).reverse do
    if i ≥ 1 then
      v := swp v 0 i
      v := overwrite v 0 (siftDown (v.extract 0 i) isLess 0)
  return v

/- Proof-facing decomposition of legacy `partition_in_blocks`. The helpers
mirror the source phases while exposing local permutation and bounds invariants. -/
/-- The block-size update at the head of `partitionInBlocks`' outer loop.
The Boolean arguments are the source conditions `start_l < end_l` and
`start_r < end_r`. -/
def adjustBlockSizes
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool) : ℕ × ℕ :=
  if gap ≤ 2 * 128 then
    let remaining :=
      if pendingLeft || pendingRight then gap - 128 else gap
    if pendingLeft then
      (blockLeft, remaining)
    else if pendingRight then
      (remaining, blockRight)
    else
      (remaining / 2, remaining - remaining / 2)
  else
    (blockLeft, blockRight)

/-- When the outer loop is done, a pending side retains its full 128-entry
block and the other side receives the remainder. With no pending side, the
gap is split in half. In every case the adjusted sizes exactly cover `gap`
and neither exceeds 128. -/
theorem adjustBlockSizes_done
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hdone : gap ≤ 2 * 128)
    (hpendingLeft : pendingLeft = true →
      blockLeft = 128 ∧ 128 ≤ gap)
    (hpendingRight : pendingRight = true →
      blockRight = 128 ∧ 128 ≤ gap) :
    let adjusted :=
      adjustBlockSizes gap blockLeft blockRight
        pendingLeft pendingRight
    adjusted.1 ≤ 128 ∧ adjusted.2 ≤ 128 ∧
      adjusted.1 + adjusted.2 = gap := by
  unfold adjustBlockSizes
  simp only [hdone, ↓reduceIte]
  by_cases hleft : pendingLeft = true
  · have hfull := hpendingLeft hleft
    simp [hleft]
    omega
  · have hleftFalse : pendingLeft = false := by
      cases pendingLeft <;> simp_all
    by_cases hright : pendingRight = true
    · have hfull := hpendingRight hright
      simp [hleftFalse, hright]
      omega
    · have hrightFalse : pendingRight = false := by
        cases pendingRight <;> simp_all
      simp [hleftFalse, hrightFalse]
      omega

/-- Above the done threshold the source adjustment is the identity, so the
ready-state component and sum bounds are inherited unchanged. -/
theorem adjustBlockSizes_not_done
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hnotDone : 2 * 128 < gap)
    (hleft : blockLeft ≤ 128)
    (hright : blockRight ≤ 128)
    (hsum : blockLeft + blockRight ≤ gap) :
    let adjusted :=
      adjustBlockSizes gap blockLeft blockRight
        pendingLeft pendingRight
    adjusted.1 ≤ 128 ∧ adjusted.2 ≤ 128 ∧
      adjusted.1 + adjusted.2 ≤ gap := by
  simp [adjustBlockSizes, show ¬gap ≤ 2 * 128 by omega,
    hleft, hright, hsum]

/-- A branch-independent form suited to the outer-loop invariant. The
pre-adjustment bounds are needed only in the not-done branch; the pending
full-block hypotheses are needed only in the done branch. -/
theorem adjustBlockSizes_bounds
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hbefore : 2 * 128 < gap →
      blockLeft ≤ 128 ∧ blockRight ≤ 128 ∧
        blockLeft + blockRight ≤ gap)
    (hpendingLeft : gap ≤ 2 * 128 →
      pendingLeft = true →
        blockLeft = 128 ∧ 128 ≤ gap)
    (hpendingRight : gap ≤ 2 * 128 →
      pendingRight = true →
        blockRight = 128 ∧ 128 ≤ gap) :
    let adjusted :=
      adjustBlockSizes gap blockLeft blockRight
        pendingLeft pendingRight
    adjusted.1 ≤ 128 ∧ adjusted.2 ≤ 128 ∧
      adjusted.1 + adjusted.2 ≤ gap := by
  by_cases hdone : gap ≤ 2 * 128
  · have hresult :=
      adjustBlockSizes_done gap blockLeft blockRight
        pendingLeft pendingRight hdone
        (hpendingLeft hdone) (hpendingRight hdone)
    exact ⟨hresult.1, hresult.2.1, hresult.2.2.le⟩
  · have hnotDone : 2 * 128 < gap := by omega
    have hready := hbefore hnotDone
    exact adjustBlockSizes_not_done gap blockLeft blockRight
      pendingLeft pendingRight hnotDone
      hready.1 hready.2.1 hready.2.2

/-- At most one pending side is preserved as an explicit source-facing
shape fact: if the left side is pending, the right side is not, and the
adjustment is exactly `(128, gap - 128)`; symmetrically on the right. -/
theorem adjustBlockSizes_pending_shape
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hdone : gap ≤ 2 * 128)
    (hatMostOne :
      ¬(pendingLeft = true ∧ pendingRight = true))
    (hpendingLeft : pendingLeft = true →
      blockLeft = 128)
    (hpendingRight : pendingRight = true →
      blockRight = 128) :
    (pendingLeft = true →
        adjustBlockSizes gap blockLeft blockRight
          pendingLeft pendingRight = (128, gap - 128)) ∧
      (pendingRight = true →
        adjustBlockSizes gap blockLeft blockRight
          pendingLeft pendingRight = (gap - 128, 128)) := by
  constructor
  · intro hleft
    simp [adjustBlockSizes, hdone, hleft, hpendingLeft hleft]
  · intro hright
    have hleft : pendingLeft = false := by
      cases h : pendingLeft
      · rfl
      · exfalso
        exact hatMostOne ⟨h, hright⟩
    simp [adjustBlockSizes, hdone, hleft, hright,
      hpendingRight hright]

omit [Inhabited T] in
private theorem pull_set_perm (value : T) :
    ∀ (items : List T) (index : ℕ) (hindex : index < items.length),
      List.Perm
        (items[index] :: items.set index value)
        (value :: items) := by
  intro items index
  induction items generalizing index with
  | nil => simp
  | cons head tail ih =>
      cases index with
      | zero =>
          intro _
          simp only [List.getElem_cons_zero, List.set_cons_zero]
          exact .swap _ _ _
      | succ index =>
          intro hindex
          simp only [List.getElem_cons_succ, List.set_cons_succ]
          exact (List.Perm.swap _ _ _).trans
            (((ih index (by simpa using hindex)).cons head).trans
              (List.Perm.swap _ _ _))

omit [Inhabited T] in
private theorem set_set_swap_perm
    (items : List T) (left right : ℕ)
    (hleft : left < items.length)
    (hright : right < items.length) :
    List.Perm
      ((items.set left items[right]).set right items[left])
      items := by
  induction items generalizing left right with
  | nil => simp at hleft
  | cons head tail ih =>
      cases left with
      | zero =>
          cases right with
          | zero => simp
          | succ right =>
              simpa only [List.getElem_cons_zero,
                List.getElem_cons_succ, List.set_cons_zero,
                List.set_cons_succ] using
                pull_set_perm head tail right (by simpa using hright)
      | succ left =>
          cases right with
          | zero =>
              simpa only [List.getElem_cons_zero,
                List.getElem_cons_succ, List.set_cons_zero,
                List.set_cons_succ] using
                pull_set_perm head tail left (by simpa using hleft)
          | succ right =>
              simpa only [List.getElem_cons_succ,
                List.set_cons_succ] using
                (ih left right (by simpa using hleft)
                  (by simpa using hright)).cons head

theorem swp_perm
    (array : Array T) (left right : ℕ)
    (hleft : left < array.size)
    (hright : right < array.size) :
    List.Perm (swp array left right).toList array.toList := by
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [show array[left]! = array.toList[left] by simp [hleft],
    show array[right]! = array.toList[right] by simp [hright]]
  exact set_set_swap_perm array.toList left right
    (by simpa using hleft) (by simpa using hright)

/-- The final left-offset cleanup loop. The state fields are
`(endLeft, right, array)`. -/
def cleanupLeft
    (indices : List ℕ) (startLeft left : ℕ)
    (offsetsLeft : Array ℕ)
    (state : MProd ℕ (MProd ℕ (Array T))) :
    MProd ℕ (MProd ℕ (Array T)) := Id.run <|
  forIn indices state fun _ state =>
    let ⟨endLeft, right, array⟩ := state
    if startLeft < endLeft then
      let endLeft := endLeft - 1
      let array :=
        swp array (left + offsetsLeft[endLeft]!) (right - 1)
      let right := right - 1
      pure (.yield ⟨endLeft, right, array⟩)
    else
      pure (.done state)

/-- The final right-offset cleanup loop. The state fields are
`(endRight, left, array)`. -/
def cleanupRight
    (indices : List ℕ) (startRight right : ℕ)
    (offsetsRight : Array ℕ)
    (state : MProd ℕ (MProd ℕ (Array T))) :
    MProd ℕ (MProd ℕ (Array T)) := Id.run <|
  forIn indices state fun _ state =>
    let ⟨endRight, left, array⟩ := state
    if startRight < endRight then
      let endRight := endRight - 1
      let array :=
        swp array left (right - offsetsRight[endRight]! - 1)
      let left := left + 1
      pure (.yield ⟨endRight, left, array⟩)
    else
      pure (.done state)

private theorem cleanupLeft_cons
    (index : ℕ) (indices : List ℕ)
    (startLeft left : ℕ) (offsetsLeft : Array ℕ)
    (endLeft right : ℕ) (array : Array T) :
    cleanupLeft (index :: indices) startLeft left offsetsLeft
        ⟨endLeft, right, array⟩ =
      if startLeft < endLeft then
        cleanupLeft indices startLeft left offsetsLeft
          ⟨endLeft - 1, right - 1,
            swp array (left + offsetsLeft[endLeft - 1]!)
              (right - 1)⟩
      else
        ⟨endLeft, right, array⟩ := by
  by_cases hactive : startLeft < endLeft
  · simp [cleanupLeft, hactive]
  · simp [cleanupLeft, hactive]

private theorem cleanupRight_cons
    (index : ℕ) (indices : List ℕ)
    (startRight right : ℕ) (offsetsRight : Array ℕ)
    (endRight left : ℕ) (array : Array T) :
    cleanupRight (index :: indices) startRight right offsetsRight
        ⟨endRight, left, array⟩ =
      if startRight < endRight then
        cleanupRight indices startRight right offsetsRight
          ⟨endRight - 1, left + 1,
            swp array left
              (right - offsetsRight[endRight - 1]! - 1)⟩
      else
        ⟨endRight, left, array⟩ := by
  by_cases hactive : startRight < endRight
  · simp [cleanupRight, hactive]
  · simp [cleanupRight, hactive]

/-- Cleanup of outstanding left offsets preserves the array multiset and
returns a right boundary no larger than the original array size.

The arithmetic invariant `endLeft - startLeft ≤ right` is precisely what
keeps `right - 1` in bounds through every remaining cleanup iteration. -/
theorem cleanupLeft_contract
    (indices : List ℕ)
    (startLeft left : ℕ) (offsetsLeft : Array ℕ)
    (endLeft right : ℕ) (array original : Array T)
    (hstart : startLeft ≤ endLeft)
    (hremaining : endLeft - startLeft ≤ right)
    (hright : right ≤ array.size)
    (hoffsets : ∀ index, index < endLeft →
      left + offsetsLeft[index]! < array.size)
    (hperm : List.Perm array.toList original.toList) :
    let result :=
      cleanupLeft indices startLeft left offsetsLeft
        ⟨endLeft, right, array⟩
    result.2.1 ≤ original.size ∧
      List.Perm result.2.2.toList original.toList := by
  induction indices generalizing endLeft right array with
  | nil =>
      change right ≤ original.size ∧
        List.Perm array.toList original.toList
      have hsize : array.size = original.size := by
        simpa using hperm.length_eq
      exact ⟨by omega, hperm⟩
  | cons index indices ih =>
      rw [cleanupLeft_cons]
      by_cases hactive : startLeft < endLeft
      · rw [if_pos hactive]
        have hend : startLeft ≤ endLeft - 1 := by omega
        have hrightPositive : 0 < right := by omega
        have hleftIndex :
            left + offsetsLeft[endLeft - 1]! < array.size :=
          hoffsets (endLeft - 1) (by omega)
        have hrightIndex : right - 1 < array.size := by omega
        let next :=
          swp array (left + offsetsLeft[endLeft - 1]!) (right - 1)
        have hnextPerm :
            List.Perm next.toList original.toList :=
          (swp_perm array
            (left + offsetsLeft[endLeft - 1]!) (right - 1)
            hleftIndex hrightIndex).trans hperm
        have hnextSize : next.size = array.size := by
          simp [next, swp, Array.set!]
        apply ih (endLeft - 1) (right - 1) next
        · exact hend
        · omega
        · omega
        · intro offsetIndex hoffsetIndex
          rw [hnextSize]
          exact hoffsets offsetIndex (by omega)
        · exact hnextPerm
      · rw [if_neg hactive]
        change right ≤ original.size ∧
          List.Perm array.toList original.toList
        have hsize : array.size = original.size := by
          simpa using hperm.length_eq
        exact ⟨by omega, hperm⟩

/-- Cleanup of outstanding right offsets preserves the array multiset and
returns a left boundary no larger than the original array size.

The arithmetic invariant `endRight - startRight ≤ right - left` is exactly
what keeps the moving left boundary in range. Active right offsets only
need to be smaller than `right`. -/
theorem cleanupRight_contract
    (indices : List ℕ)
    (startRight right : ℕ) (offsetsRight : Array ℕ)
    (endRight left : ℕ) (array original : Array T)
    (hstart : startRight ≤ endRight)
    (hlr : left ≤ right)
    (hremaining : endRight - startRight ≤ right - left)
    (hright : right ≤ array.size)
    (hoffsets : ∀ index, index < endRight →
      offsetsRight[index]! < right)
    (hperm : List.Perm array.toList original.toList) :
    let result :=
      cleanupRight indices startRight right offsetsRight
        ⟨endRight, left, array⟩
    result.2.1 ≤ original.size ∧
      List.Perm result.2.2.toList original.toList := by
  induction indices generalizing endRight left array with
  | nil =>
      change left ≤ original.size ∧
        List.Perm array.toList original.toList
      have hsize : array.size = original.size := by
        simpa using hperm.length_eq
      exact ⟨by omega, hperm⟩
  | cons index indices ih =>
      rw [cleanupRight_cons]
      by_cases hactive : startRight < endRight
      · rw [if_pos hactive]
        have hend : startRight ≤ endRight - 1 := by omega
        have hltr : left < right := by omega
        have hoffset :
            offsetsRight[endRight - 1]! < right :=
          hoffsets (endRight - 1) (by omega)
        have hrightIndex :
            right - offsetsRight[endRight - 1]! - 1 <
              array.size := by
          omega
        let next :=
          swp array left
            (right - offsetsRight[endRight - 1]! - 1)
        have hnextPerm :
            List.Perm next.toList original.toList :=
          (swp_perm array left
            (right - offsetsRight[endRight - 1]! - 1)
            (by omega) hrightIndex).trans hperm
        have hnextSize : next.size = array.size := by
          simp [next, swp, Array.set!]
        apply ih (endRight - 1) (left + 1) next
        · exact hend
        · omega
        · omega
        · omega
        · intro offsetIndex hoffsetIndex
          exact hoffsets offsetIndex (by omega)
        · exact hnextPerm
      · rw [if_neg hactive]
        change left ≤ original.size ∧
          List.Perm array.toList original.toList
        have hsize : array.size = original.size := by
          simpa using hperm.length_eq
        exact ⟨by omega, hperm⟩

private theorem cycle_repair_eq_swp
    (a : Array T) (tmp : T) (hole next : ℕ)
    (hhole : hole < a.size) (hnext : next < a.size) :
    (a.set! hole a[next]!).set! next tmp =
      swp (a.set! hole tmp) hole next := by
  apply Array.toList_inj.mp
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  by_cases heq : hole = next
  · subst next
    simp [Array.setIfInBounds, hhole]
  ·
    have hreadHole :
        (a.setIfInBounds hole tmp)[hole]! = tmp := by
      simp [Array.setIfInBounds, hhole]
    have hreadNext :
        (a.setIfInBounds hole tmp)[next]! = a[next]! := by
      have hh : hole < a.size := hhole
      rw [show a.setIfInBounds hole tmp = a.set hole tmp hh by
        simp [Array.setIfInBounds, hh]]
      simp [heq, hnext]
    rw [hreadHole, hreadNext]
    simp [hnext]

private theorem cycle_set_loop_perm :
    ∀ (nexts : List ℕ) (current : Array T)
      (hole : ℕ) (tmp : T) (original : Array T),
      hole < current.size →
      (∀ j ∈ nexts, j < current.size) →
      List.Perm (current.set! hole tmp).toList original.toList →
      let result : MProd (Array T) ℕ := Id.run <|
        forIn nexts (⟨current, hole⟩ : MProd (Array T) ℕ)
          fun next state =>
            pure (.yield
              ⟨state.fst.set! state.snd state.fst[next]!, next⟩)
      List.Perm
        (result.fst.set! result.snd tmp).toList
        original.toList := by
  intro nexts
  induction nexts with
  | nil =>
      intro current hole tmp original _ _ hperm
      simpa using hperm
  | cons next nexts ih =>
      intro current hole tmp original hhole hnexts hperm
      simp only [List.forIn_cons]
      apply ih
      ·
        simpa [Array.set!] using hnexts next (by simp)
      ·
        intro j hj
        simpa [Array.set!] using hnexts j (by simp [hj])
      ·
        rw [cycle_repair_eq_swp current tmp hole next hhole
          (hnexts next (by simp))]
        exact (swp_perm (current.set! hole tmp) hole next
          (by simpa [Array.set!] using hhole)
          (by
            simpa [Array.set!] using hnexts next (by simp))).trans
          hperm

private theorem cycle_set_perm
    (a : Array T) (hole : ℕ) (nexts : List ℕ)
    (hhole : hole < a.size)
    (hnexts : ∀ j ∈ nexts, j < a.size) :
    let tmp := a[hole]!
    let result : MProd (Array T) ℕ := Id.run <|
      forIn nexts (⟨a, hole⟩ : MProd (Array T) ℕ)
        fun next state =>
          pure (.yield
            ⟨state.fst.set! state.snd state.fst[next]!, next⟩)
    List.Perm
      (result.fst.set! result.snd tmp).toList
      a.toList := by
  apply cycle_set_loop_perm nexts a hole a[hole]! a hhole hnexts
  rw [show a.set! hole a[hole]! = a by
    apply Array.toList_inj.mp
    simpa [Array.set!, hhole] using
      (List.set_getElem_self (as := a.toList) (i := hole)
        (by simpa using hhole))]

private theorem alternating_set_loop_perm
    (n : ℕ) (left right : ℕ → ℕ) :
    ∀ (indices : List ℕ) (a' : Array T) (sl sr : ℕ)
      (tmp : T) (original : Array T),
      a'.size = n →
      (∀ k, k ≤ indices.length → left (sl + k) < n) →
      (∀ k, k ≤ indices.length → right (sr + k) < n) →
      List.Perm (a'.set! (right sr) tmp).toList
        original.toList →
      let result : ℕ × ℕ × Array T := Id.run <|
        forIn indices (sl, sr, a') fun _ state =>
          let sl' := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left sl']!
          let sr' := state.2.1 + 1
          let afterRight := afterLeft.set! (left sl')
            afterLeft[right sr']!
          pure (.yield (sl', sr', afterRight))
      List.Perm
        (result.2.2.set! (right result.2.1) tmp).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro a' sl sr tmp original _ _ _ hperm
      simpa using hperm
  | cons index indices ih =>
      intro a' sl sr tmp original hsize hleft hright hperm
      simp only [List.forIn_cons]
      let sl' := sl + 1
      let afterLeft := a'.set! (right sr) a'[left sl']!
      let sr' := sr + 1
      let afterRight := afterLeft.set! (left sl')
        afterLeft[right sr']!
      apply ih afterRight sl' sr' tmp original
      · simp [afterRight, afterLeft, hsize]
      ·
        intro k hk
        have hb := hleft (k + 1) (by simp; omega)
        simpa [sl', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hb
      ·
        intro k hk
        have hb := hright (k + 1) (by simp; omega)
        simpa [sr', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hb
      ·
        have hrightOld : right sr < a'.size := by
          simpa [hsize] using hright 0 (by simp)
        have hleftNew : left sl' < a'.size := by
          simpa [sl', hsize] using hleft 1 (by simp)
        have hrightNew : right sr' < afterLeft.size := by
          simpa [sr', afterLeft, Array.set!, hsize] using
            hright 1 (by simp)
        have hleftAfter : left sl' < afterLeft.size := by
          simpa [sl', afterLeft, Array.set!, hsize] using
            hleft 1 (by simp)
        have hpLeft :
            List.Perm (afterLeft.set! (left sl') tmp).toList
              original.toList := by
          rw [cycle_repair_eq_swp a' tmp (right sr) (left sl')
            hrightOld hleftNew]
          exact (swp_perm (a'.set! (right sr) tmp)
            (right sr) (left sl')
            (by simpa [Array.set!] using hrightOld)
            (by simpa [Array.set!] using hleftNew)).trans hperm
        rw [cycle_repair_eq_swp afterLeft tmp (left sl')
          (right sr') hleftAfter hrightNew]
        exact (swp_perm (afterLeft.set! (left sl') tmp)
          (left sl') (right sr')
          (by simpa [Array.set!] using hleftAfter)
          (by simpa [Array.set!] using hrightNew)).trans hpLeft

private def CycleStateInvariant
    (arraySize : ℕ) (left right : ℕ → ℕ)
    (sl sr count step : ℕ) (leftGood rightGood : T → Prop)
    (state : ℕ × ℕ × Array T) : Prop :=
  state.1 = sl + step ∧ state.2.1 = sr + step ∧
    state.2.2.size = arraySize ∧
    (∀ index, index ≤ step → index < count →
      rightGood state.2.2[left (sl + index)]!) ∧
    (∀ index, index < step →
      leftGood state.2.2[right (sr + index)]!) ∧
    (∀ index, step < index → index < count →
      leftGood state.2.2[left (sl + index)]!) ∧
    (∀ index, step ≤ index → index < count →
      rightGood state.2.2[right (sr + index)]!)

private theorem cycleStateInvariant_initial
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count : ℕ) (leftGood rightGood : T → Prop)
    (hcount : 0 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j))
    (hleftGood : ∀ index, index < count →
      leftGood array[left (sl + index)]!)
    (hrightGood : ∀ index, index < count →
      rightGood array[right (sr + index)]!) :
    CycleStateInvariant array.size left right sl sr count 0
      leftGood rightGood
      (sl, sr, array.set! (left sl) array[right sr]!) := by
  unfold CycleStateInvariant
  have hleftZero := hleftBound 0 hcount
  refine ⟨rfl, rfl, by simp [Array.set!], ?_, ?_, ?_, ?_⟩
  · intro index hindexZero hindexCount
    have hindex : index = 0 := by omega
    subst index
    simp only [Nat.add_zero]
    rw [set!_get! array (left sl) (left sl) array[right sr]!
      hleftZero, if_pos rfl]
    simpa using hrightGood 0 hcount
  · intro index hindex
    omega
  · intro index hindexPositive hindexCount
    rw [set!_get! array (left sl) (left (sl + index))
      array[right sr]! hleftZero, if_neg]
    · exact hleftGood index hindexCount
    · intro heq
      have := hleftInjective 0 hcount index hindexCount
        (by simpa using heq.symm)
      omega
  · intro index hindexZero hindexCount
    rw [set!_get! array (left sl) (right (sr + index))
      array[right sr]! hleftZero, if_neg]
    · exact hrightGood index hindexCount
    · exact Ne.symm (hcross 0 hcount index hindexCount)

private theorem cycleStateInvariant_step
    (arraySize : ℕ) (left right : ℕ → ℕ)
    (sl sr count step : ℕ) (leftGood rightGood : T → Prop)
    (current : Array T)
    (hnext : step + 1 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < arraySize)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < arraySize)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hrightInjective : ∀ i, i < count → ∀ j, j < count →
      right (sr + i) = right (sr + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j))
    (hinvariant : CycleStateInvariant arraySize left right sl sr count step
      leftGood rightGood (sl + step, sr + step, current)) :
    let nextStep := step + 1
    let afterLeft := current.set! (right (sr + step))
      current[left (sl + nextStep)]!
    let afterRight := afterLeft.set! (left (sl + nextStep))
      afterLeft[right (sr + nextStep)]!
    CycleStateInvariant arraySize left right sl sr count nextStep
      leftGood rightGood
      (sl + nextStep, sr + nextStep, afterRight) := by
  rcases hinvariant with
    ⟨_, _, hsize, hleftDone, hrightDone, hleftFuture, hrightFuture⟩
  let nextStep := step + 1
  let targetRight := right (sr + step)
  let targetLeft := left (sl + nextStep)
  let sourceLeft := left (sl + nextStep)
  let sourceRight := right (sr + nextStep)
  let afterLeft := current.set! targetRight current[sourceLeft]!
  let afterRight := afterLeft.set! targetLeft afterLeft[sourceRight]!
  have htargetRight : targetRight < current.size := by
    rw [hsize]
    exact hrightBound step (by omega)
  have htargetLeft : targetLeft < afterLeft.size := by
    simp only [afterLeft, Array.set!, Array.size_setIfInBounds]
    rw [hsize]
    exact hleftBound nextStep hnext
  have hsourceRightNeTargetRight : sourceRight ≠ targetRight := by
    intro heq
    have := hrightInjective nextStep hnext step (by omega) (by
      simpa [sourceRight, targetRight] using heq)
    omega
  have hsourceRightValue : afterLeft[sourceRight]! = current[sourceRight]! := by
    simp only [afterLeft]
    rw [set!_get! current targetRight sourceRight
      current[sourceLeft]! htargetRight, if_neg hsourceRightNeTargetRight]
  unfold CycleStateInvariant
  refine ⟨rfl, rfl, by simp [hsize], ?_, ?_, ?_, ?_⟩
  · intro index hindexDone hindexCount
    rw [set!_get! afterLeft targetLeft
      (left (sl + index)) afterLeft[sourceRight]! htargetLeft]
    by_cases hnew : index = nextStep
    · subst index
      rw [if_pos rfl, hsourceRightValue]
      exact hrightFuture nextStep (by omega) hnext
    · rw [if_neg (by
          intro heq
          exact hnew (hleftInjective index hindexCount nextStep hnext
            (by simpa [targetLeft] using heq)))]
      simp only [afterLeft]
      rw [set!_get! current targetRight
        (left (sl + index)) current[sourceLeft]! htargetRight,
        if_neg (hcross index hindexCount step (by omega))]
      exact hleftDone index (by omega) hindexCount
  · intro index hindexDone
    have hindexCount : index < count := hindexDone.trans_le (by omega)
    rw [set!_get! afterLeft targetLeft
      (right (sr + index)) afterLeft[sourceRight]! htargetLeft,
      if_neg (Ne.symm (hcross nextStep hnext index hindexCount))]
    simp only [afterLeft]
    rw [set!_get! current targetRight
      (right (sr + index)) current[sourceLeft]! htargetRight]
    by_cases hnew : index = step
    · subst index
      rw [if_pos rfl]
      exact hleftFuture nextStep (by omega) hnext
    · rw [if_neg (by
          intro heq
          exact hnew (hrightInjective index hindexCount step (by omega)
            (by simpa [targetRight] using heq)))]
      exact hrightDone index (by omega)
  · intro index hindexFuture hindexCount
    rw [set!_get! afterLeft targetLeft
      (left (sl + index)) afterLeft[sourceRight]! htargetLeft,
      if_neg (by
        intro heq
        have := hleftInjective index hindexCount nextStep hnext
          (by simpa [targetLeft] using heq)
        omega)]
    simp only [afterLeft]
    rw [set!_get! current targetRight
      (left (sl + index)) current[sourceLeft]! htargetRight,
      if_neg (hcross index hindexCount step (by omega))]
    exact hleftFuture index (by omega) hindexCount
  · intro index hindexFuture hindexCount
    rw [set!_get! afterLeft targetLeft
      (right (sr + index)) afterLeft[sourceRight]! htargetLeft,
      if_neg (Ne.symm (hcross nextStep hnext index hindexCount))]
    simp only [afterLeft]
    rw [set!_get! current targetRight
      (right (sr + index)) current[sourceLeft]! htargetRight,
      if_neg (by
        intro heq
        have := hrightInjective index hindexCount step (by omega)
          (by simpa [targetRight] using heq)
        omega)]
    exact hrightFuture index (by omega) hindexCount

private theorem cycleStateInvariant_loop
    (arraySize : ℕ) (left right : ℕ → ℕ)
    (sl sr count : ℕ) (leftGood rightGood : T → Prop)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < arraySize)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < arraySize)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hrightInjective : ∀ i, i < count → ∀ j, j < count →
      right (sr + i) = right (sr + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j)) :
    ∀ (indices : List ℕ) (step : ℕ) (current : Array T),
      step + indices.length = count - 1 →
      CycleStateInvariant arraySize left right sl sr count step
        leftGood rightGood (sl + step, sr + step, current) →
      CycleStateInvariant arraySize left right sl sr count
        (step + indices.length) leftGood rightGood
        (Id.run <| forIn indices (sl + step, sr + step, current)
          fun _ state =>
            let nextStepLeft := state.1 + 1
            let afterLeft := state.2.2.set! (right state.2.1)
              state.2.2[left nextStepLeft]!
            let nextStepRight := state.2.1 + 1
            let afterRight := afterLeft.set! (left nextStepLeft)
              afterLeft[right nextStepRight]!
            pure (.yield (nextStepLeft, nextStepRight, afterRight))) := by
  intro indices
  induction indices with
  | nil =>
      intro step current hsteps hinvariant
      simpa using hinvariant
  | cons index indices inductionHypothesis =>
      intro step current hsteps hinvariant
      have hnext : step + 1 < count := by
        simp only [List.length_cons] at hsteps
        omega
      have hstep := cycleStateInvariant_step arraySize left right
        sl sr count step leftGood rightGood current hnext
        hleftBound hrightBound hleftInjective hrightInjective hcross
        hinvariant
      let afterLeft := current.set! (right (sr + step))
        current[left (sl + (step + 1))]!
      let afterRight := afterLeft.set! (left (sl + (step + 1)))
        afterLeft[right (sr + (step + 1))]!
      change CycleStateInvariant arraySize left right sl sr count
          (step + 1) leftGood rightGood
          (sl + (step + 1), sr + (step + 1), afterRight) at hstep
      simp only [List.forIn_cons, pure_bind]
      have hrest := inductionHypothesis (step + 1) afterRight
        (by
          simp only [List.length_cons] at hsteps
          omega)
        hstep
      simpa [afterLeft, afterRight, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrest

private theorem block_cycle_classifies
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count : ℕ) (leftGood rightGood : T → Prop)
    (hcount : 0 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < array.size)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hrightInjective : ∀ i, i < count → ∀ j, j < count →
      right (sr + i) = right (sr + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j))
    (hleftGood : ∀ index, index < count →
      leftGood array[left (sl + index)]!)
    (hrightGood : ∀ index, index < count →
      rightGood array[right (sr + index)]!) :
    let tmp := array[left sl]!
    let afterFirst := array.set! (left sl) array[right sr]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (sl, sr, afterFirst) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
    let output := result.2.2.set! (right result.2.1) tmp
    (∀ index, index < count →
      rightGood output[left (sl + index)]!) ∧
    (∀ index, index < count →
      leftGood output[right (sr + index)]!) := by
  let tmp := array[left sl]!
  let afterFirst := array.set! (left sl) array[right sr]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (sl, sr, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  have hinitial := cycleStateInvariant_initial array left right sl sr count
    leftGood rightGood hcount hleftBound hleftInjective hcross
    hleftGood hrightGood
  have hloop := cycleStateInvariant_loop array.size left right sl sr count
    leftGood rightGood hleftBound hrightBound hleftInjective
    hrightInjective hcross (List.range' 0 (count - 1)) 0 afterFirst
    (by simp) (by simpa [afterFirst] using hinitial)
  have hloopResult : CycleStateInvariant array.size left right sl sr count
      (count - 1) leftGood rightGood result := by
    simpa only [result, Nat.zero_add, List.length_range'] using hloop
  rcases hloopResult with
    ⟨hresultLeft, hresultRight, hresultSize,
      hleftDone, hrightDone, hleftFuture, hrightFuture⟩
  have hlast : count - 1 < count := by omega
  have htarget : right result.2.1 < result.2.2.size := by
    rw [hresultRight, hresultSize]
    exact hrightBound (count - 1) hlast
  let output := result.2.2.set! (right result.2.1) tmp
  refine ⟨?_, ?_⟩
  · intro index hindex
    rw [set!_get! result.2.2 (right result.2.1)
      (left (sl + index)) tmp htarget, if_neg]
    · exact hleftDone index (by omega) hindex
    · rw [hresultRight]
      exact hcross index hindex (count - 1) hlast
  · intro index hindex
    rw [set!_get! result.2.2 (right result.2.1)
      (right (sr + index)) tmp htarget]
    by_cases hlastIndex : index = count - 1
    · subst index
      rw [hresultRight, if_pos rfl]
      simpa [tmp] using hleftGood 0 hcount
    · rw [hresultRight, if_neg (by
          intro heq
          exact hlastIndex (hrightInjective index hindex
            (count - 1) hlast heq))]
      exact hrightDone index (by omega)

private theorem cycle_loop_outside
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count position : ℕ)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < array.size)
    (houtLeft : ∀ index, index < count →
      position ≠ left (sl + index))
    (houtRight : ∀ index, index < count →
      position ≠ right (sr + index)) :
    ∀ (indices : List ℕ) (step : ℕ) (current : Array T),
      step + indices.length = count - 1 →
      current.size = array.size → current[position]! = array[position]! →
      let result : ℕ × ℕ × Array T := Id.run <|
        forIn indices (sl + step, sr + step, current) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
      result.2.2[position]! = array[position]! := by
  intro indices
  induction indices with
  | nil =>
      intro step current hsteps hsize hvalue
      simpa using hvalue
  | cons index indices inductionHypothesis =>
      intro step current hsteps hsize hvalue
      have hnext : step + 1 < count := by
        simp only [List.length_cons] at hsteps
        omega
      let afterLeft := current.set! (right (sr + step))
        current[left (sl + (step + 1))]!
      let afterRight := afterLeft.set! (left (sl + (step + 1)))
        afterLeft[right (sr + (step + 1))]!
      have htargetRight : right (sr + step) < current.size := by
        rw [hsize]
        exact hrightBound step (by omega)
      have htargetLeft : left (sl + (step + 1)) < afterLeft.size := by
        simp only [afterLeft, Array.set!, Array.size_setIfInBounds]
        rw [hsize]
        exact hleftBound (step + 1) hnext
      have hafterLeft : afterLeft[position]! = array[position]! := by
        simp only [afterLeft]
        rw [set!_get! current (right (sr + step)) position
          current[left (sl + (step + 1))]! htargetRight,
          if_neg (houtRight step (by omega)), hvalue]
      have hafterRight : afterRight[position]! = array[position]! := by
        simp only [afterRight]
        rw [set!_get! afterLeft (left (sl + (step + 1))) position
          afterLeft[right (sr + (step + 1))]! htargetLeft,
          if_neg (houtLeft (step + 1) hnext), hafterLeft]
      simp only [List.forIn_cons, pure_bind]
      have hrest := inductionHypothesis (step + 1) afterRight
        (by
          simp only [List.length_cons] at hsteps
          omega)
        (by simp [afterRight, afterLeft, hsize]) hafterRight
      simpa [afterLeft, afterRight, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrest

private theorem cycle_loop_shape
    (left right : ℕ → ℕ) (sl sr : ℕ) :
    ∀ (indices : List ℕ) (step : ℕ) (current : Array T),
      let result : ℕ × ℕ × Array T := Id.run <|
        forIn indices (sl + step, sr + step, current) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
      result.1 = sl + step + indices.length ∧
      result.2.1 = sr + step + indices.length ∧
      result.2.2.size = current.size := by
  intro indices
  induction indices with
  | nil => simp
  | cons index indices inductionHypothesis =>
      intro step current
      let afterLeft := current.set! (right (sr + step))
        current[left (sl + (step + 1))]!
      let afterRight := afterLeft.set! (left (sl + (step + 1)))
        afterLeft[right (sr + (step + 1))]!
      simp only [List.forIn_cons, pure_bind]
      have hrest := inductionHypothesis (step + 1) afterRight
      simpa [afterLeft, afterRight, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrest

private theorem block_cycle_outside
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count position : ℕ) (hcount : 0 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < array.size)
    (houtLeft : ∀ index, index < count →
      position ≠ left (sl + index))
    (houtRight : ∀ index, index < count →
      position ≠ right (sr + index)) :
    let tmp := array[left sl]!
    let afterFirst := array.set! (left sl) array[right sr]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (sl, sr, afterFirst) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
    let output := result.2.2.set! (right result.2.1) tmp
    output[position]! = array[position]! := by
  let tmp := array[left sl]!
  let afterFirst := array.set! (left sl) array[right sr]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (sl, sr, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  have hleftZero := hleftBound 0 hcount
  have hafterFirst : afterFirst[position]! = array[position]! := by
    simp only [afterFirst]
    rw [set!_get! array (left sl) position array[right sr]!
      hleftZero, if_neg (by simpa using houtLeft 0 hcount)]
  have hloop := cycle_loop_outside array left right sl sr count position
    hleftBound hrightBound houtLeft houtRight
    (List.range' 0 (count - 1)) 0 afterFirst
    (by simp) (by simp [afterFirst]) hafterFirst
  have hresultValue : result.2.2[position]! = array[position]! := by
    simpa only [result, Nat.zero_add] using hloop
  have hshape := cycle_loop_shape (T := T) left right sl sr
    (List.range' 0 (count - 1)) 0 afterFirst
  have hresultRight : result.2.1 = sr + (count - 1) := by
    simpa only [result, Nat.zero_add, List.length_range'] using hshape.2.1
  have hresultSize : result.2.2.size = array.size := by
    simpa [result, afterFirst] using hshape.2.2
  have htarget : right result.2.1 < result.2.2.size := by
    rw [hresultRight, hresultSize]
    exact hrightBound (count - 1) (by omega)
  show (result.2.2.set! (right result.2.1) tmp)[position]! = array[position]!
  rw [set!_get! result.2.2 (right result.2.1) position tmp htarget,
    if_neg]
  · exact hresultValue
  · rw [hresultRight]
    exact houtRight (count - 1) (by omega)

private theorem block_cycle_perm
    (a : Array T) (left right : ℕ → ℕ)
    (sl sr count : ℕ)
    (hleft : ∀ k, k ≤ count - 1 →
      left (sl + k) < a.size)
    (hright : ∀ k, k ≤ count - 1 →
      right (sr + k) < a.size) :
    let tmp := a[left sl]!
    let afterFirst := a.set! (left sl) a[right sr]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (sl, sr, afterFirst) fun _ state =>
          let sl' := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left sl']!
          let sr' := state.2.1 + 1
          let afterRight := afterLeft.set! (left sl')
            afterLeft[right sr']!
          pure (.yield (sl', sr', afterRight))
    List.Perm
      (result.2.2.set! (right result.2.1) tmp).toList
      a.toList := by
  let tmp := a[left sl]!
  let afterFirst := a.set! (left sl) a[right sr]!
  have hleftStart : left sl < a.size := by
    simpa using hleft 0 (by omega)
  have hrightStart : right sr < a.size := by
    simpa using hright 0 (by omega)
  have hpFirst :
      List.Perm (afterFirst.set! (right sr) tmp).toList
        a.toList := by
    rw [cycle_repair_eq_swp a tmp (left sl) (right sr)
      hleftStart hrightStart]
    have hself : a.set! (left sl) tmp = a := by
      apply Array.toList_inj.mp
      simpa [tmp, Array.set!, hleftStart] using
        (List.set_getElem_self (as := a.toList) (i := left sl)
          (by simpa using hleftStart))
    rw [hself]
    exact swp_perm a (left sl) (right sr)
      hleftStart hrightStart
  apply alternating_set_loop_perm a.size left right
    (List.range' 0 (count - 1)) afterFirst sl sr tmp a
    (by simp [afterFirst])
  · simpa using hleft
  · simpa using hright
  · exact hpFirst

private theorem scan_offsets_aux
    (block : ℕ) (keep : ℕ → Bool) :
    ∀ (indices : List ℕ) (endIdx : ℕ) (offsets : Array ℕ),
      endIdx + indices.length ≤ offsets.size →
      (∀ j, j < endIdx → offsets[j]! < block) →
      (∀ i ∈ indices, i < block) →
      let result : ℕ × Array ℕ := Id.run <|
        forIn indices (endIdx, offsets) fun i state =>
          let offsets' := state.2.set! state.1 i
          let endIdx' :=
            if keep i = true then state.1 + 1 else state.1
          pure (.yield (endIdx', offsets'))
      result.1 ≤ endIdx + indices.length ∧
        result.2.size = offsets.size ∧
        ∀ j, j < result.1 → result.2[j]! < block := by
  intro indices
  induction indices with
  | nil =>
      intro endIdx offsets _ hactive _
      exact ⟨by simp, rfl, hactive⟩
  | cons i indices ih =>
      intro endIdx offsets hcapacity hactive hindices
      simp only [List.forIn_cons]
      have hend : endIdx < offsets.size := by
        have : endIdx + 1 ≤ endIdx + (indices.length + 1) := by omega
        simpa only [List.length_cons] using
          this.trans hcapacity
      let offsets' := offsets.set! endIdx i
      let endIdx' :=
        if keep i = true then endIdx + 1 else endIdx
      have hsize : offsets'.size = offsets.size := by
        simp [offsets']
      have hendStep : endIdx' ≤ endIdx + 1 := by
        by_cases hkeep : keep i = true <;>
          simp [endIdx', hkeep]
      have hcapacity' :
          endIdx' + indices.length ≤ offsets'.size := by
        rw [hsize]
        simp only [List.length_cons] at hcapacity
        omega
      have hactive' :
          ∀ j, j < endIdx' → offsets'[j]! < block := by
        intro j hj
        by_cases hkeep : keep i = true
        · have hjle : j ≤ endIdx := by
            simp [endIdx', hkeep] at hj
            omega
          by_cases hjeq : j = endIdx
          · subst j
            have hi : i < block :=
              hindices i (by simp)
            simpa [offsets', Array.set!, hend] using hi
          ·
            have hjold : j < endIdx := by omega
            have hjbound := hactive j hjold
            have hjsize : j < offsets.size := hjold.trans hend
            have hne' : endIdx ≠ j := Ne.symm hjeq
            simpa [offsets', Array.set!, hjsize, hne'] using
              hjbound
        · have hjold : j < endIdx := by
            simpa [endIdx', hkeep] using hj
          have hjbound := hactive j hjold
          have hne : j ≠ endIdx := by omega
          have hjsize : j < offsets.size := hjold.trans hend
          have hne' : endIdx ≠ j := Ne.symm hne
          simpa [offsets', Array.set!, hjsize, hne'] using
            hjbound
      have hrest : ∀ k ∈ indices, k < block := by
        intro k hk
        exact hindices k (by simp [hk])
      have hout := ih endIdx' offsets' hcapacity' hactive' hrest
      have htotal :
          (Id.run <|
            forIn indices (endIdx', offsets') fun i state =>
              let offsets' := state.2.set! state.1 i
              let endIdx' :=
                if keep i = true then state.1 + 1 else state.1
              pure (.yield (endIdx', offsets'))).1 ≤
            endIdx + (i :: indices).length := by
        calc
          _ ≤ endIdx' + indices.length := hout.1
          _ ≤ endIdx + (i :: indices).length := by
            simp only [List.length_cons]
            omega
      simpa [offsets', endIdx'] using And.intro htotal hout.2

omit [Inhabited T] in
private theorem take_set!_self_succ
    {U : Type} (array : Array U) (index : ℕ) (value : U)
    (hindex : index < array.size) :
    (array.set! index value).toList.take (index + 1) =
      array.toList.take index ++ [value] := by
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [List.set_eq_take_cons_drop value (by simpa using hindex),
    List.take_append]
  have hlength : (array.toList.take index).length = index := by
    simp
    omega
  simp [hlength]

omit [Inhabited T] in
private theorem scan_offsets_prefix
    (keep : ℕ → Bool) :
    ∀ (indices : List ℕ) (endIdx : ℕ) (offsets : Array ℕ),
      endIdx + indices.length ≤ offsets.size →
      let result : ℕ × Array ℕ := Id.run <|
        forIn indices (endIdx, offsets) fun i state =>
          let offsets' := state.2.set! state.1 i
          let endIdx' :=
            if keep i = true then state.1 + 1 else state.1
          pure (.yield (endIdx', offsets'))
      let kept := indices.filter (fun index => keep index = true)
      result.1 = endIdx + kept.length ∧
        result.2.toList.take result.1 =
          offsets.toList.take endIdx ++ kept := by
  intro indices
  induction indices with
  | nil =>
      intro endIdx offsets hcapacity
      simp
  | cons index indices inductionHypothesis =>
      intro endIdx offsets hcapacity
      simp only [List.forIn_cons, pure_bind]
      let offsets' := offsets.set! endIdx index
      by_cases hkeep : keep index = true
      · have hend : endIdx < offsets.size := by
          simp only [List.length_cons] at hcapacity
          omega
        have hrestCapacity : endIdx + 1 + indices.length ≤ offsets'.size := by
          simp [offsets']
          simp only [List.length_cons] at hcapacity
          omega
        have hrest := inductionHypothesis (endIdx + 1) offsets'
          hrestCapacity
        dsimp only at hrest
        dsimp only [offsets'] at hrest
        have hkeepBool : decide (keep index = true) = true := by
          simp [hkeep]
        rw [List.filter_cons]
        simp only [hkeepBool, if_true]
        simp only [hkeep, if_true]
        constructor
        · simp only [List.length_cons]
          omega
        · rw [hrest.2, take_set!_self_succ offsets endIdx index hend]
          simp only [List.append_assoc, List.singleton_append]
      · have hrestCapacity : endIdx + indices.length ≤ offsets'.size := by
          simp [offsets']
          simp only [List.length_cons] at hcapacity
          omega
        have hrest := inductionHypothesis endIdx offsets' hrestCapacity
        dsimp only at hrest
        dsimp only [offsets'] at hrest
        have hkeepBool : decide (keep index = true) ≠ true := by
          simp [hkeep]
        rw [List.filter_cons]
        simp only [hkeepBool]
        simp only [hkeep, Bool.false_eq_true, if_false]
        constructor
        · exact hrest.1
        · rw [hrest.2]
          simp [List.take_set_of_le]

private theorem scan_offsets_bounds
    (block : ℕ) (offsets : Array ℕ) (keep : ℕ → Bool)
    (hblock : block ≤ offsets.size) :
    let result : ℕ × Array ℕ := Id.run <|
      forIn (List.range' 0 block) (0, offsets) fun i state =>
        let offsets' := state.2.set! state.1 i
        let endIdx' :=
          if keep i = true then state.1 + 1 else state.1
        pure (.yield (endIdx', offsets'))
    result.1 ≤ block ∧
      result.2.size = offsets.size ∧
      ∀ j, j < result.1 → result.2[j]! < block := by
  have hout := scan_offsets_aux block keep
    (List.range' 0 block) 0 offsets
    (by simpa using hblock)
    (by simp)
    (by
      intro i hi
      simpa using List.mem_range'.mp hi)
  simpa only [List.length_range', Nat.zero_add] using hout

private theorem scanned_block_cycle_perm
    (a : Array T) (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR count : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblockL : blockL ≤ r - l)
    (hblockR : blockR ≤ r - l)
    (hstartL : startL ≤ endL)
    (hstartR : startR ≤ endR)
    (hcount : 0 < count)
    (hcountL : count ≤ endL - startL)
    (hcountR : count ≤ endR - startR)
    (hactiveL : ∀ j, j < endL →
      offsetsL[j]! < blockL)
    (hactiveR : ∀ j, j < endR →
      offsetsR[j]! < blockR) :
    let left := fun i => l + offsetsL[i]!
    let right := fun i => r - offsetsR[i]! - 1
    let tmp := a[left startL]!
    let afterFirst := a.set! (left startL) a[right startR]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (startL, startR, afterFirst) fun _ state =>
          let startL' := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left startL']!
          let startR' := state.2.1 + 1
          let afterRight := afterLeft.set! (left startL')
            afterLeft[right startR']!
          pure (.yield (startL', startR', afterRight))
    List.Perm
      (result.2.2.set! (right result.2.1) tmp).toList
      a.toList := by
  let left := fun (i : ℕ) => l + offsetsL[i]!
  let right := fun (i : ℕ) => r - offsetsR[i]! - 1
  apply block_cycle_perm a left right startL startR count
  · intro k hk
    have hidx : startL + k < endL := by omega
    have hoff : offsetsL[startL + k]! < blockL :=
      hactiveL (startL + k) hidx
    simp only [left]
    omega
  · intro k hk
    have hidx : startR + k < endR := by omega
    have hoff : offsetsR[startR + k]! < blockR :=
      hactiveR (startR + k) hidx
    simp only [right]
    omega

private def refreshOffsets
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) : ℕ × ℕ × Array ℕ :=
  if startIdx = endIdx then
    let result : ℕ × Array ℕ := Id.run <|
      forIn (List.range' 0 block) (0, offsets) fun i state =>
        let offsets' := state.2.set! state.1 i
        let endIdx' :=
          if keep i = true then state.1 + 1 else state.1
        pure (.yield (endIdx', offsets'))
    (0, result.1, result.2)
  else
    (startIdx, endIdx, offsets)

private theorem refreshOffsets_fresh_prefix
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) (hblock : block ≤ offsets.size)
    (hfresh : startIdx = endIdx) :
    let result := refreshOffsets block startIdx endIdx offsets keep
    let kept := (List.range block).filter
      (fun index => keep index = true)
    result.1 = 0 ∧ result.2.1 = kept.length ∧
      result.2.2.toList.take result.2.1 = kept := by
  simp only [refreshOffsets, hfresh, ↓reduceIte]
  have hscan := scan_offsets_prefix keep
    (List.range' 0 block) 0 offsets (by simpa using hblock)
  dsimp only at hscan
  have hrange : List.range' 0 block = List.range block := by
    simp [List.range'_eq_map_range]
  rw [hrange] at hscan
  refine ⟨trivial, ?_⟩
  rw [hrange]
  simpa only [Nat.zero_add, List.take_zero, List.nil_append] using hscan

private def OffsetScanExact
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) : Prop :=
  offsets.toList.extract startIdx endIdx =
    (List.range block).filter (fun index => keep index = true)

private theorem refreshOffsets_exact
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) (hblock : block ≤ offsets.size)
    (hpending : startIdx ≠ endIdx →
      OffsetScanExact block startIdx endIdx offsets keep) :
    let result := refreshOffsets block startIdx endIdx offsets keep
    OffsetScanExact block result.1 result.2.1 result.2.2 keep := by
  by_cases hfresh : startIdx = endIdx
  · have hfacts := refreshOffsets_fresh_prefix block startIdx endIdx
      offsets keep hblock hfresh
    let result := refreshOffsets block startIdx endIdx offsets keep
    change result.1 = 0 ∧
      result.2.1 = ((List.range block).filter
        (fun index => keep index = true)).length ∧
      result.2.2.toList.take result.2.1 =
        (List.range block).filter (fun index => keep index = true)
      at hfacts
    change OffsetScanExact block result.1 result.2.1 result.2.2 keep
    rw [hfacts.1, hfacts.2.1]
    simp only [OffsetScanExact, List.extract_eq_take_drop,
      List.drop_zero, Nat.sub_zero]
    simpa only [hfacts.2.1] using hfacts.2.2
  · simpa [refreshOffsets, hfresh] using hpending hfresh

private theorem offset_active_mem
    (offsets : Array ℕ) (startIdx endIdx index : ℕ)
    (hstart : startIdx ≤ index) (hend : index < endIdx)
    (hbound : endIdx ≤ offsets.size) :
    offsets[index]! ∈ offsets.toList.extract startIdx endIdx := by
  rw [List.extract_eq_take_drop]
  let position := index - startIdx
  have hposition : position <
      ((offsets.toList.drop startIdx).take
        (endIdx - startIdx)).length := by
    simp [position]
    omega
  have hmem := List.getElem_mem
    (l := (offsets.toList.drop startIdx).take (endIdx - startIdx))
    (n := position) hposition
  have hindex : index < offsets.size := hend.trans_le hbound
  have hvalue :
      ((offsets.toList.drop startIdx).take
        (endIdx - startIdx))[position] = offsets[index]! := by
    rw [getElem!_pos offsets index hindex]
    simp only [List.getElem_take, List.getElem_drop,
      Array.getElem_toList]
    congr
    simp [position]
    omega
  rw [hvalue] at hmem
  exact hmem

private theorem OffsetScanExact.mem_iff
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (offset : ℕ) :
    offset ∈ offsets.toList.extract startIdx endIdx ↔
      offset < block ∧ keep offset = true := by
  rw [hexact, List.mem_filter, List.mem_range]
  simp

private theorem OffsetScanExact.active
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hbound : endIdx ≤ offsets.size)
    (index : ℕ) (hstart : startIdx ≤ index) (hend : index < endIdx) :
    offsets[index]! < block ∧ keep offsets[index]! = true := by
  rw [← hexact.mem_iff]
  exact offset_active_mem offsets startIdx endIdx index
    hstart hend hbound

private theorem offset_active_get!
    (offsets : Array ℕ) (startIdx endIdx position : ℕ)
    (hposition : position < endIdx - startIdx)
    (hbound : endIdx ≤ offsets.size) :
    (offsets.toList.extract startIdx endIdx)[position]'(by
      simp [List.extract_eq_take_drop]
      omega) =
      offsets[startIdx + position]! := by
  have hindex : startIdx + position < offsets.size := by omega
  rw [getElem!_pos offsets (startIdx + position) hindex]
  simp only [List.extract_eq_take_drop, List.getElem_take,
    List.getElem_drop, Array.getElem_toList]

private theorem OffsetScanExact.injective
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hbound : endIdx ≤ offsets.size) :
    ∀ i, i < endIdx - startIdx → ∀ j, j < endIdx - startIdx →
      offsets[startIdx + i]! = offsets[startIdx + j]! → i = j := by
  intro i hi j hj hequal
  have hnodup : (offsets.toList.extract startIdx endIdx).Nodup := by
    rw [hexact]
    exact (List.nodup_range (n := block)).filter _
  rw [← offset_active_get! offsets startIdx endIdx i hi hbound,
    ← offset_active_get! offsets startIdx endIdx j hj hbound] at hequal
  exact hnodup.getElem_inj_iff.mp hequal

private theorem OffsetScanExact.nodup
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep) :
    (offsets.toList.extract startIdx endIdx).Nodup := by
  rw [hexact]
  exact (List.nodup_range (n := block)).filter _

omit [Inhabited T] in
private theorem List.extract_advance
    (items : List T) (start stop count : ℕ)
    (hstart : start ≤ stop) :
    items.extract (start + count) stop =
      (items.extract start stop).drop count := by
  have hstop : stop = start + (stop - start) := by omega
  rw [hstop]
  simp only [List.extract_eq_take_drop, List.drop_take,
    List.drop_drop]
  congr 1
  omega

omit [Inhabited T] in
private theorem List.extract_shrink
    (items : List T) (start stop : ℕ) (hstart : start < stop)
    (hstop : stop ≤ items.length) :
    items.extract start (stop - 1) =
      (items.extract start stop).dropLast := by
  have hlength : (items.extract start stop).length = stop - start := by
    simp [List.extract_eq_take_drop]
    omega
  rw [List.dropLast_eq_take, hlength]
  simp only [List.extract_eq_take_drop]
  rw [List.take_take, Nat.min_eq_left (by omega)]
  apply congrArg (fun count => (items.drop start).take count)
  omega

private theorem OffsetScanExact.mem_take_iff
    (block startIdx endIdx count : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hend : endIdx ≤ offsets.size)
    (hcount : count ≤ endIdx - startIdx) (offset : ℕ) :
    offset ∈ ((List.range block).filter
        (fun index => keep index = true)).take count ↔
      ∃ index, index < count ∧
        offset = offsets[startIdx + index]! := by
  let active := (List.range block).filter
    (fun index => keep index = true)
  have hactiveEq :
      active = offsets.toList.extract startIdx endIdx := by
    exact hexact.symm
  have hactiveLength : active.length = endIdx - startIdx := by
    rw [hactiveEq]
    simp [List.extract_eq_take_drop]
    omega
  constructor
  · intro hmem
    obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmem
    have hindexCount : index < count := by
      rw [List.length_take, hactiveLength,
        Nat.min_eq_left hcount] at hindex
      exact hindex
    have hindexRemaining : index < endIdx - startIdx :=
      hindexCount.trans_le hcount
    have hactiveValue :
        active[index]'(by omega) = offsets[startIdx + index]! := by
      have hvalue := offset_active_get! offsets startIdx endIdx index
        hindexRemaining hend
      simpa only [hactiveEq] using hvalue
    refine ⟨index, hindexCount, ?_⟩
    rw [← hvalue]
    simpa only [List.getElem_take] using hactiveValue
  · rintro ⟨index, hindexCount, rfl⟩
    have hindexRemaining : index < endIdx - startIdx :=
      hindexCount.trans_le hcount
    have hactiveValue :
        active[index]'(by omega) = offsets[startIdx + index]! := by
      have hvalue := offset_active_get! offsets startIdx endIdx index
        hindexRemaining hend
      simpa only [hactiveEq] using hvalue
    have hindexTake : index < (active.take count).length := by
      simp [hactiveLength, Nat.min_eq_left hcount]
      exact hindexCount
    have hmem := List.getElem_mem (l := active.take count)
      (n := index) hindexTake
    simpa only [List.getElem_take, hactiveValue] using hmem

private theorem OffsetScanExact.getLast
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hstart : startIdx < endIdx) (hend : endIdx ≤ offsets.size) :
    let active := (List.range block).filter
      (fun index => keep index = true)
    active.getLast (by
      intro heq
      have := congrArg List.length heq
      simp only [List.length_nil] at this
      have hlength : active.length = endIdx - startIdx := by
        have hactiveEq : active = offsets.toList.extract startIdx endIdx :=
          hexact.symm
        rw [hactiveEq]
        simp [List.extract_eq_take_drop]
        omega
      omega) = offsets[endIdx - 1]! := by
  let active := (List.range block).filter
    (fun index => keep index = true)
  have hactiveEq : active = offsets.toList.extract startIdx endIdx :=
    hexact.symm
  have hlength : active.length = endIdx - startIdx := by
    rw [hactiveEq]
    simp [List.extract_eq_take_drop]
    omega
  have hremaining : endIdx - startIdx - 1 < endIdx - startIdx := by omega
  have hvalue := offset_active_get! offsets startIdx endIdx
    (endIdx - startIdx - 1) hremaining hend
  show active.getLast _ = offsets[endIdx - 1]!
  rw [List.getLast_eq_getElem]
  have hindex : startIdx + (endIdx - startIdx - 1) = endIdx - 1 := by
    omega
  have hextractLength :
      (offsets.toList.extract startIdx endIdx).length =
        endIdx - startIdx := by
    rw [← hactiveEq]
    exact hlength
  simpa only [hactiveEq, hextractLength, hindex] using hvalue

private theorem OffsetScanExact.gt_last_false
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hstart : startIdx < endIdx) (hend : endIdx ≤ offsets.size)
    (offset : ℕ) (hoffset : offset < block)
    (hgt : offsets[endIdx - 1]! < offset) : keep offset = false := by
  let active := (List.range block).filter
    (fun index => keep index = true)
  have hsorted : active.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have hnonempty : active ≠ [] := by
    intro heq
    have hlength : active.length = endIdx - startIdx := by
      have hactiveEq : active =
          offsets.toList.extract startIdx endIdx := hexact.symm
      rw [hactiveEq]
      simp [List.extract_eq_take_drop]
      omega
    rw [heq] at hlength
    simp at hlength
    omega
  have hlast : active.getLast hnonempty = offsets[endIdx - 1]! := by
    simpa only [active] using OffsetScanExact.getLast
      block startIdx endIdx offsets keep hexact hstart hend
  by_cases hkeep : keep offset = true
  · have hmem : offset ∈ active := by
      simp [active, hoffset, hkeep]
    have hne : offset ≠ active.getLast hnonempty := by
      rw [hlast]
      omega
    have hdrop : offset ∈ active.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hmem hne
    have hlt := hsorted.pairwise.rel_dropLast_getLast hdrop
    rw [hlast] at hlt
    omega
  · exact Bool.eq_false_of_not_eq_true hkeep

omit [Inhabited T] in
private theorem List.mem_drop_iff_of_nodup
    (items : List T) (count : ℕ) (item : T)
    (hnodup : items.Nodup) :
    item ∈ items.drop count ↔
      item ∈ items ∧ item ∉ items.take count := by
  constructor
  · intro hdrop
    refine ⟨List.mem_of_mem_drop hdrop, ?_⟩
    intro htake
    exact (List.disjoint_take_drop hnodup (m := count)
      (n := count) le_rfl) htake hdrop
  · rintro ⟨hmem, hnotTake⟩
    rw [← List.take_append_drop count items] at hmem
    rcases List.mem_append.mp hmem with htake | hdrop
    · exact (hnotTake htake).elim
    · exact hdrop

private theorem OffsetScanExact.consume
    (block startIdx endIdx count : ℕ) (offsets : Array ℕ)
    (before after : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets before)
    (hstart : startIdx ≤ endIdx) (hend : endIdx ≤ offsets.size)
    (hcount : count ≤ endIdx - startIdx)
    (hconsumed : ∀ index, index < count →
      after offsets[startIdx + index]! = false)
    (houtside : ∀ offset, offset < block →
      (∀ index, index < count →
        offset ≠ offsets[startIdx + index]!) →
      after offset = before offset) :
    OffsetScanExact block (startIdx + count) endIdx offsets after := by
  let oldActive := (List.range block).filter
    (fun index => before index = true)
  let newActive := (List.range block).filter
    (fun index => after index = true)
  have holdNodup : oldActive.Nodup := by
    exact (List.nodup_range (n := block)).filter _
  have holdSorted : oldActive.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have hnewSorted : newActive.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have htailSorted : (oldActive.drop count).SortedLT :=
    holdSorted.pairwise.drop.sortedLT
  have htailEq : oldActive.drop count = newActive := by
    apply htailSorted.eq_of_mem_iff hnewSorted
    intro offset
    rw [List.mem_drop_iff_of_nodup oldActive count offset holdNodup]
    change
      (offset ∈ (List.range block).filter
          (fun index => before index = true) ∧
        offset ∉ ((List.range block).filter
          (fun index => before index = true)).take count) ↔
      offset ∈ (List.range block).filter
        (fun index => after index = true)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hoffset, hbefore⟩, hnotConsumed⟩
      have hnotAddress : ∀ index, index < count →
          offset ≠ offsets[startIdx + index]! := by
        intro index hindex heq
        apply hnotConsumed
        rw [OffsetScanExact.mem_take_iff block startIdx endIdx count
          offsets before hexact hend hcount offset]
        exact ⟨index, hindex, heq⟩
      exact ⟨hoffset, by rw [houtside offset hoffset hnotAddress, hbefore]⟩
    · rintro ⟨hoffset, hafter⟩
      have hnotAddress : ∀ index, index < count →
          offset ≠ offsets[startIdx + index]! := by
        intro index hindex heq
        have := hconsumed index hindex
        rw [← heq, hafter] at this
        contradiction
      have hnotConsumed :
          offset ∉ ((List.range block).filter
            (fun index => before index = true)).take count := by
        rw [OffsetScanExact.mem_take_iff block startIdx endIdx count
          offsets before hexact hend hcount offset]
        rintro ⟨index, hindex, heq⟩
        exact hnotAddress index hindex heq
      refine ⟨⟨hoffset, ?_⟩, hnotConsumed⟩
      rw [← houtside offset hoffset hnotAddress]
      exact hafter
  rw [OffsetScanExact, List.extract_advance offsets.toList
    startIdx endIdx count hstart, hexact]
  exact htailEq

private theorem OffsetScanExact.shrinkLast
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (before after : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets before)
    (hstart : startIdx < endIdx) (hend : endIdx ≤ offsets.size)
    (hlast : offsets[endIdx - 1]! < block - 1 →
      after offsets[endIdx - 1]! = false)
    (houtside : ∀ offset, offset < block - 1 →
      offset ≠ offsets[endIdx - 1]! →
      after offset = before offset) :
    OffsetScanExact (block - 1) startIdx (endIdx - 1) offsets after := by
  let oldActive := (List.range block).filter
    (fun offset => before offset = true)
  let newActive := (List.range (block - 1)).filter
    (fun offset => after offset = true)
  have holdSorted : oldActive.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have hnewSorted : newActive.SortedLT :=
    ((List.sortedLT_range (block - 1)).pairwise.filter _).sortedLT
  have holdNonempty : oldActive ≠ [] := by
    intro heq
    have hlength : oldActive.length = endIdx - startIdx := by
      have hactiveEq : oldActive =
          offsets.toList.extract startIdx endIdx := hexact.symm
      rw [hactiveEq]
      simp [List.extract_eq_take_drop]
      omega
    rw [heq] at hlength
    simp at hlength
    omega
  have hgetLast : oldActive.getLast holdNonempty = offsets[endIdx - 1]! := by
    simpa only [oldActive] using OffsetScanExact.getLast
      block startIdx endIdx offsets before hexact hstart hend
  have hlastActive := OffsetScanExact.active block startIdx endIdx offsets
    before hexact hend (endIdx - 1) (by omega) (by omega)
  have htailSorted : oldActive.dropLast.SortedLT := by
    rw [List.dropLast_eq_take]
    exact holdSorted.pairwise.take.sortedLT
  have htailEq : oldActive.dropLast = newActive := by
    apply htailSorted.eq_of_mem_iff hnewSorted
    intro offset
    change
      (offset ∈ ((List.range block).filter
        (fun offset => before offset = true)).dropLast) ↔
      offset ∈ (List.range (block - 1)).filter
        (fun offset => after offset = true)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro hmem
      have hbeforeMem := List.mem_of_mem_dropLast hmem
      have hbefore : before offset = true := by
        simpa [oldActive] using (List.mem_filter.mp hbeforeMem).2
      have hoffsetLast : offset < offsets[endIdx - 1]! := by
        have hrel := holdSorted.pairwise.rel_dropLast_getLast hmem
        simpa only [hgetLast] using hrel
      have hoffset : offset < block - 1 := by omega
      have hne : offset ≠ offsets[endIdx - 1]! := by omega
      exact ⟨hoffset, by rw [houtside offset hoffset hne, hbefore]⟩
    · rintro ⟨hoffset, hafter⟩
      have hne : offset ≠ offsets[endIdx - 1]! := by
        intro heq
        have hlastFalse := hlast (by omega)
        rw [← heq, hafter] at hlastFalse
        contradiction
      have hbefore : before offset = true := by
        rw [← houtside offset hoffset hne]
        exact hafter
      have hmem : offset ∈ oldActive := by
        simp [oldActive, show offset < block by omega, hbefore]
      apply List.mem_dropLast_of_mem_of_ne_getLast hmem
      simpa only [hgetLast] using hne
  rw [OffsetScanExact, List.extract_shrink offsets.toList
    startIdx endIdx hstart hend, hexact]
  exact htailEq

private theorem OffsetScanExact.exhausted
    (block index : ℕ) (offsets : Array ℕ) (keep : ℕ → Bool)
    (hexact : OffsetScanExact block index index offsets keep) :
    ∀ offset, offset < block → keep offset = false := by
  have hnone : (List.range block).filter
      (fun offset => keep offset = true) = [] := by
    rw [← hexact]
    simp [List.extract_eq_take_drop]
  intro offset hoffset
  by_cases hkeep : keep offset = true
  · have hmem : offset ∈ (List.range block).filter
        (fun offset => keep offset = true) := by
      simp [hoffset, hkeep]
    rw [hnone] at hmem
    simp at hmem
  · exact Bool.eq_false_of_not_eq_true hkeep

private theorem exhausted_left_block_rangeAll
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (l block index : ℕ) (offsets : Array ℕ)
    (hexact : OffsetScanExact block index index offsets
      (fun offset => !isLess array[l + offset]! pivot)) :
    RangeAll array l (l + block)
      (fun item => isLess item pivot = true) := by
  intro position hposition hstop
  let offset := position - l
  have hoffset : offset < block := by omega
  have haddress : l + offset = position := by omega
  have hgood := OffsetScanExact.exhausted block index offsets
    (fun offset => !isLess array[l + offset]! pivot) hexact
    offset hoffset
  have hgood' : (!isLess array[l + offset]! pivot) = false := by
    simpa only using hgood
  rw [haddress] at hgood'
  simpa using hgood'

private theorem exhausted_right_block_rangeAll
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (r block index : ℕ) (offsets : Array ℕ)
    (hblock : block ≤ r)
    (hexact : OffsetScanExact block index index offsets
      (fun offset => isLess array[r - 1 - offset]! pivot)) :
    RangeAll array (r - block) r
      (fun item => isLess item pivot = false) := by
  intro position hposition hstop
  let offset := r - 1 - position
  have hoffset : offset < block := by omega
  have haddress : r - 1 - offset = position := by omega
  have hgood := OffsetScanExact.exhausted block index offsets
    (fun offset => isLess array[r - 1 - offset]! pivot) hexact
    offset hoffset
  simpa only [haddress] using hgood

private def blockCycleOutput
    (array : Array T) (l r : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL startR count : ℕ) : Array T :=
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  let tmp := array[left startL]!
  let afterFirst := array.set! (left startL) array[right startR]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (startL, startR, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  result.2.2.set! (right result.2.1) tmp

private theorem blockCycleOutput_size
    (array : Array T) (l r : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL startR count : ℕ) :
    (blockCycleOutput array l r offsetsL offsetsR
      startL startR count).size = array.size := by
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  let afterFirst := array.set! (left startL) array[right startR]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (startL, startR, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  have hshape := cycle_loop_shape (T := T) left right startL startR
    (List.range' 0 (count - 1)) 0 afterFirst
  have hresultSize : result.2.2.size = array.size := by
    simpa [result, afterFirst] using hshape.2.2
  simpa [blockCycleOutput, left, right, result, Array.set!]
    using hresultSize

private theorem scanned_block_cycle_classifies
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR count : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ array.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hstartL : startL ≤ endL) (hstartR : startR ≤ endR)
    (hendL : endL ≤ offsetsL.size) (hendR : endR ≤ offsetsR.size)
    (hcount : 0 < count)
    (hcountL : count ≤ endL - startL)
    (hcountR : count ≤ endR - startR)
    (hexactL : OffsetScanExact blockL startL endL offsetsL
      (fun index => !isLess array[l + index]! pivot))
    (hexactR : OffsetScanExact blockR startR endR offsetsR
      (fun index => isLess array[r - 1 - index]! pivot)) :
    (∀ index, index < count →
      isLess (blockCycleOutput array l r offsetsL offsetsR
        startL startR count)[l + offsetsL[startL + index]!]! pivot = true) ∧
    (∀ index, index < count →
      isLess (blockCycleOutput array l r offsetsL offsetsR
        startL startR count)[r - offsetsR[startR + index]! - 1]!
          pivot = false) := by
  simp only [blockCycleOutput]
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  apply block_cycle_classifies array left right startL startR count
    (fun item => isLess item pivot = false)
    (fun item => isLess item pivot = true) hcount
  · intro index hindex
    have hactive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + index)
      (by omega) (by omega)
    simp only [left]
    omega
  · intro index hindex
    have hactive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + index)
      (by omega) (by omega)
    simp only [right]
    omega
  · intro i hi j hj heq
    have hoffset : offsetsL[startL + i]! = offsetsL[startL + j]! := by
      simpa only [left, Nat.add_left_cancel_iff] using heq
    exact OffsetScanExact.injective blockL startL endL offsetsL _
      hexactL hendL i (by omega) j (by omega) hoffset
  · intro i hi j hj heq
    have hiActive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + i)
      (by omega) (by omega)
    have hjActive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + j)
      (by omega) (by omega)
    have hoffset : offsetsR[startR + i]! = offsetsR[startR + j]! := by
      simp only [right] at heq
      omega
    exact OffsetScanExact.injective blockR startR endR offsetsR _
      hexactR hendR i (by omega) j (by omega) hoffset
  · intro i hi j hj heq
    have hleftActive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + i)
      (by omega) (by omega)
    have hrightActive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + j)
      (by omega) (by omega)
    simp only [left, right] at heq
    omega
  · intro index hindex
    have hactive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + index)
      (by omega) (by omega)
    simpa only [left, Bool.not_eq_true'] using hactive.2
  · intro index hindex
    have hactive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + index)
      (by omega) (by omega)
    have haddress :
        r - 1 - offsetsR[startR + index]! =
          r - offsetsR[startR + index]! - 1 := by
      omega
    simpa only [right, haddress] using hactive.2

private theorem scanned_block_cycle_outside
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR count position : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ array.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hstartL : startL ≤ endL) (hstartR : startR ≤ endR)
    (hendL : endL ≤ offsetsL.size) (hendR : endR ≤ offsetsR.size)
    (hcount : 0 < count)
    (hcountL : count ≤ endL - startL)
    (hcountR : count ≤ endR - startR)
    (hexactL : OffsetScanExact blockL startL endL offsetsL
      (fun index => !isLess array[l + index]! pivot))
    (hexactR : OffsetScanExact blockR startR endR offsetsR
      (fun index => isLess array[r - 1 - index]! pivot))
    (houtL : ∀ index, index < count →
      position ≠ l + offsetsL[startL + index]!)
    (houtR : ∀ index, index < count →
      position ≠ r - offsetsR[startR + index]! - 1) :
    (blockCycleOutput array l r offsetsL offsetsR
      startL startR count)[position]! = array[position]! := by
  simp only [blockCycleOutput]
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  apply block_cycle_outside array left right startL startR count position
    hcount
  · intro index hindex
    have hactive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + index) (by omega) (by omega)
    simp only [left]
    omega
  · intro index hindex
    have hactive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + index) (by omega) (by omega)
    simp only [right]
    omega
  · simpa only [left] using houtL
  · simpa only [right] using houtR

omit [Inhabited T] in
private theorem left_block_address_lt_right_block_address
    (l r blockL blockR leftOffset rightOffset : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hleft : leftOffset < blockL) (hright : rightOffset < blockR) :
    l + leftOffset < r - rightOffset - 1 := by
  omega

omit [Inhabited T] in
private theorem right_block_address_eq
    (r blockR offset : ℕ) (hblockR : blockR ≤ r)
    (hoffset : offset < blockR) :
    r - 1 - offset = r - offset - 1 := by
  omega

omit [Inhabited T] in
private theorem right_block_le
    (l r blockL blockR : ℕ)
    (hblocks : blockL + blockR ≤ r - l) : blockR ≤ r := by
  omega

omit [Inhabited T] in
private theorem right_block_address_injective
    (r leftOffset rightOffset : ℕ)
    (hleft : leftOffset < r) (hright : rightOffset < r)
    (heq : r - leftOffset - 1 = r - rightOffset - 1) :
    leftOffset = rightOffset := by
  omega

omit [Inhabited T] in
private theorem left_block_address_mem_interval
    (l r blockL blockR offset : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hoffset : offset < blockL) :
    l ≤ l + offset ∧ l + offset < r := by
  omega

omit [Inhabited T] in
private theorem right_block_address_mem_interval
    (l r blockL blockR offset : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hoffset : offset < blockR) :
    l ≤ r - offset - 1 ∧ r - offset - 1 < r := by
  omega

private theorem refreshOffsets_bounds
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hblock : block ≤ offsets.size)
    (hstart : startIdx ≤ endIdx)
    (hend : startIdx ≠ endIdx → endIdx ≤ block)
    (hactive : startIdx ≠ endIdx →
      ∀ j, j < endIdx → offsets[j]! < block) :
    let result := refreshOffsets block startIdx endIdx offsets keep
    result.1 ≤ result.2.1 ∧
      result.2.1 ≤ block ∧
      result.2.2.size = offsets.size ∧
      ∀ j, j < result.2.1 → result.2.2[j]! < block := by
  by_cases heq : startIdx = endIdx
  · simp only [refreshOffsets, if_pos heq]
    have hout := scan_offsets_bounds block offsets keep hblock
    exact ⟨Nat.zero_le _, hout.1, hout.2.1, hout.2.2⟩
  · simp only [refreshOffsets, if_neg heq]
    exact ⟨hstart, hend heq, trivial, hactive heq⟩

private def blockMutateArray
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) : Array T :=
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  if 0 < count then
    blockCycleOutput a l r leftData.2.2 rightData.2.2
      leftData.1 rightData.1 count
  else
    a

private theorem blockMutateArray_size
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    (blockMutateArray a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR).size = a.size := by
  rw [blockMutateArray]
  split
  · exact blockCycleOutput_size a l r _ _ _ _ _
  · rfl

private theorem blockMutateArray_eq_blockCycleOutput_of_pos
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    let leftData := refreshOffsets blockL startL endL offsetsL
      (fun index => !isLess a[l + index]! pivot)
    let rightData := refreshOffsets blockR startR endR offsetsR
      (fun index => isLess a[r - 1 - index]! pivot)
    let count := min (leftData.2.1 - leftData.1)
      (rightData.2.1 - rightData.1)
    0 < count →
      blockMutateArray a pivot isLess l r blockL blockR
          offsetsL offsetsR startL endL startR endR =
        blockCycleOutput a l r leftData.2.2 rightData.2.2
          leftData.1 rightData.1 count := by
  simp only
  intro hcount
  rw [blockMutateArray, if_pos hcount]

private theorem blockMutateArray_eq_self_of_no_count
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    let leftData := refreshOffsets blockL startL endL offsetsL
      (fun index => !isLess a[l + index]! pivot)
    let rightData := refreshOffsets blockR startR endR offsetsR
      (fun index => isLess a[r - 1 - index]! pivot)
    let count := min (leftData.2.1 - leftData.1)
      (rightData.2.1 - rightData.1)
    ¬0 < count →
      blockMutateArray a pivot isLess l r blockL blockR
        offsetsL offsetsR startL endL startR endR = a := by
  simp only
  intro hcount
  rw [blockMutateArray, if_neg hcount]

private theorem blockMutateArray_perm
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblockLgap : blockL ≤ r - l)
    (hblockRgap : blockR ≤ r - l)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    List.Perm
      (blockMutateArray a pivot isLess l r blockL blockR
        offsetsL offsetsR startL endL startR endR).toList
      a.toList := by
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  have hleft := refreshOffsets_bounds blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
    (by omega) hstartL hendL hactiveL
  have hright := refreshOffsets_bounds blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
    (by omega) hstartR hendR hactiveR
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  dsimp only [blockMutateArray]
  split
  next hcount =>
    apply scanned_block_cycle_perm a l r blockL blockR
      leftData.2.2 rightData.2.2 leftData.1 leftData.2.1
      rightData.1 rightData.2.1 count
      hlr hrsize hblockLgap hblockRgap hleft.1 hright.1
      hcount
    · exact min_le_left _ _
    · exact min_le_right _ _
    · exact hleft.2.2.2
    · exact hright.2.2.2
  next _ => exact .refl _

private theorem blockMutateArray_offsets_exact
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hblockL : blockL ≤ offsetsL.size)
    (hblockR : blockR ≤ offsetsR.size)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR)
    (hexactL : startL ≠ endL →
      OffsetScanExact blockL startL endL offsetsL
        (fun index => !isLess a[l + index]! pivot))
    (hexactR : startR ≠ endR →
      OffsetScanExact blockR startR endR offsetsR
        (fun index => isLess a[r - 1 - index]! pivot)) :
    let leftData := refreshOffsets blockL startL endL offsetsL
      (fun index => !isLess a[l + index]! pivot)
    let rightData := refreshOffsets blockR startR endR offsetsR
      (fun index => isLess a[r - 1 - index]! pivot)
    let count := min (leftData.2.1 - leftData.1)
      (rightData.2.1 - rightData.1)
    let output := blockMutateArray a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    OffsetScanExact blockL (leftData.1 + count) leftData.2.1
        leftData.2.2 (fun index => !isLess output[l + index]! pivot) ∧
      OffsetScanExact blockR (rightData.1 + count) rightData.2.1
        rightData.2.2
          (fun index => isLess output[r - 1 - index]! pivot) ∧
      ∀ position, position < l ∨ r ≤ position →
        output[position]! = a[position]! := by
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun index => !isLess a[l + index]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun index => isLess a[r - 1 - index]! pivot)
  have hleftExact : OffsetScanExact blockL leftData.1 leftData.2.1
      leftData.2.2 (fun index => !isLess a[l + index]! pivot) := by
    simpa only [leftData] using refreshOffsets_exact blockL startL endL
      offsetsL (fun index => !isLess a[l + index]! pivot)
      hblockL hexactL
  have hrightExact : OffsetScanExact blockR rightData.1 rightData.2.1
      rightData.2.2 (fun index => isLess a[r - 1 - index]! pivot) := by
    simpa only [rightData] using refreshOffsets_exact blockR startR endR
      offsetsR (fun index => isLess a[r - 1 - index]! pivot)
      hblockR hexactR
  have hleft : leftData.1 ≤ leftData.2.1 ∧
      leftData.2.1 ≤ blockL ∧
      leftData.2.2.size = offsetsL.size ∧
      ∀ j, j < leftData.2.1 → leftData.2.2[j]! < blockL := by
    simpa only [leftData] using refreshOffsets_bounds blockL startL endL
      offsetsL (fun index => !isLess a[l + index]! pivot)
      hblockL hstartL hendL hactiveL
  have hright : rightData.1 ≤ rightData.2.1 ∧
      rightData.2.1 ≤ blockR ∧
      rightData.2.2.size = offsetsR.size ∧
      ∀ j, j < rightData.2.1 → rightData.2.2[j]! < blockR := by
    simpa only [rightData] using refreshOffsets_bounds blockR startR endR
      offsetsR (fun index => isLess a[r - 1 - index]! pivot)
      hblockR hstartR hendR hactiveR
  have hleftEndSize : leftData.2.1 ≤ leftData.2.2.size := by
    exact hleft.2.1.trans (hblockL.trans_eq hleft.2.2.1.symm)
  have hrightEndSize : rightData.2.1 ≤ rightData.2.2.size := by
    exact hright.2.1.trans (hblockR.trans_eq hright.2.2.1.symm)
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  have hcountL : count ≤ leftData.2.1 - leftData.1 :=
    min_le_left _ _
  have hcountR : count ≤ rightData.2.1 - rightData.1 :=
    min_le_right _ _
  let output := blockMutateArray a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
  by_cases hcount : 0 < count
  · have houtput : output = blockCycleOutput a l r leftData.2.2
        rightData.2.2 leftData.1 rightData.1 count := by
      have hresult := blockMutateArray_eq_blockCycleOutput_of_pos
        a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR
      simpa only [output, leftData, rightData, count] using hresult hcount
    have houtputRaw :
        blockMutateArray a pivot isLess l r blockL blockR
            offsetsL offsetsR startL endL startR endR =
          blockCycleOutput a l r leftData.2.2 rightData.2.2
            leftData.1 rightData.1 count := by
      simpa only [output] using houtput
    have hclassified := scanned_block_cycle_classifies a pivot isLess
      l r blockL blockR leftData.2.2 rightData.2.2
      leftData.1 leftData.2.1 rightData.1 rightData.2.1 count
      hlr hrsize hblocks hleft.1 hright.1 hleftEndSize hrightEndSize
      hcount hcountL hcountR hleftExact hrightExact
    have hclassifiedOutput :
        (∀ index, index < count →
          isLess output[l + leftData.2.2[leftData.1 + index]!]!
            pivot = true) ∧
        (∀ index, index < count →
          isLess output[r - rightData.2.2[rightData.1 + index]! - 1]!
            pivot = false) := by
      simpa only [houtput] using hclassified
    refine ⟨?_, ?_, ?_⟩
    · apply OffsetScanExact.consume blockL leftData.1 leftData.2.1
        count leftData.2.2
        (fun index => !isLess a[l + index]! pivot)
        (fun index => !isLess output[l + index]! pivot)
        hleftExact hleft.1 hleftEndSize hcountL
      · intro index hindex
        simpa using hclassifiedOutput.1 index hindex
      · intro offset hoffset hnotConsumed
        have hout := scanned_block_cycle_outside a pivot isLess
          l r blockL blockR leftData.2.2 rightData.2.2
          leftData.1 leftData.2.1 rightData.1 rightData.2.1
          count (l + offset) hlr hrsize hblocks hleft.1 hright.1
          hleftEndSize hrightEndSize hcount hcountL hcountR
          hleftExact hrightExact
          (by
            intro index hindex heq
            exact hnotConsumed index hindex
              (Nat.add_left_cancel heq))
          (by
            intro index hindex heq
            have hactive := OffsetScanExact.active blockR rightData.1
              rightData.2.1 rightData.2.2 _ hrightExact
              hrightEndSize (rightData.1 + index) (by omega) (by omega)
            exact (left_block_address_lt_right_block_address
              l r blockL blockR offset
              rightData.2.2[rightData.1 + index]!
              hblocks hoffset hactive.1).ne heq)
        simpa only [houtput] using congrArg
          (fun value => !isLess value pivot) hout
    · apply OffsetScanExact.consume blockR rightData.1 rightData.2.1
        count rightData.2.2
        (fun index => isLess a[r - 1 - index]! pivot)
        (fun index => isLess output[r - 1 - index]! pivot)
        hrightExact hright.1 hrightEndSize hcountR
      · intro index hindex
        have haddress :
            r - 1 - rightData.2.2[rightData.1 + index]! =
              r - rightData.2.2[rightData.1 + index]! - 1 := by
          have hactive := OffsetScanExact.active blockR rightData.1
            rightData.2.1 rightData.2.2 _ hrightExact hrightEndSize
            (rightData.1 + index) (by omega) (by omega)
          exact right_block_address_eq r blockR
            rightData.2.2[rightData.1 + index]!
            (right_block_le l r blockL blockR hblocks) hactive.1
        rw [haddress]
        exact hclassifiedOutput.2 index hindex
      · intro offset hoffset hnotConsumed
        have hposition : r - 1 - offset = r - offset - 1 :=
          right_block_address_eq r blockR offset
            (right_block_le l r blockL blockR hblocks) hoffset
        have hout := scanned_block_cycle_outside a pivot isLess
          l r blockL blockR leftData.2.2 rightData.2.2
          leftData.1 leftData.2.1 rightData.1 rightData.2.1
          count (r - 1 - offset) hlr hrsize hblocks hleft.1 hright.1
          hleftEndSize hrightEndSize hcount hcountL hcountR
          hleftExact hrightExact
          (by
            intro index hindex
            have hactive := OffsetScanExact.active blockL leftData.1
              leftData.2.1 leftData.2.2 _ hleftExact hleftEndSize
              (leftData.1 + index) (by omega) (by omega)
            rw [hposition]
            exact (left_block_address_lt_right_block_address
              l r blockL blockR leftData.2.2[leftData.1 + index]!
              offset hblocks hactive.1 hoffset).ne')
          (by
            intro index hindex
            rw [hposition]
            intro heq
            apply hnotConsumed index hindex
            have hactive := OffsetScanExact.active blockR rightData.1
              rightData.2.1 rightData.2.2 _ hrightExact
              hrightEndSize (rightData.1 + index) (by omega) (by omega)
            have hblockRr := right_block_le l r blockL blockR hblocks
            exact right_block_address_injective r offset
              rightData.2.2[rightData.1 + index]!
              (hoffset.trans_le hblockRr) (hactive.1.trans_le hblockRr) heq)
        simpa only [houtput] using congrArg
          (fun value => isLess value pivot) hout
    · intro position hposition
      rw [houtputRaw]
      apply scanned_block_cycle_outside a pivot isLess
        l r blockL blockR leftData.2.2 rightData.2.2
        leftData.1 leftData.2.1 rightData.1 rightData.2.1
        count position hlr hrsize hblocks hleft.1 hright.1
        hleftEndSize hrightEndSize hcount hcountL hcountR
        hleftExact hrightExact
      · intro index hindex
        have hactive := OffsetScanExact.active blockL leftData.1
          leftData.2.1 leftData.2.2 _ hleftExact hleftEndSize
          (leftData.1 + index) (by omega) (by omega)
        have hmem := left_block_address_mem_interval l r blockL blockR
          leftData.2.2[leftData.1 + index]! hblocks hactive.1
        rcases hposition with hbefore | hafter <;> omega
      · intro index hindex
        have hactive := OffsetScanExact.active blockR rightData.1
          rightData.2.1 rightData.2.2 _ hrightExact hrightEndSize
          (rightData.1 + index) (by omega) (by omega)
        have hmem := right_block_address_mem_interval l r blockL blockR
          rightData.2.2[rightData.1 + index]! hblocks hactive.1
        rcases hposition with hbefore | hafter <;> omega
  · have hzero : count = 0 := by omega
    have houtput : output = a := by
      have hresult := blockMutateArray_eq_self_of_no_count
        a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR
      simpa only [output, leftData, rightData, count] using hresult hcount
    have houtputRaw :
        blockMutateArray a pivot isLess l r blockL blockR
          offsetsL offsetsR startL endL startR endR = a := by
      simpa only [output] using houtput
    have hleftResult : OffsetScanExact blockL
        (leftData.1 + count) leftData.2.1 leftData.2.2
        (fun index => !isLess output[l + index]! pivot) := by
      simpa only [hzero, Nat.add_zero, houtput] using hleftExact
    have hrightResult : OffsetScanExact blockR
        (rightData.1 + count) rightData.2.1 rightData.2.2
        (fun index => isLess output[r - 1 - index]! pivot) := by
      simpa only [hzero, Nat.add_zero, houtput] using hrightExact
    exact ⟨hleftResult, hrightResult, fun position _ =>
      congrArg (fun array => array[position]!) houtputRaw⟩

private theorem cleanupLeftStep_order
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (start endIdx left right : ℕ) (offsets : Array ℕ)
    (hstart : start < endIdx) (hlr : left ≤ right)
    (hright : right ≤ array.size) (hend : endIdx ≤ offsets.size)
    (hprefix : RangeAll array 0 left
      (fun item => isLess item pivot = true))
    (hsuffix : RangeAll array right array.size
      (fun item => isLess item pivot = false))
    (hexact : OffsetScanExact (right - left) start endIdx offsets
      (fun offset => !isLess array[left + offset]! pivot)) :
    let next := swp array (left + offsets[endIdx - 1]!) (right - 1)
    RangeAll next 0 left (fun item => isLess item pivot = true) ∧
      RangeAll next (right - 1) next.size
        (fun item => isLess item pivot = false) ∧
      OffsetScanExact (right - 1 - left) start (endIdx - 1) offsets
        (fun offset => !isLess next[left + offset]! pivot) := by
  let block := right - left
  let last := offsets[endIdx - 1]!
  let hole := left + last
  let edge := right - 1
  let next := swp array hole edge
  have hlast := OffsetScanExact.active block start endIdx offsets
    (fun offset => !isLess array[left + offset]! pivot)
    (by simpa only [block] using hexact) hend (endIdx - 1)
    (by omega) (by omega)
  have hrightPositive : 0 < right := by
    simp only [block] at hlast
    omega
  have hhole : hole < array.size := by
    simp only [hole, block] at *
    omega
  have hedge : edge < array.size := by
    simp only [edge]
    omega
  have hnextSize : next.size = array.size := by
    simp [next, swp_size]
  have hnextPrefix : RangeAll next 0 left
      (fun item => isLess item pivot = true) := by
    apply RangeAll.swp array hole edge 0 left _ hhole hedge hprefix
    · intro _ hstop
      simp only [hole] at hstop
      omega
    · intro _ hstop
      simp only [edge] at hstop
      omega
  have hholeBad : isLess array[hole]! pivot = false := by
    have hbad := hlast.2
    simpa only [hole, last, Bool.not_eq_true'] using hbad
  have hnextEdge : isLess next[edge]! pivot = false := by
    show isLess (swp array hole edge)[edge]! pivot = false
    by_cases heq : edge = hole
    · rw [swp_get! array hole edge edge hhole hedge, if_pos heq]
      simpa only [heq] using hholeBad
    · rw [swp_get! array hole edge edge hhole hedge,
        if_neg heq, if_pos rfl]
      exact hholeBad
  have hnextSuffixBase : RangeAll next right next.size
      (fun item => isLess item pivot = false) := by
    rw [hnextSize]
    apply RangeAll.swp array hole edge right array.size _ hhole hedge hsuffix
    · intro hposition _
      simp only [hole, block] at hposition hlast
      omega
    · intro hposition _
      simp only [edge] at hposition
      omega
  have hnextSuffixPoint : RangeAll next edge right
      (fun item => isLess item pivot = false) := by
    intro position hposition hstop
    have hpositionEq : position = edge := by
      simp only [edge] at *
      omega
    simpa only [hpositionEq] using hnextEdge
  have hnextSuffix : RangeAll next edge next.size
      (fun item => isLess item pivot = false) := by
    apply RangeAll.append hnextSuffixPoint hnextSuffixBase
  have hnextExact : OffsetScanExact (block - 1) start
      (endIdx - 1) offsets
      (fun offset => !isLess next[left + offset]! pivot) := by
    apply OffsetScanExact.shrinkLast block start endIdx offsets
      (fun offset => !isLess array[left + offset]! pivot)
      (fun offset => !isLess next[left + offset]! pivot)
      (by simpa only [block] using hexact) hstart hend
    · intro hlastBeforeEdge
      have hedgeGood := OffsetScanExact.gt_last_false block start endIdx
        offsets (fun offset => !isLess array[left + offset]! pivot)
        (by simpa only [block] using hexact) hstart hend
        (block - 1) (by omega) (by simpa only [last] using hlastBeforeEdge)
      have haddress : left + (block - 1) = edge := by
        simp only [block, edge]
        omega
      have hedgeGood' :
          (!isLess array[left + (block - 1)]! pivot) = false := by
        simpa only using hedgeGood
      rw [swp_get! array hole edge (left + last) hhole hedge,
        if_pos rfl]
      rw [haddress] at hedgeGood'
      exact hedgeGood'
    · intro offset hoffset hne
      have hpositionNeHole : left + offset ≠ hole := by
        simp only [hole, last]
        intro heq
        exact hne (Nat.add_left_cancel heq)
      have hpositionNeEdge : left + offset ≠ edge := by
        simp only [block, edge] at hoffset ⊢
        omega
      rw [swp_get! array hole edge (left + offset) hhole hedge,
        if_neg hpositionNeHole, if_neg hpositionNeEdge]
  have hblockEq : block - 1 = right - 1 - left := by
    simp only [block] at *
    omega
  simpa only [next, hole, last, edge, hblockEq] using
    And.intro hnextPrefix (And.intro hnextSuffix hnextExact)

private theorem cleanupLeft_order
    (indices : List ℕ) (pivot : T) (isLess : T → T → Bool)
    (start left : ℕ) (offsets : Array ℕ) :
    ∀ (endIdx right : ℕ) (array : Array T),
      start ≤ endIdx → endIdx - start < indices.length →
      left ≤ right → right ≤ array.size → endIdx ≤ offsets.size →
      RangeAll array 0 left (fun item => isLess item pivot = true) →
      RangeAll array right array.size
        (fun item => isLess item pivot = false) →
      OffsetScanExact (right - left) start endIdx offsets
        (fun offset => !isLess array[left + offset]! pivot) →
      let result := cleanupLeft indices start left offsets
        ⟨endIdx, right, array⟩
      RangeAll result.2.2 0 result.2.1
          (fun item => isLess item pivot = true) ∧
        RangeAll result.2.2 result.2.1 result.2.2.size
          (fun item => isLess item pivot = false) := by
  induction indices with
  | nil =>
      intro endIdx right array hstart hfuel
      simp at hfuel
  | cons index indices inductionHypothesis =>
      intro endIdx right array hstart hfuel hlr hright hend
        hprefix hsuffix hexact
      rw [cleanupLeft_cons]
      by_cases hactive : start < endIdx
      · rw [if_pos hactive]
        have hstep := cleanupLeftStep_order array pivot isLess
          start endIdx left right offsets hactive hlr hright hend
          hprefix hsuffix hexact
        have hlast := OffsetScanExact.active (right - left) start endIdx
          offsets (fun offset => !isLess array[left + offset]! pivot)
          hexact hend (endIdx - 1) (by omega) (by omega)
        have hleftLtRight : left < right := by omega
        let next := swp array (left + offsets[endIdx - 1]!) (right - 1)
        have hnextSize : next.size = array.size := by simp [next, swp_size]
        apply inductionHypothesis (endIdx - 1) (right - 1) next
        · omega
        · simp only [List.length_cons] at hfuel
          omega
        · omega
        · rw [hnextSize]
          omega
        · omega
        · simpa only [next] using hstep.1
        · simpa only [next] using hstep.2.1
        · simpa only [next] using hstep.2.2
      · rw [if_neg hactive]
        have hdone : start = endIdx := by omega
        have hmiddle : RangeAll array left right
            (fun item => isLess item pivot = true) := by
          have hexhausted := exhausted_left_block_rangeAll array pivot
            isLess left (right - left) endIdx offsets (by
              simpa only [hdone] using hexact)
          simpa only [Nat.add_sub_of_le hlr] using hexhausted
        exact ⟨RangeAll.append hprefix hmiddle, hsuffix⟩

private theorem cleanupRightStep_order
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (start endIdx left right : ℕ) (offsets : Array ℕ)
    (hstart : start < endIdx) (hlr : left ≤ right)
    (hright : right ≤ array.size) (hend : endIdx ≤ offsets.size)
    (hprefix : RangeAll array 0 left
      (fun item => isLess item pivot = true))
    (hsuffix : RangeAll array right array.size
      (fun item => isLess item pivot = false))
    (hexact : OffsetScanExact (right - left) start endIdx offsets
      (fun offset => isLess array[right - 1 - offset]! pivot)) :
    let next := swp array left (right - offsets[endIdx - 1]! - 1)
    RangeAll next 0 (left + 1) (fun item => isLess item pivot = true) ∧
      RangeAll next right next.size
        (fun item => isLess item pivot = false) ∧
      OffsetScanExact (right - (left + 1)) start (endIdx - 1) offsets
        (fun offset => isLess next[right - 1 - offset]! pivot) := by
  let block := right - left
  let last := offsets[endIdx - 1]!
  let hole := right - last - 1
  let edge := left
  let next := swp array edge hole
  have hlast := OffsetScanExact.active block start endIdx offsets
    (fun offset => isLess array[right - 1 - offset]! pivot)
    (by simpa only [block] using hexact) hend (endIdx - 1)
    (by omega) (by omega)
  have hleftLtRight : left < right := by
    simp only [block] at hlast
    omega
  have hedge : edge < array.size := by simp only [edge]; omega
  have hhole : hole < array.size := by simp only [hole, block] at *; omega
  have hnextSize : next.size = array.size := by simp [next, swp_size]
  have hholeGood : isLess array[hole]! pivot = true := by
    have haddress : right - 1 - last = hole := by
      simp only [hole]
      omega
    rw [← haddress]
    simpa only [last] using hlast.2
  have hnextEdge : isLess next[edge]! pivot = true := by
    show isLess (swp array edge hole)[edge]! pivot = true
    rw [swp_get! array edge hole edge hedge hhole, if_pos rfl]
    exact hholeGood
  have hnextPrefixBase : RangeAll next 0 left
      (fun item => isLess item pivot = true) := by
    apply RangeAll.swp array edge hole 0 left _ hedge hhole hprefix
    · intro _ hstop
      simp only [edge] at hstop
      omega
    · intro _ hstop
      simp only [hole, block] at hstop hlast
      omega
  have hnextPrefixPoint : RangeAll next left (left + 1)
      (fun item => isLess item pivot = true) := by
    intro position hposition hstop
    have hpositionEq : position = edge := by simp only [edge]; omega
    simpa only [hpositionEq] using hnextEdge
  have hnextPrefix : RangeAll next 0 (left + 1)
      (fun item => isLess item pivot = true) :=
    RangeAll.append hnextPrefixBase hnextPrefixPoint
  have hnextSuffix : RangeAll next right next.size
      (fun item => isLess item pivot = false) := by
    rw [hnextSize]
    apply RangeAll.swp array edge hole right array.size _ hedge hhole hsuffix
    · intro hposition _
      simp only [edge] at hposition
      omega
    · intro hposition _
      simp only [hole, block] at hposition hlast
      omega
  have hnextExact : OffsetScanExact (block - 1) start
      (endIdx - 1) offsets
      (fun offset => isLess next[right - 1 - offset]! pivot) := by
    apply OffsetScanExact.shrinkLast block start endIdx offsets
      (fun offset => isLess array[right - 1 - offset]! pivot)
      (fun offset => isLess next[right - 1 - offset]! pivot)
      (by simpa only [block] using hexact) hstart hend
    · intro hlastBeforeEdge
      have hedgeGood := OffsetScanExact.gt_last_false block start endIdx
        offsets (fun offset => isLess array[right - 1 - offset]! pivot)
        (by simpa only [block] using hexact) hstart hend
        (block - 1) (by omega) (by simpa only [last] using hlastBeforeEdge)
      have haddress : right - 1 - (block - 1) = edge := by
        simp only [block, edge]
        omega
      have hedgeGood' :
          isLess array[right - 1 - (block - 1)]! pivot = false := by
        simpa only using hedgeGood
      rw [swp_get! array edge hole (right - 1 - last) hedge hhole]
      have htarget : right - 1 - last = hole := by simp [hole]; omega
      rw [if_neg (by omega), if_pos htarget]
      rw [haddress] at hedgeGood'
      exact hedgeGood'
    · intro offset hoffset hne
      have hpositionNeHole : right - 1 - offset ≠ hole := by
        simp only [hole, last]
        intro heq
        exact hne (right_block_address_injective right offset last
          (by simp only [block] at *; omega)
          (by simp only [block] at hlast; omega) (by omega))
      have hpositionNeEdge : right - 1 - offset ≠ edge := by
        simp only [block, edge] at hoffset ⊢
        omega
      rw [swp_get! array edge hole (right - 1 - offset) hedge hhole,
        if_neg hpositionNeEdge, if_neg hpositionNeHole]
  have hblockEq : block - 1 = right - (left + 1) := by
    simp only [block] at *
    omega
  simpa only [next, edge, hole, last, hblockEq] using
    And.intro hnextPrefix (And.intro hnextSuffix hnextExact)

private theorem cleanupRight_order
    (indices : List ℕ) (pivot : T) (isLess : T → T → Bool)
    (start right : ℕ) (offsets : Array ℕ) :
    ∀ (endIdx left : ℕ) (array : Array T),
      start ≤ endIdx → endIdx - start < indices.length →
      left ≤ right → right ≤ array.size → endIdx ≤ offsets.size →
      RangeAll array 0 left (fun item => isLess item pivot = true) →
      RangeAll array right array.size
        (fun item => isLess item pivot = false) →
      OffsetScanExact (right - left) start endIdx offsets
        (fun offset => isLess array[right - 1 - offset]! pivot) →
      let result := cleanupRight indices start right offsets
        ⟨endIdx, left, array⟩
      RangeAll result.2.2 0 result.2.1
          (fun item => isLess item pivot = true) ∧
        RangeAll result.2.2 result.2.1 result.2.2.size
          (fun item => isLess item pivot = false) := by
  induction indices with
  | nil =>
      intro endIdx left array hstart hfuel
      simp at hfuel
  | cons index indices inductionHypothesis =>
      intro endIdx left array hstart hfuel hlr hright hend
        hprefix hsuffix hexact
      rw [cleanupRight_cons]
      by_cases hactive : start < endIdx
      · rw [if_pos hactive]
        have hstep := cleanupRightStep_order array pivot isLess
          start endIdx left right offsets hactive hlr hright hend
          hprefix hsuffix hexact
        have hlast := OffsetScanExact.active (right - left) start endIdx
          offsets (fun offset => isLess array[right - 1 - offset]! pivot)
          hexact hend (endIdx - 1) (by omega) (by omega)
        have hleftLtRight : left < right := by omega
        let next := swp array left (right - offsets[endIdx - 1]! - 1)
        have hnextSize : next.size = array.size := by simp [next, swp_size]
        apply inductionHypothesis (endIdx - 1) (left + 1) next
        · omega
        · simp only [List.length_cons] at hfuel
          omega
        · omega
        · rw [hnextSize]
          omega
        · omega
        · simpa only [next] using hstep.1
        · simpa only [next] using hstep.2.1
        · simpa only [next] using hstep.2.2
      · rw [if_neg hactive]
        have hdone : start = endIdx := by omega
        have hmiddle : RangeAll array left right
            (fun item => isLess item pivot = false) := by
          have hexhausted := exhausted_right_block_rangeAll array pivot
            isLess right (right - left) endIdx offsets (by omega) (by
              simpa only [hdone] using hexact)
          simpa only [Nat.sub_sub_self hlr] using hexhausted
        exact ⟨hprefix, RangeAll.append hmiddle hsuffix⟩

omit [Inhabited T] in
private theorem min_remaining_exhausts
    (startL endL startR endR : ℕ)
    (hleft : startL ≤ endL) (hright : startR ≤ endR) :
    let count := min (endL - startL) (endR - startR)
    startL + count = endL ∨ startR + count = endR := by
  simp only
  rcases le_total (endL - startL) (endR - startR) with h | h
  · left
    rw [min_eq_left h]
    omega
  · right
    rw [min_eq_right h]
    omega

omit [Inhabited T] in
private theorem advance_block_bounds
    (n l r blockL blockR : ℕ)
    (advanceL advanceR : Bool)
    (hlr : l ≤ r) (hrn : r ≤ n)
    (hblocks : blockL + blockR ≤ r - l) :
    let l' := if advanceL = true then l + blockL else l
    let r' := if advanceR = true then r - blockR else r
    l' ≤ r' ∧ r' ≤ n := by
  by_cases hL : advanceL = true
  · by_cases hR : advanceR = true
    · simp only [if_pos hL, if_pos hR]
      omega
    · simp only [if_pos hL, if_neg hR]
      omega
  · by_cases hR : advanceR = true
    · simp only [if_neg hL, if_pos hR]
      omega
    · simp only [if_neg hL, if_neg hR]
      omega

omit [Inhabited T] in
private theorem forIn_step_invariant
    {ι S : Type} (P : S → Prop) (step : ι → S → ForInStep S)
    (hstep : ∀ i s, P s →
      match step i s with
      | .done s' => P s'
      | .yield s' => P s') :
    ∀ (indices : List ι) (initial : S),
      P initial →
      P (Id.run <|
        forIn indices initial fun i s => pure (step i s)) := by
  intro indices
  induction indices with
  | nil =>
      intro initial hinitial
      simpa using hinitial
  | cons i indices ih =>
      intro initial hinitial
      simp only [List.forIn_cons]
      cases hresult : step i initial with
      | done result =>
          simpa [hresult] using hstep i initial hinitial
      | yield result =>
          simpa [hresult] using
            ih result (by
              simpa [hresult] using hstep i initial hinitial)

omit [Inhabited T] in
private theorem forIn_step_post
    {ι S : Type} (P Q : S → Prop)
    (step : ι → S → ForInStep S)
    (hyield : ∀ i s s', P s →
      step i s = .yield s' → P s')
    (hdone : ∀ i s s', P s →
      step i s = .done s' → Q s')
    (hexhausted : ∀ s, P s → Q s) :
    ∀ (indices : List ι) (initial : S),
      P initial →
      Q (Id.run <|
        forIn indices initial fun i s => pure (step i s)) := by
  intro indices
  induction indices with
  | nil =>
      intro initial hinitial
      exact hexhausted initial hinitial
  | cons i indices ih =>
      intro initial hinitial
      simp only [List.forIn_cons]
      cases hresult : step i initial with
      | done result =>
          simpa [hresult] using
            hdone i initial result hinitial hresult
      | yield result =>
          simpa [hresult] using
            ih result (hyield i initial result hinitial hresult)

omit [Inhabited T] in
private theorem forIn_step_decreasing_post
    {ι S : Type} (P Q : S → Prop) (measure : S → ℕ)
    (step : ι → S → ForInStep S)
    (hyield : ∀ i s s', P s → step i s = .yield s' →
      P s' ∧ measure s' < measure s)
    (hdone : ∀ i s s', P s → step i s = .done s' → Q s') :
    ∀ (indices : List ι) (initial : S),
      P initial → measure initial < indices.length →
      Q (Id.run <|
        forIn indices initial fun i s => pure (step i s)) := by
  intro indices
  induction indices with
  | nil =>
      intro initial hinitial hfuel
      simp at hfuel
  | cons index indices inductionHypothesis =>
      intro initial hinitial hfuel
      simp only [List.forIn_cons]
      cases hresult : step index initial with
      | done result =>
          simpa [hresult] using hdone index initial result hinitial hresult
      | yield result =>
          have hnext := hyield index initial result hinitial hresult
          simpa [hresult] using inductionHypothesis result hnext.1 (by
            simp only [List.length_cons] at hfuel
            omega)

private structure BlockCoreResult (T : Type) where
  v : Array T
  l : ℕ
  r : ℕ
  startL : ℕ
  endL : ℕ
  offsetsL : Array ℕ
  startR : ℕ
  endR : ℕ
  offsetsR : Array ℕ

private def blockCore
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) : BlockCoreResult T :=
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  let newStartL := leftData.1 + count
  let newStartR := rightData.1 + count
  let advanceL := decide (newStartL = leftData.2.1)
  let advanceR := decide (newStartR = rightData.2.1)
  {
    v := blockMutateArray a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    l := if advanceL = true then l + blockL else l
    r := if advanceR = true then r - blockR else r
    startL := newStartL
    endL := leftData.2.1
    offsetsL := leftData.2.2
    startR := newStartR
    endR := rightData.2.1
    offsetsR := rightData.2.2
  }

private theorem blockCore_offsets_exact
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hblockL : blockL ≤ offsetsL.size)
    (hblockR : blockR ≤ offsetsR.size)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR)
    (hexactL : startL ≠ endL →
      OffsetScanExact blockL startL endL offsetsL
        (fun index => !isLess a[l + index]! pivot))
    (hexactR : startR ≠ endR →
      OffsetScanExact blockR startR endR offsetsR
        (fun index => isLess a[r - 1 - index]! pivot)) :
    let core := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    OffsetScanExact blockL core.startL core.endL core.offsetsL
        (fun index => !isLess core.v[l + index]! pivot) ∧
      OffsetScanExact blockR core.startR core.endR core.offsetsR
        (fun index => isLess core.v[r - 1 - index]! pivot) ∧
      ∀ position, position < l ∨ r ≤ position →
        core.v[position]! = a[position]! := by
  simpa only [blockCore] using blockMutateArray_offsets_exact
    a pivot isLess l r blockL blockR offsetsL offsetsR
    startL endL startR endR hlr hrsize hblocks hblockL hblockR
    hstartL hendL hstartR hendR hactiveL hactiveR hexactL hexactR

private theorem blockCore_perm
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblockLgap : blockL ≤ r - l)
    (hblockRgap : blockR ≤ r - l)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    List.Perm
      (blockCore a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR).v.toList
      a.toList := by
  apply blockMutateArray_perm a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
    hlr hrsize hblockLgap hblockRgap hsizeL hsizeR
    hblockL hblockR hstartL hendL hstartR hendR
    hactiveL hactiveR

private theorem blockCore_cursor_bounds
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (n : ℕ)
    (hlr : l ≤ r) (hrn : r ≤ n)
    (hblocks : blockL + blockR ≤ r - l) :
    let result := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    result.l ≤ result.r ∧ result.r ≤ n := by
  apply advance_block_bounds n l r blockL blockR
  · exact hlr
  · exact hrn
  · exact hblocks

private theorem blockCore_offset_bounds
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    let result := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    result.startL ≤ result.endL ∧
      result.endL ≤ blockL ∧
      result.offsetsL.size = 128 ∧
      (∀ j, j < result.endL →
        result.offsetsL[j]! < blockL) ∧
      result.startR ≤ result.endR ∧
      result.endR ≤ blockR ∧
      result.offsetsR.size = 128 ∧
      (∀ j, j < result.endR →
        result.offsetsR[j]! < blockR) ∧
      (result.startL = result.endL ∨
        result.startR = result.endR) := by
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  have hleft := refreshOffsets_bounds blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
    (by omega) hstartL hendL hactiveL
  have hright := refreshOffsets_bounds blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
    (by omega) hstartR hendR hactiveR
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  have hcountL : count ≤ leftData.2.1 - leftData.1 :=
    min_le_left _ _
  have hcountR : count ≤ rightData.2.1 - rightData.1 :=
    min_le_right _ _
  have hexhaust := min_remaining_exhausts
    leftData.1 leftData.2.1 rightData.1 rightData.2.1
    hleft.1 hright.1
  dsimp only [blockCore]
  exact ⟨by omega, hleft.2.1, by omega, hleft.2.2.2,
    by omega, hright.2.1, by omega, hright.2.2.2,
    by simpa only [count] using hexhaust⟩

private structure BlockLoopState (T : Type) where
  v : Array T
  l : ℕ
  r : ℕ
  blockL : ℕ
  blockR : ℕ
  startL : ℕ
  endL : ℕ
  offsetsL : Array ℕ
  startR : ℕ
  endR : ℕ
  offsetsR : Array ℕ

private def blockCoreState
    (blockL blockR : ℕ) (core : BlockCoreResult T) :
    BlockLoopState T := {
  v := core.v
  l := core.l
  r := core.r
  blockL := blockL
  blockR := blockR
  startL := core.startL
  endL := core.endL
  offsetsL := core.offsetsL
  startR := core.startR
  endR := core.endR
  offsetsR := core.offsetsR
}

private def blockLoopStep
    (pivot : T) (isLess : T → T → Bool)
    (state : BlockLoopState T) : ForInStep (BlockLoopState T) :=
  let gap := state.r - state.l
  let isDone := decide (gap ≤ 2 * 128)
  let pendingL := decide (state.startL < state.endL)
  let pendingR := decide (state.startR < state.endR)
  let adjusted := adjustBlockSizes gap state.blockL state.blockR
    pendingL pendingR
  let core := blockCore state.v pivot isLess state.l state.r
    adjusted.1 adjusted.2 state.offsetsL state.offsetsR
    state.startL state.endL state.startR state.endR
  let result := blockCoreState adjusted.1 adjusted.2 core
  if isDone = true then .done result else .yield result

private def BlockPreInv
    (original : Array T) (state : BlockLoopState T) : Prop :=
  List.Perm state.v.toList original.toList ∧
  state.v.size = original.size ∧
  state.l ≤ state.r ∧ state.r ≤ state.v.size ∧
  state.blockL = 128 ∧ state.blockR = 128 ∧
  state.offsetsL.size = 128 ∧ state.offsetsR.size = 128 ∧
  state.startL ≤ state.endL ∧ state.endL ≤ 128 ∧
  state.startR ≤ state.endR ∧ state.endR ≤ 128 ∧
  (∀ j, j < state.endL → state.offsetsL[j]! < 128) ∧
  (∀ j, j < state.endR → state.offsetsR[j]! < 128) ∧
  ¬(state.startL < state.endL ∧
    state.startR < state.endR) ∧
  (state.startL < state.endL → 128 ≤ state.r - state.l) ∧
  (state.startR < state.endR → 128 ≤ state.r - state.l)

private def BlockCleanupInv
    (original : Array T) (state : BlockLoopState T) : Prop :=
  List.Perm state.v.toList original.toList ∧
  state.l ≤ state.r ∧ state.r ≤ state.v.size ∧
  state.v.size = original.size ∧
  state.startL ≤ state.endL ∧
  state.startR ≤ state.endR ∧
  ¬(state.startL < state.endL ∧
    state.startR < state.endR) ∧
  (state.startL < state.endL →
    state.endL - state.startL ≤ state.r ∧
    ∀ j, j < state.endL →
      state.l + state.offsetsL[j]! < state.v.size) ∧
  (state.startR < state.endR →
    state.endR - state.startR ≤ state.r - state.l ∧
    ∀ j, j < state.endR →
      state.offsetsR[j]! < state.r)

private def BlockOrderInv
    (pivot : T) (isLess : T → T → Bool)
    (state : BlockLoopState T) : Prop :=
  RangeAll state.v 0 state.l
      (fun item => isLess item pivot = true) ∧
    RangeAll state.v state.r state.v.size
      (fun item => isLess item pivot = false) ∧
    (state.startL ≠ state.endL →
      OffsetScanExact state.blockL state.startL state.endL
        state.offsetsL
        (fun offset => !isLess state.v[state.l + offset]! pivot)) ∧
    (state.startR ≠ state.endR →
      OffsetScanExact state.blockR state.startR state.endR
        state.offsetsR
        (fun offset => isLess state.v[state.r - 1 - offset]! pivot))

private def BlockDoneShape (state : BlockLoopState T) : Prop :=
  state.offsetsL.size = 128 ∧ state.offsetsR.size = 128 ∧
    state.endL ≤ 128 ∧ state.endR ≤ 128 ∧
    (state.startL < state.endL →
      state.l + state.blockL = state.r) ∧
    (state.startR < state.endR →
      state.l + state.blockR = state.r) ∧
    (state.startL = state.endL → state.startR = state.endR →
      state.l = state.r)

omit [Inhabited T] in
private theorem blockPreInv_cleanup
    (original : Array T) (state : BlockLoopState T)
    (hinv : BlockPreInv original state) :
    BlockCleanupInv original state := by
  rcases hinv with
    ⟨hperm, hsize, hlr, hrsize, hblockL, hblockR,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL,
      hpendingR⟩
  refine ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
    hatMostOne, ?_, ?_⟩
  · intro hpending
    constructor
    · have hgap := hpendingL hpending
      omega
    · intro j hj
      have hoff := hactiveL j hj
      have hgap := hpendingL hpending
      omega
  · intro hpending
    constructor
    · have hgap := hpendingR hpending
      omega
    · intro j hj
      have hoff := hactiveR j hj
      have hgap := hpendingR hpending
      omega

private theorem blockCore_cursor_eq
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    let result := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    result.l =
        (if result.startL = result.endL then l + blockL else l) ∧
      result.r =
        (if result.startR = result.endR then r - blockR else r) := by
  simp [blockCore]

private theorem blockCore_orderInv
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hblockL : blockL ≤ offsetsL.size)
    (hblockR : blockR ≤ offsetsR.size)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR)
    (hprefix : RangeAll a 0 l
      (fun item => isLess item pivot = true))
    (hsuffix : RangeAll a r a.size
      (fun item => isLess item pivot = false))
    (hexactL : startL ≠ endL →
      OffsetScanExact blockL startL endL offsetsL
        (fun offset => !isLess a[l + offset]! pivot))
    (hexactR : startR ≠ endR →
      OffsetScanExact blockR startR endR offsetsR
        (fun offset => isLess a[r - 1 - offset]! pivot)) :
    let core := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    BlockOrderInv pivot isLess (blockCoreState blockL blockR core) := by
  let core := blockCore a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
  have hcoreExact :
      OffsetScanExact blockL core.startL core.endL core.offsetsL
          (fun offset => !isLess core.v[l + offset]! pivot) ∧
        OffsetScanExact blockR core.startR core.endR core.offsetsR
          (fun offset => isLess core.v[r - 1 - offset]! pivot) ∧
        ∀ position, position < l ∨ r ≤ position →
          core.v[position]! = a[position]! := by
    simpa only [core] using blockCore_offsets_exact a pivot isLess
      l r blockL blockR offsetsL offsetsR startL endL startR endR
      hlr hrsize hblocks hblockL hblockR hstartL hendL
      hstartR hendR hactiveL hactiveR hexactL hexactR
  have hcursor :
      core.l =
          (if core.startL = core.endL then l + blockL else l) ∧
        core.r =
          (if core.startR = core.endR then r - blockR else r) := by
    simpa only [core] using blockCore_cursor_eq a pivot isLess
      l r blockL blockR offsetsL offsetsR startL endL startR endR
  have hprefixTransfer : RangeAll core.v 0 l
      (fun item => isLess item pivot = true) :=
    RangeAll.transfer hprefix (by
      intro position _ hposition
      exact hcoreExact.2.2 position (Or.inl hposition))
  have hsuffixTransfer : RangeAll core.v r core.v.size
      (fun item => isLess item pivot = false) := by
    have hcoreSize : core.v.size = a.size := by
      simpa only [core, blockCore] using blockMutateArray_size
        a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR
    rw [hcoreSize]
    apply RangeAll.transfer hsuffix
    intro position hposition hsize
    exact hcoreExact.2.2 position (Or.inr hposition)
  unfold BlockOrderInv
  simp only [blockCoreState]
  constructor
  · by_cases hdone : core.startL = core.endL
    · rw [hcursor.1, if_pos hdone]
      apply RangeAll.append hprefixTransfer
      exact exhausted_left_block_rangeAll core.v pivot isLess
        l blockL core.endL core.offsetsL (by simpa [hdone] using hcoreExact.1)
    · rw [hcursor.1, if_neg hdone]
      exact hprefixTransfer
  constructor
  · by_cases hdone : core.startR = core.endR
    · rw [hcursor.2, if_pos hdone]
      apply RangeAll.append
      · exact exhausted_right_block_rangeAll core.v pivot isLess
          r blockR core.endR core.offsetsR
          (right_block_le l r blockL blockR hblocks)
          (by simpa [hdone] using hcoreExact.2.1)
      · exact hsuffixTransfer
    · rw [hcursor.2, if_neg hdone]
      exact hsuffixTransfer
  constructor
  · intro hpending
    rw [hcursor.1, if_neg hpending]
    exact hcoreExact.1
  · intro hpending
    rw [hcursor.2, if_neg hpending]
    exact hcoreExact.2.1

omit [Inhabited T] in
private theorem blockCleanupInv_coreState
    (original : Array T) (blockL blockR : ℕ)
    (core : BlockCoreResult T)
    (hperm : List.Perm core.v.toList original.toList)
    (hlr : core.l ≤ core.r) (hrsize : core.r ≤ core.v.size)
    (hsize : core.v.size = original.size)
    (hstartL : core.startL ≤ core.endL)
    (hstartR : core.startR ≤ core.endR)
    (hatMostOne :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR))
    (hleft : core.startL < core.endL →
      core.endL - core.startL ≤ core.r ∧
      ∀ j, j < core.endL →
        core.l + core.offsetsL[j]! < core.v.size)
    (hright : core.startR < core.endR →
      core.endR - core.startR ≤ core.r - core.l ∧
      ∀ j, j < core.endR →
        core.offsetsR[j]! < core.r) :
    BlockCleanupInv original
      (blockCoreState blockL blockR core) := by
  exact ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
    hatMostOne, hleft, hright⟩

omit [Inhabited T] in
private theorem core_pending_left_cleanup
    (core : BlockCoreResult T)
    (aSize l r blockL blockR : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hcoreSize : core.v.size = aSize)
    (hend : core.endL ≤ blockL)
    (hactive : ∀ j, j < core.endL →
      core.offsetsL[j]! < blockL)
    (hexhaust :
      core.startL = core.endL ∨
        core.startR = core.endR)
    (hcursorL :
      core.l =
        if core.startL = core.endL then l + blockL else l)
    (hcursorR :
      core.r =
        if core.startR = core.endR then r - blockR else r)
    (hrsize : r ≤ aSize) :
    core.startL < core.endL →
      core.endL - core.startL ≤ core.r ∧
      ∀ j, j < core.endL →
        core.l + core.offsetsL[j]! < core.v.size := by
  intro hpending
  have hdoneR : core.startR = core.endR := by
    rcases hexhaust with hdoneL | hdoneR
    · omega
    · exact hdoneR
  have hlEq : core.l = l := by
    rw [hcursorL, if_neg (ne_of_lt hpending)]
  have hrEq : core.r = r - blockR := by
    rw [hcursorR, if_pos hdoneR]
  constructor
  · rw [hrEq]
    omega
  · intro j hj
    have hoff := hactive j hj
    rw [hlEq, hcoreSize]
    omega

omit [Inhabited T] in
private theorem core_pending_right_cleanup
    (core : BlockCoreResult T)
    (l r blockL blockR : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hend : core.endR ≤ blockR)
    (hactive : ∀ j, j < core.endR →
      core.offsetsR[j]! < blockR)
    (hexhaust :
      core.startL = core.endL ∨
        core.startR = core.endR)
    (hcursorL :
      core.l =
        if core.startL = core.endL then l + blockL else l)
    (hcursorR :
      core.r =
        if core.startR = core.endR then r - blockR else r) :
    core.startR < core.endR →
      core.endR - core.startR ≤ core.r - core.l ∧
      ∀ j, j < core.endR →
        core.offsetsR[j]! < core.r := by
  intro hpending
  have hdoneL : core.startL = core.endL := by
    rcases hexhaust with hdoneL | hdoneR
    · exact hdoneL
    · omega
  have hlEq : core.l = l + blockL := by
    rw [hcursorL, if_pos hdoneL]
  have hrEq : core.r = r := by
    rw [hcursorR, if_neg (ne_of_lt hpending)]
  constructor
  · rw [hlEq, hrEq]
    omega
  · intro j hj
    have hoff := hactive j hj
    rw [hrEq]
    have hblockRr : blockR ≤ r := by omega
    exact hoff.trans_le hblockRr

omit [Inhabited T] in
private theorem blockPreInv_coreState
    (original : Array T) (core : BlockCoreResult T)
    (hperm : List.Perm core.v.toList original.toList)
    (hsize : core.v.size = original.size)
    (hlr : core.l ≤ core.r) (hrsize : core.r ≤ core.v.size)
    (hsizeL : core.offsetsL.size = 128)
    (hsizeR : core.offsetsR.size = 128)
    (hstartL : core.startL ≤ core.endL)
    (hendL : core.endL ≤ 128)
    (hstartR : core.startR ≤ core.endR)
    (hendR : core.endR ≤ 128)
    (hactiveL : ∀ j, j < core.endL →
      core.offsetsL[j]! < 128)
    (hactiveR : ∀ j, j < core.endR →
      core.offsetsR[j]! < 128)
    (hatMostOne :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR))
    (hpendingL :
      core.startL < core.endL →
        128 ≤ core.r - core.l)
    (hpendingR :
      core.startR < core.endR →
        128 ≤ core.r - core.l) :
    BlockPreInv original (blockCoreState 128 128 core) := by
  exact ⟨hperm, hsize, hlr, hrsize, rfl, rfl,
    hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
    hactiveL, hactiveR, hatMostOne, hpendingL, hpendingR⟩

omit [Inhabited T] in
private theorem yielded_core_pending_gap
    (core : BlockCoreResult T) (l r : ℕ)
    (hgap : 2 * 128 < r - l)
    (hexhaust :
      core.startL = core.endL ∨
        core.startR = core.endR)
    (hcursorL :
      core.l =
        if core.startL = core.endL then l + 128 else l)
    (hcursorR :
      core.r =
        if core.startR = core.endR then r - 128 else r) :
    (core.startL < core.endL →
      128 ≤ core.r - core.l) ∧
    (core.startR < core.endR →
      128 ≤ core.r - core.l) := by
  constructor
  · intro hpendingL
    have hdoneR : core.startR = core.endR := by
      rcases hexhaust with hdoneL | hdoneR
      · omega
      · exact hdoneR
    rw [hcursorL, if_neg (ne_of_lt hpendingL),
      hcursorR, if_pos hdoneR]
    omega
  · intro hpendingR
    have hdoneL : core.startL = core.endL := by
      rcases hexhaust with hdoneL | hdoneR
      · exact hdoneL
      · omega
    rw [hcursorL, if_pos hdoneL,
      hcursorR, if_neg (ne_of_lt hpendingR)]
    omega

private theorem blockCoreState_cleanup
    (original a : Array T) (pivot : T)
    (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hperm : List.Perm a.toList original.toList)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    let core := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    BlockCleanupInv original
      (blockCoreState blockL blockR core) := by
  let core := blockCore a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
  have hcorePerm : List.Perm core.v.toList original.toList :=
    (blockCore_perm a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
      hlr hrsize
      (by omega) (by omega)
      hsizeL hsizeR hblockL hblockR
      hstartL hendL hstartR hendR hactiveL hactiveR).trans
      hperm
  have hcursorRaw := blockCore_cursor_bounds a pivot isLess
    l r blockL blockR offsetsL offsetsR
    startL endL startR endR a.size hlr hrsize hblocks
  change core.l ≤ core.r ∧ core.r ≤ a.size at hcursorRaw
  have hcursor := hcursorRaw
  have hoffsetsRaw := blockCore_offset_bounds a pivot isLess
    l r blockL blockR offsetsL offsetsR
    startL endL startR endR hsizeL hsizeR
    hblockL hblockR hstartL hendL hstartR hendR
    hactiveL hactiveR
  change
      core.startL ≤ core.endL ∧
      core.endL ≤ blockL ∧
      core.offsetsL.size = 128 ∧
      (∀ j, j < core.endL → core.offsetsL[j]! < blockL) ∧
      core.startR ≤ core.endR ∧
      core.endR ≤ blockR ∧
      core.offsetsR.size = 128 ∧
      (∀ j, j < core.endR → core.offsetsR[j]! < blockR) ∧
      (core.startL = core.endL ∨
        core.startR = core.endR) at hoffsetsRaw
  have hoffsets := hoffsetsRaw
  rcases hoffsets with
    ⟨hcStartL, hcEndL, hcSizeL, hcActiveL,
      hcStartR, hcEndR, hcSizeR, hcActiveR, hcExhaust⟩
  have hcursorEqRaw := blockCore_cursor_eq a pivot isLess
    l r blockL blockR offsetsL offsetsR
    startL endL startR endR
  change
      core.l =
          (if core.startL = core.endL then l + blockL else l) ∧
        core.r =
          (if core.startR = core.endR then r - blockR else r)
    at hcursorEqRaw
  have hcursorEq := hcursorEqRaw
  have hcoreSize : core.v.size = original.size := by
    simpa using hcorePerm.length_eq
  have hcoreASize : core.v.size = a.size := by
    have haSize : a.size = original.size := by
      simpa using hperm.length_eq
    omega
  have hatMostOne :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR) := by
    intro hpending
    rcases hcExhaust with hdoneL | hdoneR
    · omega
    · omega
  apply blockCleanupInv_coreState original blockL blockR core
    hcorePerm hcursor.1
    (hcursor.2.trans_eq hcoreASize.symm)
    hcoreSize hcStartL hcStartR hatMostOne
  · exact core_pending_left_cleanup core a.size l r
      blockL blockR hblocks hcoreASize hcEndL hcActiveL
      hcExhaust hcursorEq.1 hcursorEq.2 hrsize
  · exact core_pending_right_cleanup core l r blockL blockR
      hblocks hcEndR hcActiveR hcExhaust
      hcursorEq.1 hcursorEq.2

private theorem blockLoopStep_cleanup
    (original : Array T) (pivot : T)
    (isLess : T → T → Bool) (state : BlockLoopState T)
    (hinv : BlockPreInv original state) :
    match blockLoopStep pivot isLess state with
    | .done result => BlockCleanupInv original result
    | .yield result => BlockCleanupInv original result := by
  rcases state with
    ⟨a, l, r, blockL, blockR, startL, endL, offsetsL,
      startR, endR, offsetsR⟩
  simp only [BlockPreInv] at hinv
  rcases hinv with
    ⟨hperm, hsize, hlr, hrsize, hblockLEq, hblockREq,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL,
      hpendingR⟩
  let gap := r - l
  let pendingL := decide (startL < endL)
  let pendingR := decide (startR < endR)
  let adjusted := adjustBlockSizes gap blockL blockR
    pendingL pendingR
  have hadjust := adjustBlockSizes_bounds gap blockL blockR
    pendingL pendingR
    (by
      intro hlarge
      exact ⟨by omega, by omega, by omega⟩)
    (by
      intro hdone hpending
      have hp : startL < endL := by
        simpa [pendingL] using hpending
      exact ⟨hblockLEq, hpendingL hp⟩)
    (by
      intro hdone hpending
      have hp : startR < endR := by
        simpa [pendingR] using hpending
      exact ⟨hblockREq, hpendingR hp⟩)
  have hleftEnd :
      startL ≠ endL → endL ≤ adjusted.1 := by
    intro hne
    have hp : startL < endL := by omega
    have hadjustLeft : adjusted.1 = blockL := by
      simp only [adjusted, adjustBlockSizes]
      by_cases hdone : gap ≤ 2 * 128 <;>
        simp [hdone, pendingL, hp]
    omega
  have hrightEnd :
      startR ≠ endR → endR ≤ adjusted.2 := by
    intro hne
    have hp : startR < endR := by omega
    have hpBool : pendingR = true := by simp [pendingR, hp]
    have hleftFalse : pendingL = false := by
      simp only [pendingL, decide_eq_false_iff_not]
      intro hpLeft
      exact hatMostOne ⟨hpLeft, hp⟩
    have hadjustRight : adjusted.2 = blockR := by
      simp only [adjusted, adjustBlockSizes]
      by_cases hdone : gap ≤ 2 * 128 <;>
        simp [hdone, pendingR, hp, hleftFalse]
    omega
  have hcleanup := blockCoreState_cleanup original a pivot isLess
    l r adjusted.1 adjusted.2 offsetsL offsetsR
    startL endL startR endR hperm hlr
    (by omega) hadjust.2.2 hsizeL hsizeR
    hadjust.1 hadjust.2.1 hstartL hleftEnd
    hstartR hrightEnd
    (by
      intro hne j hj
      have hp : startL < endL := by omega
      have hadjustLeft : adjusted.1 = blockL := by
        simp only [adjusted, adjustBlockSizes]
        by_cases hdone : gap ≤ 2 * 128 <;>
          simp [hdone, pendingL, hp]
      simpa [hadjustLeft, hblockLEq] using hactiveL j hj)
    (by
      intro hne j hj
      have hp : startR < endR := by omega
      have hleftFalse : pendingL = false := by
        simp only [pendingL, decide_eq_false_iff_not]
        intro hpLeft
        exact hatMostOne ⟨hpLeft, hp⟩
      have hadjustRight : adjusted.2 = blockR := by
        simp only [adjusted, adjustBlockSizes]
        by_cases hdone : gap ≤ 2 * 128 <;>
          simp [hdone, pendingR, hp, hleftFalse]
      simpa [hadjustRight, hblockREq] using hactiveR j hj)
  by_cases hdone : gap ≤ 2 * 128
  · simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      hdone] using hcleanup
  · simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      hdone] using hcleanup

private theorem blockLoopStep_order
    (original : Array T) (pivot : T)
    (isLess : T → T → Bool) (state : BlockLoopState T)
    (hpre : BlockPreInv original state)
    (horder : BlockOrderInv pivot isLess state) :
    match blockLoopStep pivot isLess state with
    | .done result =>
        BlockOrderInv pivot isLess result ∧ BlockDoneShape result
    | .yield result => BlockOrderInv pivot isLess result := by
  rcases state with
    ⟨a, l, r, blockL, blockR, startL, endL, offsetsL,
      startR, endR, offsetsR⟩
  simp only [BlockPreInv] at hpre
  rcases hpre with
    ⟨hperm, hsize, hlr, hrsize, hblockLEq, hblockREq,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL, hpendingR⟩
  simp only [BlockOrderInv] at horder
  rcases horder with ⟨hprefix, hsuffix, hexactL, hexactR⟩
  let gap := r - l
  let pendingL := decide (startL < endL)
  let pendingR := decide (startR < endR)
  let adjusted := adjustBlockSizes gap blockL blockR pendingL pendingR
  have hadjust := adjustBlockSizes_bounds gap blockL blockR
    pendingL pendingR
    (by
      intro hlarge
      exact ⟨by omega, by omega, by omega⟩)
    (by
      intro hdone hpending
      have hp : startL < endL := by simpa [pendingL] using hpending
      exact ⟨hblockLEq, hpendingL hp⟩)
    (by
      intro hdone hpending
      have hp : startR < endR := by simpa [pendingR] using hpending
      exact ⟨hblockREq, hpendingR hp⟩)
  have hadjustLeft : startL ≠ endL → adjusted.1 = blockL := by
    intro hne
    have hp : startL < endL := by omega
    simp only [adjusted, adjustBlockSizes]
    by_cases hdone : gap ≤ 2 * 128 <;> simp [hdone, pendingL, hp]
  have hadjustRight : startR ≠ endR → adjusted.2 = blockR := by
    intro hne
    have hp : startR < endR := by omega
    have hleftFalse : pendingL = false := by
      simp only [pendingL, decide_eq_false_iff_not]
      intro hpLeft
      exact hatMostOne ⟨hpLeft, hp⟩
    simp only [adjusted, adjustBlockSizes]
    by_cases hdone : gap ≤ 2 * 128 <;>
      simp [hdone, pendingR, hp, hleftFalse]
  let core := blockCore a pivot isLess l r adjusted.1 adjusted.2
    offsetsL offsetsR startL endL startR endR
  have hcoreOrder : BlockOrderInv pivot isLess
      (blockCoreState adjusted.1 adjusted.2 core) := by
    simpa only [core] using blockCore_orderInv a pivot isLess
      l r adjusted.1 adjusted.2 offsetsL offsetsR
      startL endL startR endR hlr (by omega) hadjust.2.2
      (hadjust.1.trans_eq hsizeL.symm)
      (hadjust.2.1.trans_eq hsizeR.symm)
      hstartL (fun hne => by
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hendL)
      hstartR (fun hne => by
        rw [hadjustRight hne]
        simpa only [hblockREq] using hendR)
      (by
        intro hne j hj
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hactiveL j hj)
      (by
        intro hne j hj
        rw [hadjustRight hne]
        simpa only [hblockREq] using hactiveR j hj)
      hprefix hsuffix
      (by
        intro hne
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hexactL hne)
      (by
        intro hne
        rw [hadjustRight hne]
        simpa only [hblockREq] using hexactR hne)
  by_cases hdone : gap ≤ 2 * 128
  · have hadjustDone : adjusted.1 + adjusted.2 = gap :=
      (adjustBlockSizes_done gap blockL blockR pendingL pendingR hdone
        (by
          intro hpending
          have hp : startL < endL := by simpa [pendingL] using hpending
          exact ⟨hblockLEq, hpendingL hp⟩)
        (by
          intro hpending
          have hp : startR < endR := by simpa [pendingR] using hpending
          exact ⟨hblockREq, hpendingR hp⟩)).2.2
    have hoffsets := blockCore_offset_bounds a pivot isLess
      l r adjusted.1 adjusted.2 offsetsL offsetsR
      startL endL startR endR hsizeL hsizeR hadjust.1 hadjust.2.1
      hstartL (fun hne => by
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hendL)
      hstartR (fun hne => by
        rw [hadjustRight hne]
        simpa only [hblockREq] using hendR)
      (by
        intro hne j hj
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hactiveL j hj)
      (by
        intro hne j hj
        rw [hadjustRight hne]
        simpa only [hblockREq] using hactiveR j hj)
    have hoffsetsCore :
        core.startL ≤ core.endL ∧ core.endL ≤ adjusted.1 ∧
        core.offsetsL.size = 128 ∧
        (∀ j, j < core.endL → core.offsetsL[j]! < adjusted.1) ∧
        core.startR ≤ core.endR ∧ core.endR ≤ adjusted.2 ∧
        core.offsetsR.size = 128 ∧
        (∀ j, j < core.endR → core.offsetsR[j]! < adjusted.2) ∧
        (core.startL = core.endL ∨ core.startR = core.endR) := by
      simpa only [core] using hoffsets
    rcases hoffsetsCore with
      ⟨_, hcoreEndL, hcoreSizeL, _, _, hcoreEndR,
        hcoreSizeR, _, hexhaust⟩
    have hcursor :
        core.l =
            (if core.startL = core.endL then l + adjusted.1 else l) ∧
          core.r =
            (if core.startR = core.endR then r - adjusted.2 else r) := by
      simpa only [core] using blockCore_cursor_eq a pivot isLess
        l r adjusted.1 adjusted.2 offsetsL offsetsR
        startL endL startR endR
    have hshape : BlockDoneShape
        (blockCoreState adjusted.1 adjusted.2 core) := by
      unfold BlockDoneShape
      simp only [blockCoreState]
      refine ⟨hcoreSizeL, hcoreSizeR,
        hcoreEndL.trans hadjust.1, hcoreEndR.trans hadjust.2.1,
        ?_, ?_, ?_⟩
      · intro hpending
        have hdoneR : core.startR = core.endR := by
          rcases hexhaust with hdoneL | hdoneR
          · omega
          · exact hdoneR
        rw [hcursor.1, if_neg (ne_of_lt hpending),
          hcursor.2, if_pos hdoneR]
        simp only [gap] at hadjustDone
        omega
      · intro hpending
        have hdoneL : core.startL = core.endL := by
          rcases hexhaust with hdoneL | hdoneR
          · exact hdoneL
          · omega
        rw [hcursor.1, if_pos hdoneL,
          hcursor.2, if_neg (ne_of_lt hpending)]
        simp only [gap] at hadjustDone
        omega
      · intro hdoneL hdoneR
        rw [hcursor.1, if_pos hdoneL, hcursor.2, if_pos hdoneR]
        simp only [gap] at hadjustDone
        omega
    simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      core, hdone] using And.intro hcoreOrder hshape
  · simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      core, hdone] using hcoreOrder

private theorem blockLoopStep_yield_pre
    (original : Array T) (pivot : T)
    (isLess : T → T → Bool)
    (state result : BlockLoopState T)
    (hinv : BlockPreInv original state)
    (hstep : blockLoopStep pivot isLess state = .yield result) :
    BlockPreInv original result ∧
      result.r - result.l < state.r - state.l := by
  rcases state with
    ⟨a, l, r, blockL, blockR, startL, endL, offsetsL,
      startR, endR, offsetsR⟩
  simp only [BlockPreInv] at hinv
  rcases hinv with
    ⟨hperm, hsize, hlr, hrsize, hblockLEq, hblockREq,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL,
      hpendingR⟩
  subst blockL
  subst blockR
  let core := blockCore a pivot isLess l r 128 128
    offsetsL offsetsR startL endL startR endR
  have hnotDone : ¬r - l ≤ 2 * 128 := by
    intro hdone
    simp [blockLoopStep, adjustBlockSizes, hdone] at hstep
  have hresult :
      result = blockCoreState 128 128 core := by
    simpa [blockLoopStep, adjustBlockSizes, hnotDone, core]
      using hstep.symm
  subst result
  have hgap : 2 * 128 < r - l := by omega
  have hcorePerm : List.Perm core.v.toList original.toList :=
    (blockCore_perm a pivot isLess l r 128 128
      offsetsL offsetsR startL endL startR endR
      hlr (by omega) (by omega) (by omega)
      hsizeL hsizeR (by omega) (by omega)
      hstartL (fun _ => hendL) hstartR (fun _ => hendR)
      (fun _ => hactiveL) (fun _ => hactiveR)).trans hperm
  have hcursorRaw := blockCore_cursor_bounds a pivot isLess
    l r 128 128 offsetsL offsetsR
    startL endL startR endR a.size hlr (by omega)
    (by omega)
  change core.l ≤ core.r ∧ core.r ≤ a.size at hcursorRaw
  have hoffsetsRaw := blockCore_offset_bounds a pivot isLess
    l r 128 128 offsetsL offsetsR
    startL endL startR endR hsizeL hsizeR
    (by omega) (by omega)
    hstartL (fun _ => hendL) hstartR (fun _ => hendR)
    (fun _ => hactiveL) (fun _ => hactiveR)
  change
    core.startL ≤ core.endL ∧
    core.endL ≤ 128 ∧ core.offsetsL.size = 128 ∧
    (∀ j, j < core.endL → core.offsetsL[j]! < 128) ∧
    core.startR ≤ core.endR ∧
    core.endR ≤ 128 ∧ core.offsetsR.size = 128 ∧
    (∀ j, j < core.endR → core.offsetsR[j]! < 128) ∧
    (core.startL = core.endL ∨ core.startR = core.endR)
      at hoffsetsRaw
  rcases hoffsetsRaw with
    ⟨hcStartL, hcEndL, hcSizeL, hcActiveL,
      hcStartR, hcEndR, hcSizeR, hcActiveR, hcExhaust⟩
  have hcursorEqRaw := blockCore_cursor_eq a pivot isLess
    l r 128 128 offsetsL offsetsR
    startL endL startR endR
  change
    core.l =
        (if core.startL = core.endL then l + 128 else l) ∧
      core.r =
        (if core.startR = core.endR then r - 128 else r)
    at hcursorEqRaw
  have hpendingGap := yielded_core_pending_gap core l r
    hgap hcExhaust hcursorEqRaw.1 hcursorEqRaw.2
  have hgapDecrease : core.r - core.l < r - l := by
    rcases hcExhaust with hdoneL | hdoneR
    · rw [hcursorEqRaw.1, if_pos hdoneL]
      by_cases hdoneRight : core.startR = core.endR
      · rw [hcursorEqRaw.2, if_pos hdoneRight]
        omega
      · rw [hcursorEqRaw.2, if_neg hdoneRight]
        omega
    · rw [hcursorEqRaw.2, if_pos hdoneR]
      by_cases hdoneLeft : core.startL = core.endL
      · rw [hcursorEqRaw.1, if_pos hdoneLeft]
        omega
      · rw [hcursorEqRaw.1, if_neg hdoneLeft]
        omega
  have hcoreSize : core.v.size = original.size := by
    simpa using hcorePerm.length_eq
  have hcoreASize : core.v.size = a.size := by omega
  have hatMostOneCore :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR) := by
    intro hpending
    rcases hcExhaust with hdoneL | hdoneR <;> omega
  exact ⟨blockPreInv_coreState original core hcorePerm hcoreSize
      hcursorRaw.1 (hcursorRaw.2.trans_eq hcoreASize.symm)
      hcSizeL hcSizeR hcStartL hcEndL hcStartR hcEndR
      hcActiveL hcActiveR hatMostOneCore
      hpendingGap.1 hpendingGap.2,
    hgapDecrease⟩

private theorem blockLoop_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let initial : BlockLoopState T := {
      v := v
      l := 0
      r := v.size
      blockL := 128
      blockR := 128
      startL := 0
      endL := 0
      offsetsL := Array.replicate 128 0
      startR := 0
      endR := 0
      offsetsR := Array.replicate 128 0
    }
    let result := Id.run <|
      forIn (List.range' 0 (v.size + 4)) initial
        fun _ state => pure (blockLoopStep pivot isLess state)
    BlockCleanupInv v result := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  apply forIn_step_post
    (BlockPreInv v) (BlockCleanupInv v)
    (fun _ state => blockLoopStep pivot isLess state)
  · intro _ state result hinv hstep
    exact blockLoopStep_yield_pre v pivot isLess
      state result hinv hstep |>.1
  · intro _ state result hinv hstep
    have hout := blockLoopStep_cleanup v pivot isLess state hinv
    rw [hstep] at hout
    exact hout
  · exact blockPreInv_cleanup v
  · show BlockPreInv v initial
    simp [BlockPreInv, initial]

private theorem blockLoop_order_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let initial : BlockLoopState T := {
      v := v
      l := 0
      r := v.size
      blockL := 128
      blockR := 128
      startL := 0
      endL := 0
      offsetsL := Array.replicate 128 0
      startR := 0
      endR := 0
      offsetsR := Array.replicate 128 0
    }
    let result := Id.run <|
      forIn (List.range' 0 (v.size + 4)) initial
        fun _ state => pure (blockLoopStep pivot isLess state)
    BlockCleanupInv v result ∧ BlockOrderInv pivot isLess result ∧
      BlockDoneShape result := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  apply forIn_step_decreasing_post
    (fun state => BlockPreInv v state ∧
      BlockOrderInv pivot isLess state)
    (fun state => BlockCleanupInv v state ∧
      BlockOrderInv pivot isLess state ∧ BlockDoneShape state)
    (fun state => state.r - state.l)
    (fun _ state => blockLoopStep pivot isLess state)
  · intro _ state result hinv hstep
    have hprogress := blockLoopStep_yield_pre v pivot isLess
      state result hinv.1 hstep
    have horder := blockLoopStep_order v pivot isLess state
      hinv.1 hinv.2
    rw [hstep] at horder
    exact ⟨⟨hprogress.1, horder⟩, hprogress.2⟩
  · intro _ state result hinv hstep
    have hcleanup := blockLoopStep_cleanup v pivot isLess state hinv.1
    have horder := blockLoopStep_order v pivot isLess state
      hinv.1 hinv.2
    rw [hstep] at hcleanup horder
    exact ⟨hcleanup, horder.1, horder.2⟩
  · constructor
    · show BlockPreInv v initial
      simp [BlockPreInv, initial]
    · show BlockOrderInv pivot isLess initial
      simp [BlockOrderInv, initial, RangeAll.empty]
  · simp

private def partitionInBlocksFactored
    (v : Array T) (pivot : T)
    (isLess : T → T → Bool) : ℕ × Array T :=
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  let state := Id.run <|
    forIn (List.range' 0 (v.size + 4)) initial
      fun _ state => pure (blockLoopStep pivot isLess state)
  if state.startL < state.endL then
    let result := cleanupLeft (List.range' 0 (128 + 1))
      state.startL state.l state.offsetsL
      ⟨state.endL, state.r, state.v⟩
    (result.2.1, result.2.2)
  else if state.startR < state.endR then
    let result := cleanupRight (List.range' 0 (128 + 1))
      state.startR state.r state.offsetsR
      ⟨state.endR, state.l, state.v⟩
    (result.2.1, result.2.2)
  else
    (state.l, state.v)

private theorem partitionInBlocksFactored_eq
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let initial : BlockLoopState T := {
      v := v
      l := 0
      r := v.size
      blockL := 128
      blockR := 128
      startL := 0
      endL := 0
      offsetsL := Array.replicate 128 0
      startR := 0
      endR := 0
      offsetsR := Array.replicate 128 0
    }
    let state := Id.run <|
      forIn (List.range' 0 (v.size + 4)) initial
        fun _ state => pure (blockLoopStep pivot isLess state)
    partitionInBlocksFactored v pivot isLess =
      if state.startL < state.endL then
        let result := cleanupLeft (List.range' 0 (128 + 1))
          state.startL state.l state.offsetsL
          ⟨state.endL, state.r, state.v⟩
        (result.2.1, result.2.2)
      else if state.startR < state.endR then
        let result := cleanupRight (List.range' 0 (128 + 1))
          state.startR state.r state.offsetsR
          ⟨state.endR, state.l, state.v⟩
        (result.2.1, result.2.2)
      else
        (state.l, state.v) := by
  rfl

theorem partitionInBlocksFactored_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocksFactored v pivot isLess
    result.1 ≤ v.size ∧
      List.Perm result.2.toList v.toList := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  let state := Id.run <|
    forIn (List.range' 0 (v.size + 4)) initial
      fun _ state => pure (blockLoopStep pivot isLess state)
  have hinv := blockLoop_contract v pivot isLess
  change BlockCleanupInv v state at hinv
  rcases hinv with
    ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
      hatMostOne, hleft, hright⟩
  unfold partitionInBlocksFactored
  change
    (if state.startL < state.endL then
      let result := cleanupLeft (List.range' 0 (128 + 1))
        state.startL state.l state.offsetsL
        ⟨state.endL, state.r, state.v⟩
      (result.2.1, result.2.2)
    else if state.startR < state.endR then
      let result := cleanupRight (List.range' 0 (128 + 1))
        state.startR state.r state.offsetsR
        ⟨state.endR, state.l, state.v⟩
      (result.2.1, result.2.2)
    else
      (state.l, state.v)).1 ≤ v.size ∧
    List.Perm
      (if state.startL < state.endL then
        let result := cleanupLeft (List.range' 0 (128 + 1))
          state.startL state.l state.offsetsL
          ⟨state.endL, state.r, state.v⟩
        (result.2.1, result.2.2)
      else if state.startR < state.endR then
        let result := cleanupRight (List.range' 0 (128 + 1))
          state.startR state.r state.offsetsR
          ⟨state.endR, state.l, state.v⟩
        (result.2.1, result.2.2)
      else
        (state.l, state.v)).2.toList
      v.toList
  by_cases hpendingL : state.startL < state.endL
  · simp only [if_pos hpendingL]
    have hfacts := hleft hpendingL
    exact cleanupLeft_contract (T := T)
      (List.range' 0 (128 + 1))
      state.startL state.l state.offsetsL
      state.endL state.r state.v v
      hstartL hfacts.1 hrsize hfacts.2 hperm
  · simp only [if_neg hpendingL]
    by_cases hpendingR : state.startR < state.endR
    · simp only [if_pos hpendingR]
      have hfacts := hright hpendingR
      exact cleanupRight_contract (T := T)
        (List.range' 0 (128 + 1))
        state.startR state.r state.offsetsR
        state.endR state.l state.v v
        hstartR hlr hfacts.1 hrsize hfacts.2 hperm
    · simp only [if_neg hpendingR]
      exact ⟨by omega, hperm⟩

theorem partitionInBlocksFactored_order
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocksFactored v pivot isLess
    RangeAll result.2 0 result.1
        (fun item => isLess item pivot = true) ∧
      RangeAll result.2 result.1 result.2.size
        (fun item => isLess item pivot = false) := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  let state := Id.run <|
    forIn (List.range' 0 (v.size + 4)) initial
      fun _ state => pure (blockLoopStep pivot isLess state)
  have hinv := blockLoop_order_contract v pivot isLess
  have htyped : BlockCleanupInv v state ∧
      BlockOrderInv pivot isLess state ∧ BlockDoneShape state := by
    simpa only [initial, state] using hinv
  rcases htyped with ⟨hcleanup, horder, hshape⟩
  simp only [BlockCleanupInv] at hcleanup
  rcases hcleanup with
    ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
      hatMostOne, hleft, hright⟩
  simp only [BlockOrderInv] at horder
  rcases horder with ⟨hprefix, hsuffix, hexactL, hexactR⟩
  simp only [BlockDoneShape] at hshape
  rcases hshape with
    ⟨hsizeL, hsizeR, hendL, hendR, hleftShape,
      hrightShape, hclosed⟩
  have hpartition : partitionInBlocksFactored v pivot isLess =
      (if state.startL < state.endL then
        let result := cleanupLeft (List.range' 0 (128 + 1))
          state.startL state.l state.offsetsL
          ⟨state.endL, state.r, state.v⟩
        (result.2.1, result.2.2)
      else if state.startR < state.endR then
        let result := cleanupRight (List.range' 0 (128 + 1))
          state.startR state.r state.offsetsR
          ⟨state.endR, state.l, state.v⟩
        (result.2.1, result.2.2)
      else (state.l, state.v)) := by
    simpa only [initial, state] using
      partitionInBlocksFactored_eq v pivot isLess
  rw [hpartition]
  by_cases hpendingL : state.startL < state.endL
  · simp only [if_pos hpendingL]
    have hblock : state.blockL = state.r - state.l := by
      have := hleftShape hpendingL
      omega
    have hresult := cleanupLeft_order (T := T)
      (List.range' 0 (128 + 1)) pivot isLess
      state.startL state.l state.offsetsL
      state.endL state.r state.v hstartL (by
        simp
        omega) hlr hrsize (by omega) hprefix hsuffix (by
          simpa only [hblock] using
            hexactL (ne_of_lt hpendingL))
    simpa only [initial, state] using hresult
  · simp only [if_neg hpendingL]
    by_cases hpendingR : state.startR < state.endR
    · simp only [if_pos hpendingR]
      have hblock : state.blockR = state.r - state.l := by
        have := hrightShape hpendingR
        omega
      have hresult := cleanupRight_order (T := T)
        (List.range' 0 (128 + 1)) pivot isLess
        state.startR state.r state.offsetsR
        state.endR state.l state.v hstartR (by
          simp
          omega) hlr hrsize (by omega) hprefix hsuffix (by
            simpa only [hblock] using
              hexactR (ne_of_lt hpendingR))
      simpa only [initial, state] using hresult
    · simp only [if_neg hpendingR]
      have hdoneL : state.startL = state.endL := by omega
      have hdoneR : state.startR = state.endR := by omega
      have hlrEq : state.l = state.r := hclosed hdoneL hdoneR
      exact ⟨hprefix, by simpa only [hlrEq] using hsuffix⟩

/-- `partition_in_blocks` (`sort.rs:233-465`), implemented through the
proved phase decomposition above. -/
def partitionInBlocks (v : Array T) (pivot : T)
    (isLess : T → T → Bool) : ℕ × Array T :=
  partitionInBlocksFactored v pivot isLess

/-- The block partition returns an in-bounds split and only permutes its input. -/
theorem partitionInBlocks_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocks v pivot isLess
    result.1 ≤ v.size ∧ List.Perm result.2.toList v.toList := by
  simpa only [partitionInBlocks] using
    partitionInBlocksFactored_contract v pivot isLess

/-- The block partition places precisely the `isLess` elements before its
split and all remaining elements after it. -/
theorem partitionInBlocks_order
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocks v pivot isLess
    RangeAll result.2 0 result.1
        (fun item => isLess item pivot = true) ∧
      RangeAll result.2 result.1 result.2.size
        (fun item => isLess item pivot = false) := by
  simpa only [partitionInBlocks] using
    partitionInBlocksFactored_order v pivot isLess

/-- `partition` (`sort.rs:474-521`): partition around `v[pivotIdx]`. Returns
`((#elements < pivot, was_already_partitioned), mutated slice)`. -/
def partitionP (v0 : Array T) (pivotIdx : ℕ) (isLess : T → T → Bool) : (ℕ × Bool) × Array T := Id.run do
  let mut v := swp v0 0 pivotIdx
  let pivotVal := v[0]!
  let n := v.size
  let mut l : ℕ := 0
  let mut r : ℕ := n - 1
  for _ in [0:n] do
    if l < r && isLess (v[1+l]!) pivotVal then l := l + 1 else break
  for _ in [0:n] do
    if l < r && !isLess (v[1+(r-1)]!) pivotVal then r := r - 1 else break
  let (cnt, sub') := partitionInBlocks (v.extract (1+l) (1+r)) pivotVal isLess
  v := overwrite v (1+l) sub'
  let mid := l + cnt
  let wasP := decide (l ≥ r)
  v := swp v 0 mid
  return ((mid, wasP), v)

/-- `partition_equal` (`sort.rs:527-579`): partition `[==pivot | >pivot]` (assumes no element
`< pivot`). Returns the number equal to the pivot (incl. the pivot) and the mutated slice. -/
def partitionEqual (v0 : Array T) (pivotIdx : ℕ) (isLess : T → T → Bool) : ℕ × Array T := Id.run do
  let mut v := swp v0 0 pivotIdx
  let pivotVal := v[0]!
  let n := v.size
  let mut l : ℕ := 0
  let mut r : ℕ := n - 1
  let mut done := false
  for _ in [0:n+1] do
    if !done then
      for _ in [0:n] do
        if l < r && !isLess pivotVal (v[1+l]!) then l := l + 1 else break
      for _ in [0:n] do
        if l < r && isLess pivotVal (v[1+(r-1)]!) then r := r - 1 else break
      if l ≥ r then done := true
      else
        r := r - 1
        v := swp v (1+l) (1+r)
        l := l + 1
  return (l+1, v)

/-- Smallest power of two `≥ n` (`usize::next_power_of_two`). -/
def nextPow2 (n : ℕ) : ℕ := Id.run do
  let mut p := 1
  for _ in [0:64] do
    if p ≥ n then break
    p := p * 2
  return p

/-- `break_patterns` (`sort.rs:584-620`): pseudo-random swaps to defeat adversarial patterns.
Uses the MODIFIED (deterministic, 64-bit) Xorshift with two `gen_u32` calls per `gen_usize`
(`sort.rs:595-597`). u32 wrapping arithmetic is modelled with `UInt32`. -/
def breakPatterns (v0 : Array T) : Array T := Id.run do
  let mut v := v0
  let len := v.size
  if len ≥ 8 then
    let mut random : UInt32 := len.toUInt32
    let modulus := nextPow2 len
    let pos := len/4*2
    for i in [0:3] do
      random := random ^^^ (random <<< 13)
      random := random ^^^ (random >>> 17)
      random := random ^^^ (random <<< 5)
      let hi := random
      random := random ^^^ (random <<< 13)
      random := random ^^^ (random >>> 17)
      random := random ^^^ (random <<< 5)
      let lo := random
      let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
      let mut other : ℕ := g.toNat % modulus
      if other ≥ len then other := other - len
      v := swp v (pos - 1 + i) other
  return v

/-- `choose_pivot` (`sort.rs:625-686`): median-of-medians pivot selection. Returns
`((pivot index, likely-sorted), mutated slice)`. `sort2`/`sort3` reorder INDEX variables
(comparing `v` at those indices), not the slice; only the final `v.reverse()` mutates `v`. -/
def choosePivot (v0 : Array T) (isLess : T → T → Bool) : (ℕ × Bool) × Array T := Id.run do
  let mut v := v0
  let len := v.size
  let mut a := len/4*1
  let mut b := len/4*2
  let mut c := len/4*3
  let mut swaps : ℕ := 0
  -- sort2/sort3 as pure functions over index triples, threading the swap counter.
  let sort2 := fun (x y sw : ℕ) => if isLess (v[y]!) (v[x]!) then (y, x, sw+1) else (x, y, sw)
  let sort3 := fun (x y z sw : ℕ) =>
    let (x, y, sw) := sort2 x y sw
    let (y, z, sw) := sort2 y z sw
    let (x, y, sw) := sort2 x y sw
    (x, y, z, sw)
  if len ≥ 8 then
    if len ≥ 50 then
      let (_, ya, _, sw) := sort3 (a-1) a (a+1) swaps; a := ya; swaps := sw
      let (_, yb, _, sw) := sort3 (b-1) b (b+1) swaps; b := yb; swaps := sw
      let (_, yc, _, sw) := sort3 (c-1) c (c+1) swaps; c := yc; swaps := sw
    let (xa, yb, zc, sw) := sort3 a b c swaps
    a := xa; b := yb; c := zc; swaps := sw
  if swaps < 4*3 then
    return ((b, decide (swaps == 0)), v)
  else
    v := v.reverse
    return ((len - 1 - b, true), v)

/-- `partial_insertion_sort` (`sort.rs:129-172`). Returns `(sorted?, mutated slice)`. -/
def partialInsertionSort (v0 : Array T) (isLess : T → T → Bool) : Bool × Array T := Id.run do
  let MAX_STEPS := 5
  let SHORTEST_SHIFTING := 50
  let mut v := v0
  let len := v.size
  let mut i : ℕ := 1
  let mut result : Option Bool := none
  for _ in [0:MAX_STEPS] do
    if result.isNone then
      for _ in [0:len+1] do
        if i < len && !isLess (v[i]!) (v[i-1]!) then i := i + 1 else break
      if i == len then result := some true
      else if len < SHORTEST_SHIFTING then result := some false
      else
        v := swp v (i-1) i
        v := overwrite v 0 (shiftTail (v.extract 0 i) isLess)
        v := overwrite v i (shiftHead (v.extract i v.size) isLess)
  return (result.getD false, v)

/--
The ordinary pivot split, factored out of the recursive driver.  Making this
phase explicit avoids normalizing the entire `Id.run` program when proving its
local permutation law.
-/
def recursePartition
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (pivot : ℕ) : Array T :=
  let ((mid, wasP), v4) := partitionP v pivot isLess
  let newBalanced := decide (Nat.min mid (len - mid) ≥ len / 8)
  let pivotVal := v4[mid]!
  let left := v4.extract 0 mid
  let right := v4.extract (mid + 1) v4.size
  if left.size < right.size then
    let left' := rec left pred limit true true
    let right' := rec right (some pivotVal) limit newBalanced wasP
    left' ++ #[pivotVal] ++ right'
  else
    let right' := rec right (some pivotVal) limit true true
    let left' := rec left pred limit newBalanced wasP
    left' ++ #[pivotVal] ++ right'

/-- The predecessor-equal fast path, followed by the ordinary pivot split. -/
def recursePred
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (pivot : ℕ) : Array T :=
  match pred with
  | some p =>
    if !isLess p (v[pivot]!) then
      let (mid, v3) := partitionEqual v pivot isLess
      let head := v3.extract 0 mid
      let tail := rec (v3.extract mid v3.size) pred limit
        wasBalanced wasPartitioned
      head ++ tail
    else
      recursePartition rec v isLess pred limit len pivot
  | none =>
    recursePartition rec v isLess pred limit len pivot

/-- Optional partial-insertion fast path after pivot selection. -/
def recurseAfterPivot
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned likelySorted : Bool)
    (pivot : ℕ) : Array T :=
  if wasBalanced && wasPartitioned && likelySorted then
    let (sorted, v2) := partialInsertionSort v isLess
    if sorted then v2
    else
      recursePred rec v2 isLess pred limit len
        wasBalanced wasPartitioned pivot
  else
    recursePred rec v isLess pred limit len
      wasBalanced wasPartitioned pivot

/-- Pivot selection and the remainder of a long-array driver iteration. -/
def recurseChoose
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool) : Array T :=
  let ((pivot, likelySorted), v1) := choosePivot v isLess
  recurseAfterPivot rec v1 isLess pred limit len
    wasBalanced wasPartitioned likelySorted pivot

/-- Pattern breaking before pivot selection. -/
def recurseLong
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool) : Array T :=
  if !wasBalanced then
    recurseChoose rec (breakPatterns v) isLess pred (limit - 1) len
      wasBalanced wasPartitioned
  else
    recurseChoose rec v isLess pred limit len
      wasBalanced wasPartitioned

/-- One structurally recursive pdqsort driver step. -/
def recurseStep
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit : ℕ) (wasBalanced wasPartitioned : Bool) : Array T :=
  let len := v.size
  if len ≤ 20 then insertionSort v isLess
  else if limit == 0 then heapsort v isLess
  else
    recurseLong rec v isLess pred limit len
      wasBalanced wasPartitioned

/-- `recurse` (`sort.rs:694-777`), factored through one proof-facing driver step. -/
def recurse : ℕ → Array T → (T → T → Bool) → Option T → ℕ → Bool → Bool → Array T
  | 0, v, isLess, _, _, _, _ => heapsort v isLess
  | fuel + 1, v, isLess, pred, limit, wasBalanced, wasPartitioned =>
      recurseStep
        (fun v pred limit wasBalanced wasPartitioned =>
          recurse fuel v isLess pred limit wasBalanced wasPartitioned)
        v isLess pred limit wasBalanced wasPartitioned

/-- `quicksort` (`sort.rs:780-793`): `limit = usize::BITS − leading_zeros(len)` = the bit
length of `len` = `Nat.log2 len + 1` for `len ≥ 1`. Fuel `v.size + 1` bounds the
recursion depth (see `recurse`). -/
def quicksort (v : Array T) (isLess : T → T → Bool) : Array T :=
  if v.size == 0 then v
  else recurse (v.size + 1) v isLess none (Nat.log2 v.size + 1) true true


end Pdqsort
end Halo2.FloorPlanner
