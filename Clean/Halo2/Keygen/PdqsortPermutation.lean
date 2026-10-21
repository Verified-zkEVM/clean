import Clean.Halo2.Keygen.Pdqsort
import Mathlib.Tactic.NormNum

namespace Halo2.FloorPlanner
namespace Pdqsort

variable {T : Type} [Inhabited T]

/-! ## Permutation correctness of legacy pdqsort -/

theorem overwrite_size (a : Array T) (start : ℕ) (sub : Array T) :
    (overwrite a start sub).size = a.size := by
  simp [overwrite]
  induction List.range' 0 sub.size generalizing a with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.foldl_cons]
      rw [ih, Array.size_setIfInBounds]

private theorem fold_set_range_toList
    (a sub : Array T) (start n : ℕ)
    (hn : n ≤ sub.size) (hfit : start + n ≤ a.size) :
    (List.foldl
        (fun b i => b.setIfInBounds (start + i) sub[i]!)
        a (List.range n)).toList =
      a.toList.take start ++ sub.toList.take n ++
        a.toList.drop (start + n) := by
  induction n with
  | zero =>
      simp only [List.range_zero, List.foldl_nil, List.take_zero,
        List.append_nil, Nat.add_zero]
      exact (List.take_append_drop start a.toList).symm
  | succ n ih =>
      have hn' : n ≤ sub.size := by omega
      have hfit' : start + n ≤ a.size := by omega
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil,
        Array.toList_setIfInBounds]
      rw [ih hn' hfit', List.set_eq_take_cons_drop]
      ·
        have ha : a.toList.length = a.size := Array.length_toList
        have hs : sub.toList.length = sub.size := Array.length_toList
        have hstart : start ≤ a.toList.length := by omega
        have hnsize : n ≤ sub.toList.length := by omega
        have hidx : n < sub.toList.length := by omega
        have hA : (a.toList.take start).length = start := by
          rw [List.length_take, Nat.min_eq_left hstart]
        have hB : (sub.toList.take n).length = n := by
          rw [List.length_take, Nat.min_eq_left hnsize]
        have hAB :
            (a.toList.take start ++ sub.toList.take n).length =
              start + n := by simp [hA, hB]
        have htake :
            (a.toList.take start ++ sub.toList.take n ++
                a.toList.drop (start + n)).take (start + n) =
              a.toList.take start ++ sub.toList.take n := by
          rw [List.take_append_of_le_length (by omega)]
          apply List.take_of_length_le
          omega
        have hdrop :
            (a.toList.take start ++ sub.toList.take n ++
                a.toList.drop (start + n)).drop (start + n + 1) =
              a.toList.drop (start + (n + 1)) := by
          rw [List.drop_append]
          simp [hAB, List.drop_drop, Nat.add_assoc]
        rw [htake, hdrop,
          show sub[n]! = sub.toList[n] by simp [show n < sub.size by omega]]
        rw [← List.take_append_getElem hidx]
        simp only [List.append_assoc, List.singleton_append]
      ·
        have ha : a.toList.length = a.size := Array.length_toList
        have hs : sub.toList.length = sub.size := Array.length_toList
        simp [List.length_append]
        omega

theorem overwrite_toList (a : Array T) (start : ℕ) (sub : Array T)
    (hfit : start + sub.size ≤ a.size) :
    (overwrite a start sub).toList =
      a.toList.take start ++ sub.toList ++
        a.toList.drop (start + sub.size) := by
  simp [overwrite]
  have ht : sub.toList.take sub.size = sub.toList := by
    rw [← Array.length_toList, List.take_length]
  simpa [List.range'_eq_map_range, ht] using
    fold_set_range_toList a sub start sub.size (Nat.le_refl _) hfit

private theorem arrayToList_getElem!
    (array : Array T) (index : ℕ) :
    array.toList[index]! = array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos array.toList index (by simpa using hindex),
      getElem!_pos array index hindex]
    simp
  · rw [getElem!_neg array.toList index (by simpa using hindex),
      getElem!_neg array index hindex]

/-- `overwrite` replaces exactly the requested interval and leaves every
other entry unchanged. -/
theorem overwrite_get!
    (array sub : Array T) (start index : ℕ)
    (hfit : start + sub.size ≤ array.size) :
    (overwrite array start sub)[index]! =
      if start ≤ index ∧ index < start + sub.size then
        sub[index - start]!
      else
        array[index]! := by
  have heq := congrArg (fun values : List T => values[index]!)
    (overwrite_toList array start sub hfit)
  dsimp only at heq
  rw [arrayToList_getElem!] at heq
  rw [heq]
  by_cases hinside : start ≤ index ∧ index < start + sub.size
  · rw [if_pos hinside]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
    have htake : (array.toList.take start).length = start := by
      simp only [List.length_take, Array.length_toList]
      omega
    have hprefix :
        (array.toList.take start ++ sub.toList).length =
          start + sub.size := by simp [htake]
    rw [if_pos (by rw [hprefix]; omega), htake,
      if_neg (by omega)]
    rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some]
    rw [getElem!_pos sub (index - start) (by omega)]
    exact Array.getElem_toList (xs := sub) (by omega)
  · rw [if_neg hinside]
    by_cases hbefore : index < start
    · simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
      have htake : (array.toList.take start).length = start := by
        simp only [List.length_take, Array.length_toList]
        omega
      have hprefix :
          (array.toList.take start ++ sub.toList).length =
            start + sub.size := by simp [htake]
      rw [if_pos (by rw [hprefix]; omega),
        if_pos (by rw [htake]; omega)]
      rw [List.getElem?_eq_getElem (by
        simp only [List.length_take, Array.length_toList]
        omega), Option.getD_some, List.getElem_take]
      rw [getElem!_pos array index (by omega)]
      exact Array.getElem_toList (xs := array) (by omega)
    · have hafter : start + sub.size ≤ index := by omega
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
      have htake : (array.toList.take start).length = start := by
        simp only [List.length_take, Array.length_toList]
        omega
      have hprefix :
          (array.toList.take start ++ sub.toList).length =
            start + sub.size := by simp [htake]
      rw [if_neg (by rw [hprefix]; omega), hprefix]
      by_cases horiginal : index < array.size
      · rw [List.getElem?_eq_getElem (by
            simp only [List.length_drop, Array.length_toList]
            omega), Option.getD_some, List.getElem_drop]
        rw [getElem!_pos array index horiginal]
        simpa only [show start + sub.size + (index - (start + sub.size)) =
            index by omega] using
          Array.getElem_toList (xs := array) horiginal
      · rw [List.getElem?_eq_none (by
            simp only [List.length_drop, Array.length_toList]
            omega), Option.getD_none,
          getElem!_neg array index horiginal]

theorem overwrite_perm_of_extract
    (a : Array T) (start : ℕ) (sub : Array T)
    (hfit : start + sub.size ≤ a.size)
    (hsub : List.Perm sub.toList
      (a.extract start (start + sub.size)).toList) :
    List.Perm (overwrite a start sub).toList a.toList := by
  rw [overwrite_toList a start sub hfit]
  have hsegment :
      (a.extract start (start + sub.size)).toList =
        (a.toList.drop start).take sub.size := by
    simp [Array.toList_extract, List.extract_eq_take_drop]
  have hreplace :
      List.Perm
        (a.toList.take start ++ sub.toList ++
          a.toList.drop (start + sub.size))
        (a.toList.take start ++
          (a.extract start (start + sub.size)).toList ++
          a.toList.drop (start + sub.size)) :=
    by
      simpa only [List.append_assoc] using
        (List.Perm.refl (a.toList.take start)).append
          (hsub.append
            (List.Perm.refl (a.toList.drop (start + sub.size))))
  have horiginal :
      a.toList.take start ++
          (a.extract start (start + sub.size)).toList ++
          a.toList.drop (start + sub.size) =
        a.toList := by
    rw [hsegment, List.append_assoc,
      List.drop_take_append_drop, List.take_append_drop]
  rw [horiginal] at hreplace
  exact hreplace

private theorem list_shift_restore
    (tmp : T) : ∀ (l : List T) (i : ℕ) (_hi : i + 1 < l.length),
    (l.set (i + 1) l[i]!).set i tmp =
      ((l.set (i + 1) tmp).set i tmp).set (i + 1) l[i]! := by
  intro l i
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
      cases i with
      | zero =>
          intro hi
          cases l with
          | nil => simp at hi
          | cons b l => simp
      | succ i =>
          intro hi
          simpa only [List.getElem!_cons_succ, List.set_cons_succ] using
            congrArg (List.cons a) (ih i (by simpa using hi))

private theorem list_set_self :
    ∀ (l : List T) (i : ℕ), l.set i l[i]! = l := by
  intro l i
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a l ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.getElem!_cons_succ, List.set_cons_succ] using
            congrArg (List.cons a) (ih i)

private theorem shift_restore_eq_swp
    (a : Array T) (tmp : T) (i : ℕ) (hi : i + 1 < a.size) :
    (a.set! (i + 1) a[i]!).set! i tmp =
      swp (a.set! (i + 1) tmp) i (i + 1) := by
  apply Array.toList_inj.mp
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [show a[i]! = a.toList[i]! by simp [show i < a.size by omega]]
  have hreadi :
      (a.setIfInBounds (i + 1) tmp)[i]! = a.toList[i]! := by
    simp [Array.setIfInBounds, hi,
      show i < a.size by omega]
  have hreadsucc :
      (a.setIfInBounds (i + 1) tmp)[i + 1]! = tmp := by
    simp [Array.setIfInBounds, hi]
  rw [hreadi, hreadsucc]
  exact list_shift_restore tmp a.toList i (by simpa using hi)

private theorem shiftTail_loop_perm
    (tmp : T) (isLess : T → T → Bool) :
    ∀ (n : ℕ) (a original : Array T),
      n < a.size →
      List.Perm (a.set! n tmp).toList original.toList →
      let output : Array T := Id.run do
        pure PUnit.unit
        pure PUnit.unit
        let r ← forIn (List.range n).reverse
          (⟨n, a⟩ : MProd ℕ (Array T)) fun i (r : MProd ℕ (Array T)) =>
          if !isLess tmp (r.snd[i]!) then
            pure (.done ⟨r.fst, r.snd⟩)
          else do
            pure PUnit.unit
            pure PUnit.unit
            pure (.yield ⟨i, r.snd.set! (i + 1) (r.snd[i]!)⟩)
        pure (r.snd.set! r.fst tmp)
      List.Perm output.toList original.toList := by
  intro n
  induction n with
  | zero =>
      intro a original hn hperm
      simpa using hperm
  | succ n ih =>
      intro a original hn hperm
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append]
      simp only [List.forIn_cons]
      split
      · simpa using hperm
      ·
        apply ih (a.set! (n + 1) a[n]!) original
        · simpa [Array.set!] using Nat.lt_trans (Nat.lt_succ_self n) hn
        · rw [shift_restore_eq_swp a tmp n (by simpa using hn)]
          have hin : n < (a.set! (n + 1) tmp).size := by
            simpa [Array.set!] using Nat.lt_trans (Nat.lt_succ_self n) hn
          have his : n + 1 < (a.set! (n + 1) tmp).size := by
            simpa [Array.set!] using hn
          exact (swp_perm (a.set! (n + 1) tmp) n (n + 1)
            hin his).trans hperm

theorem shiftTail_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (shiftTail v isLess).toList v.toList := by
  simp only [shiftTail]
  split
  · simp
  split
  · simp
  ·
    have hnSucc : v.size - 2 + 1 < v.size := by omega
    have hnBase : v.size - 2 < v.size := by omega
    have hn : v.size - 2 <
        (v.set! (v.size - 1) v[v.size - 2]!).size := by
      simpa [Array.set!] using Nat.lt_trans
        (Nat.lt_succ_self (v.size - 2)) hnSucc
    have hinit :
        List.Perm
          ((v.set! (v.size - 1) v[v.size - 2]!).set!
            (v.size - 2) v[v.size - 1]!).toList
          v.toList := by
      rw [show v.size - 1 = v.size - 2 + 1 by omega]
      rw [shift_restore_eq_swp v v[v.size - 2 + 1]!
        (v.size - 2) hnSucc]
      have hp := swp_perm (v.set! (v.size - 2 + 1)
          v[v.size - 2 + 1]!) (v.size - 2) (v.size - 2 + 1)
        (by simpa [Array.set!] using hnBase)
        (by simpa [Array.set!] using hnSucc)
      have hself :
          (v.set! (v.size - 2 + 1) v[v.size - 2 + 1]!).toList =
            v.toList := by
        simp only [Array.set!, Array.toList_setIfInBounds]
        rw [show v[v.size - 2 + 1]! = v.toList[v.size - 2 + 1]! by
          simp [hnSucc]]
        exact list_set_self v.toList (v.size - 2 + 1)
      exact hp.trans (hself ▸ List.Perm.refl v.toList)
    have hloop := shiftTail_loop_perm v[v.size - 1]! isLess
        (v.size - 2) (v.set! (v.size - 1) v[v.size - 2]!) v
        hn hinit
    exact hloop

private theorem list_shiftHead_restore
    (tmp : T) : ∀ (l : List T) (i : ℕ) (_hi : i + 1 < l.length),
    (l.set i l[i + 1]!).set (i + 1) tmp =
      ((l.set i tmp).set i l[i + 1]!).set (i + 1) tmp := by
  intro l i
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
      cases i with
      | zero =>
          intro hi
          cases l with
          | nil => simp at hi
          | cons b l => simp
      | succ i =>
          intro hi
          simpa only [List.getElem!_cons_succ, List.set_cons_succ] using
            congrArg (List.cons a) (ih i (by simpa using hi))

private theorem shiftHead_restore_eq_swp
    (a : Array T) (tmp : T) (i : ℕ) (hi : i + 1 < a.size) :
    (a.set! i a[i + 1]!).set! (i + 1) tmp =
      swp (a.set! i tmp) i (i + 1) := by
  apply Array.toList_inj.mp
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [show a[i + 1]! = a.toList[i + 1]! by simp [hi]]
  have hreadi :
      (a.setIfInBounds i tmp)[i]! = tmp := by
    simp [Array.setIfInBounds, show i < a.size by omega]
  have hreadsucc :
      (a.setIfInBounds i tmp)[i + 1]! = a.toList[i + 1]! := by
    have hibase : i < a.size := by omega
    rw [show a.setIfInBounds i tmp = a.set i tmp hibase by
      simp [Array.setIfInBounds, hibase]]
    simp [hi]
  rw [hreadi, hreadsucc]
  exact list_shiftHead_restore tmp a.toList i (by simpa using hi)

private theorem shiftHead_loop_perm
    (tmp : T) (isLess : T → T → Bool) :
    ∀ (start count : ℕ) (a original : Array T),
      0 < start →
      start + count ≤ a.size →
      List.Perm (a.set! (start - 1) tmp).toList original.toList →
      let output : Array T := Id.run do
        pure PUnit.unit
        pure PUnit.unit
        let r ← forIn (List.range' start count)
          (⟨start - 1, a⟩ : MProd ℕ (Array T))
          fun i (r : MProd ℕ (Array T)) =>
            if !isLess (r.snd[i]!) tmp then
              pure (.done ⟨r.fst, r.snd⟩)
            else do
              pure PUnit.unit
              pure PUnit.unit
              pure (.yield ⟨i, r.snd.set! (i - 1) (r.snd[i]!)⟩)
        pure (r.snd.set! r.fst tmp)
      List.Perm output.toList original.toList := by
  intro start count
  induction count generalizing start with
  | zero =>
      intro a original hstart hfit hperm
      simpa using hperm
  | succ count ih =>
      intro a original hstart hfit hperm
      rw [List.range'_succ]
      simp only [List.forIn_cons]
      split
      · simpa using hperm
      ·
        apply ih (start + 1)
          (a.set! (start - 1) a[start]!) original
        · omega
        · simpa [Array.set!] using (show start + 1 + count ≤ a.size by
            omega)
        ·
          simp only [Nat.add_sub_cancel]
          have hslt : start < a.size := by omega
          have hprev : start - 1 + 1 = start := by omega
          have hstep :
              (a.set! (start - 1) a[start]!).set! start tmp =
                swp (a.set! (start - 1) tmp) (start - 1) start := by
            simpa only [hprev] using
              shiftHead_restore_eq_swp a tmp (start - 1)
                (hprev ▸ hslt)
          rw [hstep]
          have hleft :
              start - 1 < (a.set! (start - 1) tmp).size := by
            simpa [Array.set!] using (show start - 1 < a.size by omega)
          have hright :
              start < (a.set! (start - 1) tmp).size := by
            simpa [Array.set!] using (show start < a.size by omega)
          exact (swp_perm (a.set! (start - 1) tmp)
            (start - 1) start hleft hright).trans hperm

theorem shiftHead_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (shiftHead v isLess).toList v.toList := by
  simp only [shiftHead]
  split
  · simp
  split
  · simp
  ·
    have hone : 1 < v.size := by omega
    have hfit : 2 + (v.size - 2) ≤ v.size := by omega
    have hinit :
        List.Perm ((v.set! 0 v[1]!).set! 1 v[0]!).toList
          v.toList := by
      rw [shiftHead_restore_eq_swp v v[0]! 0 (by simpa using hone)]
      have hp := swp_perm (v.set! 0 v[0]!) 0 1
        (by simpa [Array.set!] using (show 0 < v.size by omega))
        (by simpa [Array.set!] using hone)
      have hself : (v.set! 0 v[0]!).toList = v.toList := by
        simp only [Array.set!, Array.toList_setIfInBounds]
        rw [show v[0]! = v.toList[0]! by simp [show 0 < v.size by omega]]
        exact list_set_self v.toList 0
      exact hp.trans (hself ▸ List.Perm.refl v.toList)
    have hloop := shiftHead_loop_perm v[0]! isLess
      2 (v.size - 2) (v.set! 0 v[1]!) v
      (by omega) (by simpa [Array.set!] using hfit) hinit
    simpa using hloop

omit [Inhabited T] in
private theorem array_size_eq_of_perm {left right : Array T}
    (hperm : List.Perm left.toList right.toList) :
    left.size = right.size := by
  simpa using hperm.length_eq

private theorem insertion_step_perm
    (v : Array T) (isLess : T → T → Bool) (i : ℕ)
    (hi : i < v.size) :
    List.Perm
      (overwrite v 0
        (shiftTail (v.extract 0 (i + 1)) isLess)).toList
      v.toList := by
  let pre := v.extract 0 (i + 1)
  let shifted := shiftTail pre isLess
  have hshift : List.Perm shifted.toList pre.toList :=
    shiftTail_perm pre isLess
  have hsize : shifted.size = pre.size :=
    array_size_eq_of_perm hshift
  have hprefix : pre.size = i + 1 := by
    have hbound : i + 1 ≤ v.size := Nat.succ_le_iff.mpr hi
    simp [pre, Array.size_extract, Nat.min_eq_left hbound]
  apply overwrite_perm_of_extract v 0 shifted
  · simp [hsize, hprefix]
    omega
  · simpa [shifted, pre, hsize, hprefix] using hshift

private theorem insertion_fold_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (indices.foldl (fun a i =>
          overwrite a 0
            (shiftTail (a.extract 0 (i + 1)) isLess)) current).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      have hi : i < current.size := by
        rw [hsize]
        exact hindices i (by simp)
      have hstep := insertion_step_perm current isLess i hi
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hindices j (by simp [hj])
      · exact hstep.trans hperm

theorem insertionSort_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (insertionSort v isLess).toList v.toList := by
  simp [insertionSort]
  apply insertion_fold_perm isLess (List.range' 1 (v.size - 1)) v v
  · intro i hi
    simp only [List.mem_range'] at hi
    omega
  · exact List.Perm.refl _

private theorem insertion_range_sorted
    (key : T → ℕ) :
    ∀ (count start : ℕ) (current : Array T),
      start + count ≤ current.size →
      KeySorted key (current.toList.take start) →
      KeySorted key
        (((List.range' start count).foldl (fun array index =>
          overwrite array 0
            (shiftTail (array.extract 0 (index + 1)) (lessBy key)))
          current).toList.take (start + count)) := by
  intro count
  induction count with
  | zero =>
      intro start current _ hsorted
      simpa using hsorted
  | succ count inductionHypothesis =>
      intro start current hfit hsorted
      rw [List.range'_succ, List.foldl_cons]
      let prefixArray := current.extract 0 (start + 1)
      let shifted := shiftTail prefixArray (lessBy key)
      let next := overwrite current 0 shifted
      have hprefixSize : prefixArray.size = start + 1 := by
        simp [prefixArray]
        omega
      have hprefixSorted : KeySorted key
          (prefixArray.toList.take (prefixArray.size - 1)) := by
        simp only [prefixArray, Array.toList_extract,
          List.extract_eq_take_drop, List.drop_zero, hprefixSize]
        rw [show start + 1 - 1 = start by omega, List.take_take,
          Nat.min_eq_left (by omega)]
        exact hsorted
      have hshiftedSorted : KeySorted key shifted.toList :=
        shiftTail_sorted prefixArray key hprefixSorted
      have hshiftedSize : shifted.size = prefixArray.size := by
        have hperm := shiftTail_perm prefixArray (lessBy key)
        simpa using hperm.length_eq
      have hnextSize : next.size = current.size := by
        simp [next, overwrite_size]
      have hnextPrefix :
          KeySorted key (next.toList.take (start + 1)) := by
        have hoverwrite := overwrite_toList current 0 shifted (by
          simp [hshiftedSize, hprefixSize]
          omega)
        simp only [List.take_zero, List.nil_append, Nat.zero_add] at hoverwrite
        rw [hoverwrite]
        rw [List.take_append_of_le_length]
        · have hlength : shifted.toList.length = start + 1 := by
            simp [hshiftedSize, hprefixSize]
          rw [← hlength, List.take_length]
          exact hshiftedSorted
        · simp [hshiftedSize, hprefixSize]
      have hresult := inductionHypothesis (start + 1) next
        (by simp [hnextSize]; omega) hnextPrefix
      unfold next shifted prefixArray at hresult
      rw [show start + (count + 1) = start + 1 + count by omega]
      exact hresult

/-- The legacy insertion-sort implementation orders its output by the supplied key. -/
theorem insertionSort_sorted (array : Array T) (key : T → ℕ) :
    KeySorted key (insertionSort array (lessBy key)).toList := by
  by_cases hempty : array.size = 0
  · have hnil : array.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hempty
    have hresult : insertionSort array (lessBy key) = array := by
      simp [insertionSort, hempty]
    rw [hresult, hnil]
    exact KeySorted.nil key
  · have hprefix : KeySorted key (array.toList.take 1) := by
      rw [KeySorted, List.sortedLE_iff_pairwise,
        List.pairwise_map, List.pairwise_iff_get]
      intro left right horder
      have hleft := left.isLt
      have hright := right.isLt
      simp only [List.length_take] at hleft hright
      omega
    have hsorted := insertion_range_sorted key (array.size - 1) 1 array
      (by omega) hprefix
    rw [show 1 + (array.size - 1) = array.size by omega] at hsorted
    have hlength :
        (insertionSort array (lessBy key)).toList.length = array.size := by
      have hperm := insertionSort_perm array (lessBy key)
      simpa using hperm.length_eq
    have hfold :
        (List.range' 1 (array.size - 1)).foldl (fun current index =>
          overwrite current 0
            (shiftTail (current.extract 0 (index + 1)) (lessBy key))) array =
          insertionSort array (lessBy key) := by
      simp [insertionSort]
    rw [hfold, ← hlength, List.take_length] at hsorted
    exact hsorted

private theorem siftDown_loop_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (node : ℕ) (a original : Array T),
      node < a.size →
      List.Perm a.toList original.toList →
      let result : MProd ℕ (Array T) := Id.run <|
        forIn indices (⟨node, a⟩ : MProd ℕ (Array T))
          fun _ (r : MProd ℕ (Array T)) =>
            let left := 2 * r.fst + 1
            let right := 2 * r.fst + 2
            let greater :=
              if right < r.snd.size &&
                  isLess (r.snd[left]!) (r.snd[right]!) then
                right
              else left
            if greater ≥ r.snd.size ||
                !isLess (r.snd[r.fst]!) (r.snd[greater]!) then
              pure (.done ⟨r.fst, r.snd⟩)
            else do
              pure PUnit.unit
              pure PUnit.unit
              pure (.yield ⟨greater,
                swp r.snd r.fst greater⟩)
      result.fst < result.snd.size ∧
        List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro node a original hnode hperm
      exact ⟨hnode, hperm⟩
  | cons index indices ih =>
      intro node a original hnode hperm
      simp only [List.forIn_cons]
      split
      · split
        · exact ⟨hnode, hperm⟩
        ·
          apply ih
          · simp only [Bool.and_eq_true, Bool.or_eq_true,
              decide_eq_true_eq] at *
            have hright : 2 * node + 2 < a.size := by omega
            simpa [swp, Array.set!] using hright
          ·
            have hright : 2 * node + 2 < a.size := by
              simp only [Bool.and_eq_true, Bool.or_eq_true,
                decide_eq_true_eq] at *
              omega
            exact (swp_perm a node (2 * node + 2)
              hnode hright).trans hperm
      ·
        split
        · exact ⟨hnode, hperm⟩
        ·
          apply ih
          ·
            simp only [Bool.or_eq_true, decide_eq_true_eq] at *
            have hleft : 2 * node + 1 < a.size := by omega
            simpa [swp, Array.set!] using hleft
          ·
            have hleft : 2 * node + 1 < a.size := by
              simp only [Bool.or_eq_true, decide_eq_true_eq] at *
              omega
            exact (swp_perm a node (2 * node + 1)
              hnode hleft).trans hperm

theorem siftDown_perm (v : Array T) (isLess : T → T → Bool)
    (node : ℕ) (hnode : node < v.size) :
    List.Perm (siftDown v isLess node).toList v.toList := by
  simp [siftDown]
  have hloop := siftDown_loop_perm isLess
    (List.range' 0 (v.size + 1)) node v v
    hnode (List.Perm.refl _)
  simpa using hloop.2

private theorem siftDown_fold_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (indices.foldl (fun a i => siftDown a isLess i)
          current).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      have hi : i < current.size := by
        rw [hsize]
        exact hindices i (by simp)
      have hstep := siftDown_perm current isLess i hi
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hindices j (by simp [hj])
      · exact hstep.trans hperm

private theorem heapsort_extract_step_perm
    (v : Array T) (isLess : T → T → Bool) (i : ℕ)
    (hi : i < v.size) (hone : 1 ≤ i) :
    List.Perm
      (overwrite (swp v 0 i) 0
        (siftDown ((swp v 0 i).extract 0 i) isLess 0)).toList
      v.toList := by
  have hzero : 0 < v.size := by omega
  have hswap : List.Perm (swp v 0 i).toList v.toList :=
    swp_perm v 0 i hzero hi
  let swapped := swp v 0 i
  let pre := swapped.extract 0 i
  let sifted := siftDown pre isLess 0
  have hswappedSize : swapped.size = v.size :=
    array_size_eq_of_perm hswap
  have hpreSize : pre.size = i := by
    simp [pre, swapped, swp, Array.set!, hi]
    omega
  have hsift : List.Perm sifted.toList pre.toList := by
    apply siftDown_perm pre isLess 0
    simp [hpreSize]
    omega
  have hsiftSize : sifted.size = pre.size :=
    array_size_eq_of_perm hsift
  have hover : List.Perm (overwrite swapped 0 sifted).toList
      swapped.toList := by
    apply overwrite_perm_of_extract swapped 0 sifted
    · simp [hsiftSize, hpreSize, hswappedSize]
      omega
    · simpa [sifted, pre, hsiftSize, hpreSize] using hsift
  exact hover.trans hswap

private theorem heapsort_extract_fold_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (indices.foldl (fun a i =>
          if i ≥ 1 then
            overwrite (swp a 0 i) 0
              (siftDown ((swp a 0 i).extract 0 i) isLess 0)
          else a) current).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      simp only [List.foldl_cons]
      split
      ·
        have hi : i < current.size := by
          rw [hsize]
          exact hindices i (by simp)
        have hstep := heapsort_extract_step_perm current isLess i hi
          (by omega)
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hstep.trans hperm
      ·
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hperm

private theorem heapsort_extract_forIn_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (Id.run (forIn indices current fun i a =>
          if i ≥ 1 then
            pure (.yield (overwrite (swp a 0 i) 0
              (siftDown ((swp a 0 i).extract 0 i) isLess 0)))
          else pure (.yield a))).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      simp only [List.forIn_cons]
      split
      ·
        have hi : i < current.size := by
          rw [hsize]
          exact hindices i (by simp)
        have hstep := heapsort_extract_step_perm current isLess i hi
          (by omega)
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hstep.trans hperm
      ·
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hperm

theorem heapsort_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (heapsort v isLess).toList v.toList := by
  simp [heapsort]
  let heapified :=
    List.foldr (fun i a => siftDown a isLess i)
      v (List.range (v.size / 2))
  have hheap : List.Perm heapified.toList v.toList := by
    have hfold := siftDown_fold_perm isLess
      (List.range (v.size / 2)).reverse v v
      (by
        intro i hi
        simp only [List.mem_reverse, List.mem_range] at hi
        omega)
      (List.Perm.refl _)
    simpa [heapified] using hfold
  have hextract := heapsort_extract_forIn_perm isLess
    (List.range v.size).reverse heapified v
    (by
      intro i hi
      simpa only [List.mem_reverse, List.mem_range] using hi)
    hheap
  simpa [heapified] using hextract

private theorem nextPow2_loop_bounds :
    ∀ (indices : List ℕ) (n p : ℕ),
      0 < p →
      p ≤ 2 * n →
      let result : ℕ := Id.run <|
        forIn indices p fun _ p =>
          if p ≥ n then pure (.done p)
          else pure (.yield (p * 2))
      0 < result ∧ result ≤ 2 * n := by
  intro indices
  induction indices with
  | nil =>
      intro n p hp hbound
      exact ⟨hp, hbound⟩
  | cons i indices ih =>
      intro n p hp hbound
      simp only [List.forIn_cons]
      split
      · exact ⟨hp, hbound⟩
      ·
        apply ih
        · omega
        · omega

private theorem nextPow2_bounds (n : ℕ) (hn : 0 < n) :
    0 < nextPow2 n ∧ nextPow2 n ≤ 2 * n := by
  have hloop := nextPow2_loop_bounds
    (List.range' 0 64) n 1 (by omega) (by omega)
  simpa [nextPow2] using hloop

private theorem adjusted_mod_lt (x len : ℕ) (hlen : 0 < len) :
    let raw := x % nextPow2 len
    (if raw ≥ len then raw - len else raw) < len := by
  have hb := nextPow2_bounds len hlen
  have hmod : x % nextPow2 len < nextPow2 len :=
    Nat.mod_lt x hb.1
  dsimp only
  split <;> omega

/-
private theorem breakPatterns_loop_perm :
    ∀ (indices : List ℕ) (len : ℕ)
      (random : UInt32) (a original : Array T),
      8 ≤ len →
      a.size = len →
      (∀ i ∈ indices, i < 3) →
      List.Perm a.toList original.toList →
      let result : MProd UInt32 (Array T) := Id.run <|
        forIn indices (⟨random, a⟩ : MProd UInt32 (Array T))
          fun i (r : MProd UInt32 (Array T)) =>
            let random₁ := r.fst ^^^ (r.fst <<< 13)
            let random₂ := random₁ ^^^ (random₁ >>> 17)
            let random₃ := random₂ ^^^ (random₂ <<< 5)
            let hi := random₃
            let random₄ := random₃ ^^^ (random₃ <<< 13)
            let random₅ := random₄ ^^^ (random₄ >>> 17)
            let random₆ := random₅ ^^^ (random₅ <<< 5)
            let lo := random₆
            let g : UInt64 :=
              (hi.toUInt64 <<< 32) ||| lo.toUInt64
            let raw : ℕ := g.toNat % nextPow2 len
            let other := if raw ≥ len then raw - len else raw
            pure (.yield ⟨random₆,
              swp r.snd (len / 4 * 2 - 1 + i) other⟩)
      List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro len random a original hlen hsize hindices hperm
      simpa using hperm
  | cons i indices ih =>
      intro len random a original hlen hsize hindices hperm
      simp only [List.forIn_cons]
      apply ih
      · exact hlen
      ·
        have hpermStep := swp_perm a (len / 4 * 2 - 1 + i)
          (if
              (((((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                  (((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                ((((random ^^^ (random <<< 13)) ^^^
                      ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                    (((random ^^^ (random <<< 13)) ^^^
                      ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17) ^^^
              (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                    (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) <<< 5)).toUInt64.toNat %
                nextPow2 len ≥ len then
            (((((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                  (((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)).toUInt64 <<< 32 |||
              (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                    (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) ^^^
                  (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                        (((((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                              (((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                            ((((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                                (((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) <<< 5)).toUInt64).toNat %
                nextPow2 len - len
          else
            (((((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                  (((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)).toUInt64 <<< 32 |||
              (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                    (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) ^^^
                  (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                        (((((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                              (((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                            ((((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                                (((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) <<< 5)).toUInt64).toNat %
              nextPow2 len)
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            apply adjusted_mod_lt
            omega)
        exact array_size_eq_of_perm hpermStep
      · intro j hj
        exact hindices j (by simp [hj])
      ·
        apply (swp_perm a (len / 4 * 2 - 1 + i)
          _ (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega) (by
            rw [hsize]
            apply adjusted_mod_lt
            omega)).trans hperm
-/

private def xorshift32 (random : UInt32) : UInt32 :=
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  random ^^^ (random <<< 5)

private def breakNextRandom (random : UInt32) : UInt32 :=
  xorshift32 (xorshift32 random)

private def breakOther (random : UInt32) (len : ℕ) : ℕ :=
  let hi := xorshift32 random
  let lo := xorshift32 hi
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  let raw := g.toNat % nextPow2 len
  if raw ≥ len then raw - len else raw

private def breakWord (random : UInt32) : ℕ :=
  let hi := xorshift32 random
  let lo := xorshift32 hi
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  g.toNat

private theorem breakOther_lt (random : UInt32) (len : ℕ)
    (hlen : 0 < len) :
    breakOther random len < len := by
  unfold breakOther
  apply adjusted_mod_lt
  exact hlen

private theorem breakPatterns_loop_perm_clean :
    ∀ (indices : List ℕ) (len : ℕ)
      (random : UInt32) (a original : Array T),
      8 ≤ len →
      a.size = len →
      (∀ i ∈ indices, i < 3) →
      List.Perm a.toList original.toList →
      let result : MProd UInt32 (Array T) := Id.run <|
        forIn indices (⟨random, a⟩ : MProd UInt32 (Array T))
          fun i (r : MProd UInt32 (Array T)) =>
            pure (.yield ⟨breakNextRandom r.fst,
              swp r.snd (len / 4 * 2 - 1 + i)
                (breakOther r.fst len)⟩)
      List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro len random a original hlen hsize hindices hperm
      simpa using hperm
  | cons i indices ih =>
      intro len random a original hlen hsize hindices hperm
      simp only [List.forIn_cons]
      apply ih
      · exact hlen
      ·
        have hstep := swp_perm a (len / 4 * 2 - 1 + i)
          (breakOther random len)
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakOther_lt random len (by omega))
        exact (array_size_eq_of_perm hstep).trans hsize
      · intro j hj
        exact hindices j (by simp [hj])
      ·
        exact (swp_perm a (len / 4 * 2 - 1 + i)
          (breakOther random len)
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakOther_lt random len (by omega))).trans hperm

private def breakChoice (random : UInt32) (len : ℕ) :
    MProd UInt32 ℕ :=
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let hi := random
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let lo := random
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  let raw := g.toNat % nextPow2 len
  ⟨random, if raw ≥ len then raw - len else raw⟩

private theorem breakChoice_other_lt (random : UInt32) (len : ℕ)
    (hlen : 0 < len) :
    (breakChoice random len).snd < len := by
  unfold breakChoice
  apply adjusted_mod_lt
  exact hlen

private theorem breakPatterns_loop_perm_choice :
    ∀ (indices : List ℕ) (len : ℕ)
      (random : UInt32) (a original : Array T),
      8 ≤ len →
      a.size = len →
      (∀ i ∈ indices, i < 3) →
      List.Perm a.toList original.toList →
      let result : MProd UInt32 (Array T) := Id.run <|
        forIn indices (⟨random, a⟩ : MProd UInt32 (Array T))
          fun i (r : MProd UInt32 (Array T)) =>
            let choice := breakChoice r.fst len
            pure (.yield ⟨choice.fst,
              swp r.snd (len / 4 * 2 - 1 + i) choice.snd⟩)
      List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro len random a original hlen hsize hindices hperm
      simpa using hperm
  | cons i indices ih =>
      intro len random a original hlen hsize hindices hperm
      simp only [List.forIn_cons]
      apply ih
      · exact hlen
      ·
        have hstep := swp_perm a (len / 4 * 2 - 1 + i)
          (breakChoice random len).snd
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakChoice_other_lt random len (by omega))
        exact (array_size_eq_of_perm hstep).trans hsize
      · intro j hj
        exact hindices j (by simp [hj])
      ·
        exact (swp_perm a (len / 4 * 2 - 1 + i)
          (breakChoice random len).snd
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakChoice_other_lt random len (by omega))).trans hperm

omit [Inhabited T] in
private theorem state_forIn_perm
    (indices : List ℕ)
    (step : ℕ → MProd UInt32 (Array T) →
      MProd UInt32 (Array T))
    (initial : MProd UInt32 (Array T)) (original : Array T)
    (hstep : ∀ i ∈ indices, ∀ r,
      List.Perm r.snd.toList original.toList →
      List.Perm (step i r).snd.toList original.toList)
    (hperm : List.Perm initial.snd.toList original.toList) :
    let result : MProd UInt32 (Array T) := Id.run <|
      forIn indices initial fun i r =>
        pure (.yield (step i r))
    List.Perm result.snd.toList original.toList := by
  induction indices generalizing initial with
  | nil =>
      simpa using hperm
  | cons i indices ih =>
      simp only [List.forIn_cons]
      apply ih
      · intro j hj r
        exact hstep j (by simp [hj]) r
      · exact hstep i (by simp) initial hperm

omit [Inhabited T] in
private theorem state_forIn_body_perm
    (indices : List ℕ)
    (body : ℕ → MProd UInt32 (Array T) →
      Id (ForInStep (MProd UInt32 (Array T))))
    (initial : MProd UInt32 (Array T)) (original : Array T)
    (hbody : ∀ i ∈ indices, ∀ r,
      List.Perm r.snd.toList original.toList →
      match body i r with
      | .done s => List.Perm s.snd.toList original.toList
      | .yield s => List.Perm s.snd.toList original.toList)
    (hperm : List.Perm initial.snd.toList original.toList) :
    let result : MProd UInt32 (Array T) := Id.run <|
      forIn indices initial body
    List.Perm result.snd.toList original.toList := by
  induction indices generalizing initial with
  | nil =>
      simpa using hperm
  | cons i indices ih =>
      rw [List.forIn_cons]
      generalize hb : body i initial = b
      cases b with
      | done s =>
          have hs := hbody i (by simp) initial hperm
          rw [hb] at hs
          exact hs
      | yield s =>
          apply ih
          · intro j hj r hr
            exact hbody j (by simp [hj]) r hr
          ·
            have hs := hbody i (by simp) initial hperm
            rw [hb] at hs
            exact hs

omit [Inhabited T] in
private theorem state_forIn_body_result_perm
    (indices : List ℕ)
    (body : ℕ → MProd UInt32 (Array T) →
      Id (ForInStep (MProd UInt32 (Array T))))
    (initial : MProd UInt32 (Array T)) (original : Array T)
    (hbody : ∀ i ∈ indices, ∀ r,
      List.Perm r.snd.toList original.toList →
      match body i r with
      | .done s => List.Perm s.snd.toList original.toList
      | .yield s => List.Perm s.snd.toList original.toList)
    (hperm : List.Perm initial.snd.toList original.toList) :
    List.Perm
      (Id.run do
        let r ← forIn indices initial body
        pure PUnit.unit
        pure r.snd).toList
      original.toList := by
  simpa using state_forIn_body_perm indices body initial original
    hbody hperm

private def breakPatternsStep (len modulus pos : ℕ) (i : ℕ)
    (r : MProd UInt32 (Array T)) : MProd UInt32 (Array T) :=
  let random := r.fst ^^^ (r.fst <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let hi := random
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let lo := random
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  let raw := g.toNat % modulus
  let other := if raw ≥ len then raw - len else raw
  ⟨random, swp r.snd (pos - 1 + i) other⟩

private theorem breakPatternsStep_perm (v : Array T) (i : ℕ)
    (hi : i < 3) (r : MProd UInt32 (Array T))
    (hlen : 8 ≤ v.size)
    (hr : List.Perm r.snd.toList v.toList) :
    List.Perm
      (breakPatternsStep v.size (nextPow2 v.size)
        (v.size / 4 * 2) i r).snd.toList v.toList := by
  have hrsize : r.snd.size = v.size :=
    array_size_eq_of_perm hr
  unfold breakPatternsStep
  exact (swp_perm r.snd (v.size / 4 * 2 - 1 + i) _
    (by rw [hrsize]; omega)
    (by rw [hrsize]; apply adjusted_mod_lt; omega)).trans hr

theorem breakPatterns_perm (v : Array T) :
    List.Perm (breakPatterns v).toList v.toList := by
  simp only [breakPatterns]
  split
  ·
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    let body : ℕ → MProd UInt32 (Array T) →
        Id (ForInStep (MProd UInt32 (Array T))) :=
      fun i r => do
        let mut a := r.snd
        let mut random := r.fst
        random := random ^^^ (random <<< 13)
        random := random ^^^ (random >>> 17)
        random := random ^^^ (random <<< 5)
        let hi := random
        random := random ^^^ (random <<< 13)
        random := random ^^^ (random >>> 17)
        random := random ^^^ (random <<< 5)
        let lo := random
        let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
        let mut other : ℕ := g.toNat % nextPow2 v.size
        if other ≥ v.size then other := other - v.size
        a := swp a (v.size / 4 * 2 - 1 + i) other
        pure PUnit.unit
        pure (.yield ⟨random, a⟩)
    have hbody :
        ∀ i ∈ List.range' 0 3, ∀ r,
          List.Perm r.snd.toList v.toList →
          match body i r with
          | .done s => List.Perm s.snd.toList v.toList
          | .yield s => List.Perm s.snd.toList v.toList := by
      intro i hi r hr
      simp only [List.mem_range'] at hi
      have hrsize : r.snd.size = v.size :=
        array_size_eq_of_perm hr
      simp only [body]
      split_ifs with hother
      ·
        exact (swp_perm r.snd (v.size / 4 * 2 - 1 + i) _
          (by rw [hrsize]; omega)
          (by
            rw [hrsize]
            simpa only [breakWord, xorshift32, if_pos hother] using
              (adjusted_mod_lt (breakWord r.fst) v.size
                (by omega)))).trans hr
      ·
        exact (swp_perm r.snd (v.size / 4 * 2 - 1 + i) _
          (by rw [hrsize]; omega)
          (by
            rw [hrsize]
            simpa only [breakWord, xorshift32, if_neg hother] using
              (adjusted_mod_lt (breakWord r.fst) v.size
                (by omega)))).trans hr
    have hmain := state_forIn_body_result_perm
      (List.range' 0 3) body ⟨v.size.toUInt32, v⟩ v
      hbody (List.Perm.refl _)
    simpa only [body] using hmain
  · simp

private theorem partialInsertionMutation_perm
    (v0 : Array T) (isLess : T → T → Bool) (i : ℕ)
    (hi0 : 0 < i) (hi : i < v0.size) :
    let v := swp v0 (i - 1) i
    let v := overwrite v 0 (shiftTail (v.extract 0 i) isLess)
    let v := overwrite v i (shiftHead (v.extract i v.size) isLess)
    List.Perm v.toList v0.toList := by
  let v1 := swp v0 (i - 1) i
  have hp1 : List.Perm v1.toList v0.toList := by
    apply swp_perm
    · omega
    · exact hi
  have hv1size : v1.size = v0.size :=
    array_size_eq_of_perm hp1
  let sub1 := shiftTail (v1.extract 0 i) isLess
  have hsub1 :
      List.Perm sub1.toList (v1.extract 0 i).toList :=
    shiftTail_perm _ isLess
  have hsub1size : sub1.size = i := by
    have hs := array_size_eq_of_perm hsub1
    simp only [Array.size_extract] at hs
    omega
  have hp2 :
      List.Perm (overwrite v1 0 sub1).toList v1.toList := by
    apply overwrite_perm_of_extract
    · simp [hsub1size]
      omega
    · simpa [hsub1size] using hsub1
  let v2 := overwrite v1 0 sub1
  have hv2size : v2.size = v1.size :=
    array_size_eq_of_perm hp2
  have hi2 : i < v2.size := by omega
  let sub2 := shiftHead (v2.extract i v2.size) isLess
  have hsub2 :
      List.Perm sub2.toList (v2.extract i v2.size).toList :=
    shiftHead_perm _ isLess
  have hsub2size : sub2.size = v2.size - i := by
    have hs := array_size_eq_of_perm hsub2
    simp only [Array.size_extract] at hs
    omega
  have hp3 :
      List.Perm (overwrite v2 i sub2).toList v2.toList := by
    apply overwrite_perm_of_extract
    · omega
    ·
      have hend : i + sub2.size = v2.size := by omega
      simpa [hend] using hsub2
  exact hp3.trans (hp2.trans hp1)

private theorem list_forIn_invariant
    {S : Type} (indices : List ℕ)
    (body : ℕ → S → Id (ForInStep S))
    (Inv : S → Prop) (initial : S)
    (hbody : ∀ i ∈ indices, ∀ s s', Inv s →
      ((body i s).run = .done s' ∨
        (body i s).run = .yield s') → Inv s')
    (hinit : Inv initial) :
    Inv (Id.run <| forIn indices initial body) := by
  induction indices generalizing initial with
  | nil =>
      simpa using hinit
  | cons i indices ih =>
      rw [List.forIn_cons]
      generalize hb : body i initial = b
      cases b with
      | done s =>
          exact hbody i (by simp) initial s hinit
            (Or.inl (by simpa using congrArg Id.run hb))
      | yield s =>
          apply ih
          · intro j hj t t' ht hstep
            exact hbody j (by simp [hj]) t t' ht hstep
          ·
            exact hbody i (by simp) initial s hinit
              (Or.inr (by simpa using congrArg Id.run hb))

private theorem bounded_scan
    (indices : List ℕ) (len i0 : ℕ)
    (pred : ℕ → Bool)
    (hpred : ∀ i, pred i = true → i < len)
    (hi0 : 0 < i0) (hile : i0 ≤ len) :
    let result : ℕ := Id.run <|
      forIn indices i0 fun _ i =>
        if pred i then do
          pure PUnit.unit
          pure (.yield (i + 1))
        else pure (.done i)
    0 < result ∧ result ≤ len := by
  induction indices generalizing i0 with
  | nil =>
      exact ⟨hi0, hile⟩
  | cons x indices ih =>
      simp only [List.forIn_cons]
      split
      · apply ih
        · omega
        · have := hpred i0 (by assumption)
          omega
      · exact ⟨hi0, hile⟩

private theorem scan_le
    (indices : List ℕ) (bound i0 : ℕ)
    (pred : ℕ → Bool)
    (hpred : ∀ i, pred i = true → i < bound)
    (hile : i0 ≤ bound) :
    let result : ℕ := Id.run <|
      forIn indices i0 fun _ i =>
        if pred i then do
          pure PUnit.unit
          pure (.yield (i + 1))
        else pure (.done i)
    result ≤ bound := by
  induction indices generalizing i0 with
  | nil =>
      exact hile
  | cons x indices ih =>
      simp only [List.forIn_cons]
      split
      · apply ih
        have := hpred i0 (by assumption)
        omega
      · exact hile

private theorem scan_down_bounds
    (indices : List ℕ) (lower r0 : ℕ)
    (pred : ℕ → Bool)
    (hpred : ∀ r, pred r = true → lower < r)
    (hlower : lower ≤ r0) :
    let result : ℕ := Id.run <|
      forIn indices r0 fun _ r =>
        if pred r then do
          pure PUnit.unit
          pure (.yield (r - 1))
        else pure (.done r)
    lower ≤ result ∧ result ≤ r0 := by
  induction indices generalizing r0 with
  | nil =>
      exact ⟨hlower, Nat.le_refl _⟩
  | cons x indices ih =>
      simp only [List.forIn_cons]
      split
      ·
        have hlt := hpred r0 (by assumption)
        have hrest := ih (r0 - 1) (by omega)
        exact ⟨hrest.1,
          hrest.2.trans (Nat.sub_le r0 1)⟩
      · exact ⟨hlower, Nat.le_refl _⟩

theorem partialInsertionSort_perm (v : Array T)
    (isLess : T → T → Bool) :
    List.Perm (partialInsertionSort v isLess).2.toList v.toList := by
  simp only [partialInsertionSort,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  let body :
      ℕ → MProd ℕ (MProd (Option Bool) (Array T)) →
        Id (ForInStep
          (MProd ℕ (MProd (Option Bool) (Array T)))) :=
    fun _ r =>
      if r.snd.fst.isNone = true then do
        let i ←
          forIn (List.range' 0 (v.size + 1)) r.fst fun _ i =>
            if (decide (i < v.size) &&
                !isLess r.snd.snd[i]! r.snd.snd[i - 1]!) = true then do
              pure PUnit.unit
              pure (.yield (i + 1))
            else
              pure (.done i)
        if (i == v.size) = true then do
          pure PUnit.unit
          pure (.yield ⟨i, some true, r.snd.snd⟩)
        else if v.size < 50 then do
          pure PUnit.unit
          pure (.yield ⟨i, some false, r.snd.snd⟩)
        else do
          pure PUnit.unit
          pure (.yield
            ⟨i, r.snd.fst,
              overwrite
                (overwrite (swp r.snd.snd (i - 1) i) 0
                  (shiftTail
                    ((swp r.snd.snd (i - 1) i).extract 0 i)
                    isLess))
                i
                (shiftHead
                  ((overwrite (swp r.snd.snd (i - 1) i) 0
                    (shiftTail
                      ((swp r.snd.snd (i - 1) i).extract 0 i)
                      isLess)).extract i)
                  isLess)⟩)
      else do
        pure PUnit.unit
        pure (.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩)
  let Inv :=
    fun r : MProd ℕ (MProd (Option Bool) (Array T)) =>
      List.Perm r.snd.snd.toList v.toList ∧
      (r.snd.fst.isNone = true → 50 ≤ v.size →
        0 < r.fst ∧ r.fst ≤ v.size)
  have hbody :
      ∀ x ∈ List.range' 0 5, ∀ r, Inv r →
        match (body x r).run with
        | .done r' => Inv r'
        | .yield r' => Inv r' := by
    intro x hx r hr
    by_cases hnone : r.snd.fst.isNone = true
    ·
      simp only [body, hnone, ↓reduceIte, Id.run_bind]
      generalize hscan :
        (Id.run <| forIn (List.range' 0 (v.size + 1)) r.fst
          fun _ i =>
            if (decide (i < v.size) &&
                !isLess r.snd.snd[i]! r.snd.snd[i - 1]!) = true then do
              pure PUnit.unit
              pure (.yield (i + 1))
            else
              pure (.done i)) = i
      by_cases heq : (i == v.size) = true
      · simp only [heq, ↓reduceIte, Inv]
        exact ⟨hr.1, by simp⟩
      · simp only [heq]
        by_cases hshort : v.size < 50
        · simp only [hshort, ↓reduceIte, Inv]
          exact ⟨hr.1, by simp⟩
        · simp only [hshort, ↓reduceIte, Inv]
          have hstart := hr.2 hnone (by omega)
          have hscanBounds := bounded_scan
            (List.range' 0 (v.size + 1)) v.size r.fst
            (fun j =>
              decide (j < v.size) &&
                !isLess r.snd.snd[j]! r.snd.snd[j - 1]!)
            (by
              intro j hj
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
              exact hj.1)
            hstart.1 hstart.2
          rw [hscan] at hscanBounds
          have hilt : i < v.size := by
            have hne : i ≠ v.size := by
              intro hieq
              apply heq
              simp [hieq]
            omega
          have hrsize : r.snd.snd.size = v.size :=
            array_size_eq_of_perm hr.1
          have hilt' : i < r.snd.snd.size := by omega
          exact ⟨partialInsertionMutation_perm r.snd.snd isLess i
              hscanBounds.1 hilt' |>.trans hr.1,
            fun _ _ => hscanBounds⟩
    · simp only [body, hnone, Inv]
      exact hr
  have hinit : Inv ⟨1, none, v⟩ := by
    exact ⟨List.Perm.refl _, by simp; omega⟩
  have hloop := list_forIn_invariant
    (List.range' 0 5) body Inv ⟨1, none, v⟩
    (fun x hx r r' hr hstep => by
      have h := hbody x hx r hr
      rcases hstep with hstep | hstep
      · rw [hstep] at h
        exact h
      · rw [hstep] at h
        exact h)
    hinit
  simpa only [body, Inv] using hloop.1

private theorem KeySorted.take_succ
    (array : Array T) (key : T → ℕ) (index : ℕ)
    (hpositive : 0 < index) (hindex : index < array.size)
    (hsorted : KeySorted key (array.toList.take index))
    (hnext : key array[index - 1]! ≤ key array[index]!) :
    KeySorted key (array.toList.take (index + 1)) := by
  rw [List.take_succ_eq_append_getElem (by simpa using hindex)]
  rw [Array.getElem_toList hindex]
  rw [getElem!_pos array index hindex] at hnext
  apply KeySorted.append key _ _ hsorted (KeySorted.singleton key array[index])
  intro left hleft right hright
  simp only [List.mem_singleton] at hright
  subst right
  have hlength : (array.toList.take index).length = index := by
    simp only [List.length_take, Array.length_toList]
    omega
  have hprefixBound := KeySorted.keysLE_last key
    (array.toList.take index) hsorted (by omega)
  have hleftLast := hprefixBound left hleft
  have hlast : (array.toList.take index)[index - 1]! =
      array[index - 1]! := by
    rw [getElem!_pos _ _ (by rw [hlength]; omega),
      List.getElem_take]
    rw [Array.getElem_toList (by omega)]
    rw [getElem!_pos array (index - 1) (by omega)]
  rw [hlength, hlast] at hleftLast
  exact hleftLast.trans hnext

private theorem ascendingScan_sorted
    (indices : List ℕ) (array : Array T) (key : T → ℕ)
    (initial : ℕ) (hpositive : 0 < initial)
    (hbound : initial ≤ array.size)
    (hsorted : KeySorted key (array.toList.take initial)) :
    let result := Id.run <| forIn indices initial fun _ index =>
      if index < array.size &&
          !lessBy key array[index]! array[index - 1]! then do
        pure PUnit.unit
        pure (.yield (index + 1))
      else
        pure (.done index)
    0 < result ∧ result ≤ array.size ∧
      KeySorted key (array.toList.take result) := by
  induction indices generalizing initial with
  | nil => exact ⟨hpositive, hbound, hsorted⟩
  | cons _ indices inductionHypothesis =>
      simp only [List.forIn_cons]
      split
      next hstep =>
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true'] at hstep
        have hnext : key array[initial - 1]! ≤ key array[initial]! := by
          rw [lessBy_eq_false_iff] at hstep
          exact hstep.2
        exact inductionHypothesis (initial + 1) (by omega) (by omega)
          (KeySorted.take_succ array key initial hpositive hstep.1
            hsorted hnext)
      next _ => exact ⟨hpositive, hbound, hsorted⟩

private theorem swp_toList_take_before
    (array : Array T) (left right stop : ℕ)
    (hleft : left < array.size) (hright : right < array.size)
    (hstopLeft : stop ≤ left) (hstopRight : stop ≤ right) :
    (swp array left right).toList.take stop =
      array.toList.take stop := by
  apply List.ext_getElem
  · simp only [List.length_take, Array.length_toList, swp_size]
  · intro index hindexLeft hindexRight
    rw [List.getElem_take, List.getElem_take]
    have hindex : index < array.size := by
      have := hindexRight
      simp only [List.length_take, Array.length_toList] at this
      omega
    have hindexStop : index < stop := by
      have := hindexRight
      simp only [List.length_take, Array.length_toList] at this
      omega
    rw [Array.getElem_toList (by simpa only [swp_size] using hindex),
      Array.getElem_toList hindex,
      ← getElem!_pos (swp array left right) index
        (by simpa only [swp_size] using hindex),
      ← getElem!_pos array index hindex,
      swp_get! array left right index hleft hright,
      getElem!_pos array index hindex,
      if_neg (by omega), if_neg (by omega)]

private theorem partialInsertionMutation_prefix_sorted
    (array : Array T) (key : T → ℕ) (index : ℕ)
    (hpositive : 0 < index) (hindex : index < array.size)
    (hsorted : KeySorted key (array.toList.take index)) :
    let swapped := swp array (index - 1) index
    let sortedPrefix := shiftTail (swapped.extract 0 index) (lessBy key)
    let prefixed := overwrite swapped 0 sortedPrefix
    let suffix := shiftHead (prefixed.extract index prefixed.size) (lessBy key)
    let output := overwrite prefixed index suffix
    KeySorted key (output.toList.take index) := by
  let swapped := swp array (index - 1) index
  let prefixSource := swapped.extract 0 index
  let sortedPrefix := shiftTail prefixSource (lessBy key)
  let prefixed := overwrite swapped 0 sortedPrefix
  let suffixSource := prefixed.extract index prefixed.size
  let suffix := shiftHead suffixSource (lessBy key)
  let output := overwrite prefixed index suffix
  show KeySorted key (output.toList.take index)
  have hswappedSize : swapped.size = array.size := swp_size _ _ _
  have hprefixSourceSize : prefixSource.size = index := by
    simp [prefixSource]
    omega
  have hbeforeSwap : swapped.toList.take (index - 1) =
      array.toList.take (index - 1) := by
    exact swp_toList_take_before array (index - 1) index (index - 1)
      (by omega) hindex (Nat.le_refl _) (by omega)
  have hbeforeSorted : KeySorted key
      (prefixSource.toList.take (prefixSource.size - 1)) := by
    have hsmaller := KeySorted.take key
      (array.toList.take index) (index - 1) hsorted
    have horiginal : KeySorted key (array.toList.take (index - 1)) := by
      rw [List.take_take,
        show min (index - 1) index = index - 1 by omega] at hsmaller
      exact hsmaller
    simp only [prefixSource, Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
      hprefixSourceSize, List.take_take]
    rw [show min (index - 1) index = index - 1 by omega]
    rw [hbeforeSwap]
    exact horiginal
  have hprefixSorted : KeySorted key sortedPrefix.toList :=
    shiftTail_sorted prefixSource key hbeforeSorted
  have hprefixPerm := shiftTail_perm prefixSource (lessBy key)
  have hprefixSize : sortedPrefix.size = index := by
    have := array_size_eq_of_perm hprefixPerm
    rw [hprefixSourceSize] at this
    exact this
  have hprefixedSize : prefixed.size = array.size := by
    simp [prefixed, overwrite_size, hswappedSize]
  have hprefixedPrefix :
      KeySorted key (prefixed.toList.take index) := by
    have hoverwrite := overwrite_toList swapped 0 sortedPrefix (by
      simp only [Nat.zero_add, hprefixSize]
      omega)
    simp only [List.take_zero, List.nil_append, Nat.zero_add] at hoverwrite
    have hlength : sortedPrefix.toList.length = index := by
      simp only [Array.length_toList, hprefixSize]
    rw [hoverwrite, List.take_append_of_le_length (by omega),
      ← hlength, List.take_length]
    exact hprefixSorted
  have hsuffixPerm := shiftHead_perm suffixSource (lessBy key)
  have hsuffixSourceSize : suffixSource.size = prefixed.size - index := by
    simp [suffixSource]
  have hsuffixSize : suffix.size = prefixed.size - index := by
    have := array_size_eq_of_perm hsuffixPerm
    rw [hsuffixSourceSize] at this
    exact this
  have houtputPrefix : output.toList.take index =
      prefixed.toList.take index := by
    have hoverwrite := overwrite_toList prefixed index suffix (by
      rw [hsuffixSize]
      omega)
    rw [hoverwrite]
    rw [List.append_assoc]
    rw [List.take_append_of_le_length (by
      simp only [List.length_take, Array.length_toList]
      omega)]
    rw [List.take_of_length_le (by
      simp only [List.length_take, Array.length_toList]
      omega)]
  rw [houtputPrefix]
  exact hprefixedPrefix

/-- A successful nearly-sorted fast path really has scanned a sorted prefix
through the end of the array. -/
theorem partialInsertionSort_sorted
    (array : Array T) (key : T → ℕ)
    (hsuccess :
      (partialInsertionSort array (lessBy key)).1 = true) :
    KeySorted key
      (partialInsertionSort array (lessBy key)).2.toList := by
  by_cases hempty : array.size = 0
  · exfalso
    norm_num [partialInsertionSort, hempty, List.range'_eq_map_range,
      List.range_succ, List.forIn_cons] at hsuccess
  · simp only [partialInsertionSort,
      Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one] at hsuccess ⊢
    let body :
        ℕ → MProd ℕ (MProd (Option Bool) (Array T)) →
          Id (ForInStep
            (MProd ℕ (MProd (Option Bool) (Array T)))) :=
      fun _ state =>
        if state.snd.fst.isNone = true then do
          let index ←
            forIn (List.range' 0 (array.size + 1)) state.fst fun _ index =>
              if (decide (index < array.size) &&
                  !lessBy key state.snd.snd[index]!
                    state.snd.snd[index - 1]!) = true then do
                pure PUnit.unit
                pure (.yield (index + 1))
              else
                pure (.done index)
          if (index == array.size) = true then do
            pure PUnit.unit
            pure (.yield ⟨index, some true, state.snd.snd⟩)
          else if array.size < 50 then do
            pure PUnit.unit
            pure (.yield ⟨index, some false, state.snd.snd⟩)
          else do
            pure PUnit.unit
            pure (.yield
              ⟨index, state.snd.fst,
                overwrite
                  (overwrite (swp state.snd.snd (index - 1) index) 0
                    (shiftTail
                      ((swp state.snd.snd (index - 1) index).extract 0 index)
                      (lessBy key)))
                  index
                  (shiftHead
                    ((overwrite (swp state.snd.snd (index - 1) index) 0
                      (shiftTail
                        ((swp state.snd.snd (index - 1) index).extract 0 index)
                        (lessBy key))).extract index)
                    (lessBy key))⟩)
        else do
          pure PUnit.unit
          pure (.yield
            ⟨state.fst, state.snd.fst, state.snd.snd⟩)
    let Inv :=
      fun state : MProd ℕ (MProd (Option Bool) (Array T)) =>
        state.snd.snd.size = array.size ∧
        (state.snd.fst.isNone = true →
          0 < state.fst ∧ state.fst ≤ array.size ∧
            KeySorted key (state.snd.snd.toList.take state.fst)) ∧
        (state.snd.fst = some true →
          KeySorted key state.snd.snd.toList)
    have hbody :
        ∀ outer ∈ List.range' 0 5, ∀ state, Inv state →
          match (body outer state).run with
          | .done next => Inv next
          | .yield next => Inv next := by
      intro outer houter state hinvariant
      by_cases hnone : state.snd.fst.isNone = true
      · simp only [body, hnone, ↓reduceIte, Id.run_bind]
        generalize hscan :
          (Id.run <| forIn (List.range' 0 (array.size + 1)) state.fst
            fun _ index =>
              if (decide (index < array.size) &&
                  !lessBy key state.snd.snd[index]!
                    state.snd.snd[index - 1]!) = true then do
                pure PUnit.unit
                pure (.yield (index + 1))
              else
                pure (.done index)) = index
        have hstart := hinvariant.2.1 hnone
        have hscanResult := ascendingScan_sorted
          (List.range' 0 (array.size + 1)) state.snd.snd key
          state.fst hstart.1 (by omega) hstart.2.2
        rw [hinvariant.1] at hscanResult
        rw [hscan] at hscanResult
        by_cases hend : (index == array.size) = true
        · simp only [hend, ↓reduceIte, Inv]
          have hindex : index = array.size := by simpa using hend
          refine ⟨hinvariant.1, by simp, ?_⟩
          intro _
          have hlength : state.snd.snd.toList.length = index := by
            simp only [Array.length_toList, hinvariant.1, hindex]
          have hsorted := hscanResult.2.2
          rw [← hlength, List.take_length] at hsorted
          exact hsorted
        · simp only [hend]
          by_cases hshort : array.size < 50
          · simp only [hshort, ↓reduceIte, Inv]
            exact ⟨hinvariant.1, by simp⟩
          · simp only [hshort, ↓reduceIte, Inv]
            have hindexLt : index < state.snd.snd.size := by
              have hindexNe : index ≠ array.size := by
                intro heq
                exact hend (by simp [heq])
              omega
            have hmutationPerm := partialInsertionMutation_perm
              state.snd.snd (lessBy key) index hscanResult.1 hindexLt
            have hmutationSize := array_size_eq_of_perm hmutationPerm
            refine ⟨hmutationSize.trans hinvariant.1,
              fun _ => ⟨hscanResult.1, hscanResult.2.1, ?_⟩, ?_⟩
            · exact partialInsertionMutation_prefix_sorted
                state.snd.snd key index hscanResult.1 hindexLt
                hscanResult.2.2
            · intro himpossible
              have : False := by
                rw [himpossible] at hnone
                simp at hnone
              exact this.elim
      · simp only [body, hnone, Inv]
        exact hinvariant
    have hinitial : Inv ⟨1, none, array⟩ := by
      dsimp only [Inv]
      refine ⟨rfl, ?_, by simp⟩
      intro _
      refine ⟨by omega, by omega, ?_⟩
      have hsingle : KeySorted key (array.toList.take 1) := by
        rw [KeySorted, List.sortedLE_iff_pairwise,
          List.pairwise_map, List.pairwise_iff_get]
        intro left right horder
        have hleft := left.isLt
        have hright := right.isLt
        simp only [List.length_take] at hleft hright
        omega
      exact hsingle
    have hloop := list_forIn_invariant
      (List.range' 0 5) body Inv ⟨1, none, array⟩
      (fun outer houter state next hinvariant hstep => by
        have h := hbody outer houter state hinvariant
        rcases hstep with hstep | hstep
        · rw [hstep] at h
          exact h
        · rw [hstep] at h
          exact h)
      hinitial
    let final := Id.run <| forIn (List.range' 0 5)
      ⟨1, none, array⟩ body
    change final.snd.fst.getD false = true at hsuccess
    change KeySorted key final.snd.snd.toList
    have hsuccessOption : final.snd.fst = some true := by
      cases hoption : final.snd.fst <;> simp_all
    have hfinalSorted := hloop.2.2 hsuccessOption
    exact hfinalSorted

omit [Inhabited T] in
theorem extract_split_toList (a : Array T) (i : ℕ) :
    (a.extract 0 i ++ a.extract i a.size).toList = a.toList := by
  simp only [Array.toList_append, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero]
  rw [Nat.sub_zero]
  have hlen :
      a.size - i = (a.toList.drop i).length := by simp
  rw [hlen, List.take_length]
  rw [List.take_append_drop]

omit [Inhabited T] in
theorem reverse_perm (a : Array T) :
    List.Perm a.reverse.toList a.toList := by
  rw [Array.toList_reverse]
  exact List.reverse_perm _

theorem extract_pivot_split_toList (a : Array T) (i : ℕ)
    (hi : i < a.size) :
    (a.extract 0 i).toList ++ [a[i]!] ++
        (a.extract (i + 1) a.size).toList =
      a.toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  have hget : a[i]! = a.toList[i] := by simp [hi]
  rw [hget]
  have htail :
      (a.toList.drop (i + 1)).take (a.size - (i + 1)) =
        a.toList.drop (i + 1) := by
    have hlen :
        (a.toList.drop (i + 1)).length = a.size - (i + 1) := by
      simp
    rw [← hlen, List.take_length]
  rw [htail, List.take_concat_get' _ _ (by simpa using hi),
    List.take_append_drop]

def PartitionInBlocksPermContract : Prop :=
  ∀ (v : Array T) (pivot : T) (isLess : T → T → Bool),
    let result := partitionInBlocks v pivot isLess
    result.1 ≤ v.size ∧ List.Perm result.2.toList v.toList

theorem partitionInBlocks_perm_contract :
    PartitionInBlocksPermContract (T := T) :=
  partitionInBlocks_contract

private theorem partitionP_mutations_perm
    (hblocks : PartitionInBlocksPermContract (T := T))
    (v0 : Array T) (pivotIdx l r : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIdx < v0.size)
    (hlr : l ≤ r) (hr : r < v0.size) :
    let v1 := swp v0 0 pivotIdx
    let block := partitionInBlocks
      (v1.extract (1 + l) (1 + r)) v1[0]! isLess
    let v2 := overwrite v1 (1 + l) block.2
    let mid := l + block.1
    List.Perm (swp v2 0 mid).toList v0.toList := by
  let v1 := swp v0 0 pivotIdx
  have hp1 : List.Perm v1.toList v0.toList := by
    apply swp_perm
    · omega
    · exact hpivot
  have hv1size : v1.size = v0.size :=
    array_size_eq_of_perm hp1
  let source := v1.extract (1 + l) (1 + r)
  let block := partitionInBlocks source v1[0]! isLess
  have hb := hblocks source v1[0]! isLess
  have hsourceSize : source.size = r - l := by
    simp only [source, Array.size_extract]
    omega
  have hblockSize : block.2.size = source.size :=
    array_size_eq_of_perm hb.2
  let v2 := overwrite v1 (1 + l) block.2
  have hp2 : List.Perm v2.toList v1.toList := by
    apply overwrite_perm_of_extract
    · omega
    ·
      have hend : 1 + l + block.2.size = 1 + r := by omega
      simpa [source, hend] using hb.2
  have hv2size : v2.size = v1.size :=
    array_size_eq_of_perm hp2
  have hmid : l + block.1 < v2.size := by
    have hcount := hb.1
    change block.1 ≤ source.size at hcount
    omega
  exact (swp_perm v2 0 (l + block.1)
    (by omega) hmid).trans (hp2.trans hp1)

private theorem partitionP_scan_bounds
    (a : Array T) (isLess : T → T → Bool)
    (hsize : 0 < a.size) :
    let l := Id.run <| forIn (List.range' 0 a.size) 0 fun _ l =>
      if (decide (l < a.size - 1) &&
          isLess a[1 + l]! a[0]!) = true then do
        pure PUnit.unit
        pure (.yield (l + 1))
      else
        pure (.done l)
    let r := Id.run <|
      forIn (List.range' 0 a.size) (a.size - 1) fun _ r =>
        if (decide (l < r) &&
            !isLess a[1 + (r - 1)]! a[0]!) = true then do
          pure PUnit.unit
          pure (.yield (r - 1))
        else
          pure (.done r)
    l ≤ r ∧ r < a.size := by
  let l := Id.run <| forIn (List.range' 0 a.size) 0 fun _ l =>
    if (decide (l < a.size - 1) &&
        isLess a[1 + l]! a[0]!) = true then do
      pure PUnit.unit
      pure (.yield (l + 1))
    else
      pure (.done l)
  have hl : l ≤ a.size - 1 := by
    exact scan_le (List.range' 0 a.size)
      (a.size - 1) 0
      (fun l =>
        decide (l < a.size - 1) &&
          isLess a[1 + l]! a[0]!)
      (by
        intro j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        exact hj.1)
      (by omega)
  let r := Id.run <|
    forIn (List.range' 0 a.size) (a.size - 1) fun _ r =>
      if (decide (l < r) &&
          !isLess a[1 + (r - 1)]! a[0]!) = true then do
        pure PUnit.unit
        pure (.yield (r - 1))
      else
        pure (.done r)
  have hrange : l ≤ r ∧ r ≤ a.size - 1 := by
    exact scan_down_bounds (List.range' 0 a.size)
      l (a.size - 1)
      (fun r =>
        decide (l < r) &&
          !isLess a[1 + (r - 1)]! a[0]!)
      (by
        intro j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        exact hj.1)
      hl
  have hout : l ≤ r ∧ r < a.size :=
    ⟨hrange.1, hrange.2.trans_lt (by omega)⟩
  simpa only [l, r] using hout

theorem partitionP_perm_of_blocks_contract
    (hblocks : PartitionInBlocksPermContract (T := T))
    (v : Array T) (pivotIdx : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIdx < v.size) :
    List.Perm (partitionP v pivotIdx isLess).2.toList v.toList := by
  simp only [partitionP,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, Id.run_bind]
  generalize hscanL :
    (Id.run <| forIn
      (List.range' 0 (swp v 0 pivotIdx).size) 0 fun _ l =>
      if (decide (l < (swp v 0 pivotIdx).size - 1) &&
          isLess
            (swp v 0 pivotIdx)[1 + l]!
            (swp v 0 pivotIdx)[0]!) = true then do
        pure PUnit.unit
        pure (.yield (l + 1))
      else
        pure (.done l)) = l
  generalize hscanR :
    (Id.run <| forIn
      (List.range' 0 (swp v 0 pivotIdx).size)
      ((swp v 0 pivotIdx).size - 1)
      fun _ r =>
        if (decide (l < r) &&
            !isLess
              (swp v 0 pivotIdx)[1 + (r - 1)]!
              (swp v 0 pivotIdx)[0]!) = true then do
          pure PUnit.unit
          pure (.yield (r - 1))
        else
          pure (.done r)) = r
  have hp1 := swp_perm v 0 pivotIdx (by omega) hpivot
  have hv1size :
      (swp v 0 pivotIdx).size = v.size :=
    array_size_eq_of_perm hp1
  have hrange := partitionP_scan_bounds
    (swp v 0 pivotIdx) isLess (by omega)
  dsimp only at hrange
  rw [hscanL, hscanR] at hrange
  generalize hblock :
    partitionInBlocks
      ((swp v 0 pivotIdx).extract (1 + l) (1 + r))
      (swp v 0 pivotIdx)[0]! isLess = block
  have hr : r < v.size := by
    rw [← hv1size]
    exact hrange.2
  have hmut := partitionP_mutations_perm
    hblocks v pivotIdx l r isLess hpivot hrange.1 hr
  dsimp only at hmut
  rw [hblock] at hmut
  exact hmut

/- The remaining end-to-end proof can be cleanly factored through these
helper contracts.  This theorem is intentionally left below the concrete
primitive milestones while the loop contracts are established. -/
private def scanLeft :
    List ℕ → ℕ → ℕ → T → Array T →
      (T → T → Bool) → ℕ
  | [], left, _, _, _, _ => left
  | _ :: indices, left, right, pivot, array, isLess =>
      if left < right && !isLess pivot (array[1 + left]!) then
        scanLeft indices (left + 1) right pivot array isLess
      else
        left

private def scanRight :
    List ℕ → ℕ → ℕ → T → Array T →
      (T → T → Bool) → ℕ
  | [], _, right, _, _, _ => right
  | _ :: indices, left, right, pivot, array, isLess =>
      if left < right && isLess pivot (array[1 + (right - 1)]!) then
        scanRight indices left (right - 1) pivot array isLess
      else
        right

/-- Reversing and complementing a strict comparison turns the scans used by
`partitionEqual` into the two scans used by `partitionP`. -/
private def dualLess (isLess : T → T → Bool) (left right : T) : Bool :=
  !isLess right left

private theorem scanLeft_lt
    (indices : List ℕ) (left right bound : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool)
    (hleft : left < bound) (hright : right < bound) :
    scanLeft indices left right pivot array isLess < bound := by
  induction indices generalizing left with
  | nil =>
      exact hleft
  | cons index indices ih =>
      simp only [scanLeft]
      split
      · exact ih (left + 1) (by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          omega)
      · exact hleft

private theorem scanRight_le
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    scanRight indices left right pivot array isLess ≤ right := by
  induction indices generalizing right with
  | nil =>
      exact Nat.le_refl _
  | cons index indices ih =>
      simp only [scanRight]
      split
      · exact (ih (right - 1)).trans (Nat.sub_le right 1)
      · exact Nat.le_refl _

private theorem scanLeft_le
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) (hle : left ≤ right) :
    scanLeft indices left right pivot array isLess ≤ right := by
  induction indices generalizing left with
  | nil => exact hle
  | cons index indices inductionHypothesis =>
      simp only [scanLeft]
      split
      · apply inductionHypothesis
        simp only [Bool.and_eq_true, decide_eq_true_eq] at *
        omega
      · exact hle

private theorem scanLeft_ge
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    left ≤ scanLeft indices left right pivot array isLess := by
  induction indices generalizing left with
  | nil => exact Nat.le_refl _
  | cons index indices inductionHypothesis =>
      simp only [scanLeft]
      split
      · exact Nat.le_add_right left 1 |>.trans (inductionHypothesis (left + 1))
      · exact Nat.le_refl _

private theorem scanRight_ge
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) (hle : left ≤ right) :
    left ≤ scanRight indices left right pivot array isLess := by
  induction indices generalizing right with
  | nil => exact hle
  | cons index indices inductionHypothesis =>
      simp only [scanRight]
      split
      · apply inductionHypothesis
        simp only [Bool.and_eq_true, decide_eq_true_eq] at *
        omega
      · exact hle

private theorem scanLeft_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array (1 + left)
      (1 + scanLeft indices left right pivot array isLess)
      (fun item => isLess pivot item = false) := by
  induction indices generalizing left with
  | nil => exact RangeAll.empty array (1 + left) _
  | cons index indices inductionHypothesis =>
      simp only [scanLeft]
      split
      next hstep =>
        have hless : isLess pivot array[1 + left]! = false := by
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true'] at hstep
          exact hstep.2
        have hrest := inductionHypothesis (left + 1)
        intro position hpositionStart hpositionStop
        by_cases hfirst : position = 1 + left
        · simpa [hfirst] using hless
        · apply hrest position <;> omega
      next _ => exact RangeAll.empty array (1 + left) _

private theorem scanRight_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array (1 + scanRight indices left right pivot array isLess)
      (1 + right) (fun item => isLess pivot item = true) := by
  induction indices generalizing right with
  | nil => exact RangeAll.empty array (1 + right) _
  | cons index indices inductionHypothesis =>
      simp only [scanRight]
      split
      next hstep =>
        have hless : isLess pivot array[1 + (right - 1)]! = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          exact hstep.2
        have hrest := inductionHypothesis (right - 1)
        intro position hpositionStart hpositionStop
        by_cases hlast : position = right
        · simpa [hlast, show 1 + (right - 1) = right by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
            omega] using hless
        · apply hrest position <;> omega
      next _ => exact RangeAll.empty array (1 + right) _

private theorem scanLeft_stops_on_greater
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool)
    (hcapacity : right - left ≤ indices.length)
    (hresult : scanLeft indices left right pivot array isLess < right) :
    isLess pivot
      array[1 + scanLeft indices left right pivot array isLess]! = true := by
  induction indices generalizing left with
  | nil =>
      simp only [scanLeft, List.length_nil] at hcapacity hresult
      omega
  | cons index indices inductionHypothesis =>
      by_cases hstep :
          (decide (left < right) &&
            !isLess pivot array[1 + left]!) = true
      · rw [scanLeft, if_pos hstep] at hresult ⊢
        apply inductionHypothesis
        · simp only [List.length_cons] at hcapacity
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          omega
        · exact hresult
      · rw [scanLeft, if_neg hstep] at hresult ⊢
        have hleftRight : left < right := hresult
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true'] at hstep
        cases hless : isLess pivot array[1 + left]! with
        | false => exact (hstep ⟨hleftRight, hless⟩).elim
        | true => rfl

private theorem scanRight_stops_on_not_greater
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool)
    (hcapacity : right - left ≤ indices.length)
    (hresult : left < scanRight indices left right pivot array isLess) :
    isLess pivot
      array[scanRight indices left right pivot array isLess]! = false := by
  induction indices generalizing right with
  | nil =>
      exfalso
      simp only [scanRight, List.length_nil] at hresult hcapacity
      omega
  | cons index indices inductionHypothesis =>
      by_cases hstep :
          (decide (left < right) &&
            isLess pivot array[1 + (right - 1)]!) = true
      · rw [scanRight, if_pos hstep] at hresult ⊢
        apply inductionHypothesis
        · simp only [List.length_cons] at hcapacity
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          omega
        · exact hresult
      · rw [scanRight, if_neg hstep] at hresult ⊢
        have hleftRight : left < right := hresult
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
        cases hless : isLess pivot array[1 + (right - 1)]! with
        | true => exact (hstep ⟨hleftRight, hless⟩).elim
        | false =>
            simpa [show 1 + (right - 1) = right by omega] using hless

private theorem scanLeft_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices left fun _ current =>
      if current < right &&
          !isLess pivot (array[1 + current]!) then
        do
          pure PUnit.unit
          pure (.yield (current + 1))
      else
        pure (.done current)) =
      scanLeft indices left right pivot array isLess := by
  induction indices generalizing left with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.forIn_cons, scanLeft]
      split
      · exact ih (left + 1)
      · rfl

private theorem scanRight_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices right fun _ current =>
      if left < current &&
          isLess pivot (array[1 + (current - 1)]!) then
        do
          pure PUnit.unit
          pure (.yield (current - 1))
      else
        pure (.done current)) =
      scanRight indices left right pivot array isLess := by
  induction indices generalizing right with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.forIn_cons, scanRight]
      split
      · exact ih (right - 1)
      · rfl

private theorem partitionScanLeft_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices left fun _ current =>
      if current < right &&
          isLess (array[1 + current]!) pivot then
        do
          pure PUnit.unit
          pure (.yield (current + 1))
      else
        pure (.done current)) =
      scanLeft indices left right pivot array (dualLess isLess) := by
  simpa only [dualLess, Bool.not_not] using
    scanLeft_forIn indices left right pivot array (dualLess isLess)

private theorem partitionScanRight_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices right fun _ current =>
      if left < current &&
          !isLess (array[1 + (current - 1)]!) pivot then
        do
          pure PUnit.unit
          pure (.yield (current - 1))
      else
        pure (.done current)) =
      scanRight indices left right pivot array (dualLess isLess) := by
  simpa only [dualLess] using
    scanRight_forIn indices left right pivot array (dualLess isLess)

private theorem partitionScanLeft_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array (1 + left)
      (1 + scanLeft indices left right pivot array (dualLess isLess))
      (fun item => isLess item pivot = true) := by
  have h :=
    scanLeft_rangeAll indices left right pivot array (dualLess isLess)
  intro index hstart hstop
  have hnot := h index hstart hstop
  simp only [dualLess] at hnot
  cases hvalue : isLess array[index]! pivot <;> simp_all

private theorem partitionScanRight_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array
      (1 + scanRight indices left right pivot array (dualLess isLess))
      (1 + right) (fun item => isLess item pivot = false) := by
  have h :=
    scanRight_rangeAll indices left right pivot array (dualLess isLess)
  intro index hstart hstop
  have hnot := h index hstart hstop
  simp only [dualLess] at hnot
  cases hvalue : isLess array[index]! pivot <;> simp_all

/-- `partitionP` places its selected pivot between the strictly-smaller and
the remaining elements. -/
theorem partitionP_order
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    let result := partitionP array pivotIndex isLess
    RangeAll result.2 0 result.1.1
        (fun item => isLess item result.2[result.1.1]! = true) ∧
      RangeAll result.2 (result.1.1 + 1) result.2.size
        (fun item => isLess item result.2[result.1.1]! = false) := by
  simp only [partitionP,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, Id.run_bind]
  generalize hscanLeft :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size) 0
      fun _ left =>
        if decide (left < (swp array 0 pivotIndex).size - 1) &&
            isLess
              (swp array 0 pivotIndex)[1 + left]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (left + 1))
        else
          pure (.done left)) = left
  generalize hscanRight :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size)
      ((swp array 0 pivotIndex).size - 1)
      fun _ right =>
        if decide (left < right) &&
            !isLess
              (swp array 0 pivotIndex)[1 + (right - 1)]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (right - 1))
        else
          pure (.done right)) = right
  generalize hblock :
    partitionInBlocks
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right))
      (swp array 0 pivotIndex)[0]! isLess = block
  let swapped := swp array 0 pivotIndex
  let source := swapped.extract (1 + left) (1 + right)
  let rewritten := overwrite swapped (1 + left) block.2
  let middle := left + block.1
  have hswappedSize : swapped.size = array.size := swp_size _ _ _
  have hpositive : 0 < swapped.size := by
    rw [hswappedSize]
    omega
  have hrange := partitionP_scan_bounds swapped isLess hpositive
  dsimp only [swapped] at hrange
  rw [hscanLeft, hscanRight] at hrange
  have hrangeSwapped : left ≤ right ∧ right < swapped.size := by
    simpa only [swapped] using hrange
  have hleftDefinition := partitionScanLeft_forIn
    (List.range' 0 swapped.size) 0 (swapped.size - 1)
    swapped[0]! swapped isLess
  dsimp only [swapped] at hleftDefinition
  rw [hscanLeft] at hleftDefinition
  have hrightDefinition := partitionScanRight_forIn
    (List.range' 0 swapped.size) left (swapped.size - 1)
    swapped[0]! swapped isLess
  dsimp only [swapped] at hrightDefinition
  rw [hscanRight] at hrightDefinition
  have hleftOrder := partitionScanLeft_rangeAll
    (List.range' 0 swapped.size) 0 (swapped.size - 1)
    swapped[0]! swapped isLess
  rw [← hleftDefinition] at hleftOrder
  simp only [Nat.add_zero] at hleftOrder
  have hrightOrder := partitionScanRight_rangeAll
    (List.range' 0 swapped.size) left (swapped.size - 1)
    swapped[0]! swapped isLess
  rw [← hrightDefinition] at hrightOrder
  have hblockContract := partitionInBlocks_contract
    source swapped[0]! isLess
  have hblockOrder := partitionInBlocks_order
    source swapped[0]! isLess
  dsimp only [source, swapped] at hblockContract hblockOrder
  rw [hblock] at hblockContract hblockOrder
  have hsourceSize : source.size = right - left := by
    simp only [source, Array.size_extract]
    omega
  have hblockSize : block.2.size = source.size :=
    array_size_eq_of_perm hblockContract.2
  have hblockCount : block.1 ≤ block.2.size := by
    rw [hblockSize]
    simpa only [source, swapped] using hblockContract.1
  have hfit : 1 + left + block.2.size ≤ swapped.size := by
    rw [hblockSize, hsourceSize]
    omega
  have hmiddle : middle < rewritten.size := by
    have hcount : block.1 ≤ source.size := by
      simpa only [source, swapped] using hblockContract.1
    simp only [middle, rewritten, overwrite_size]
    rw [hsourceSize] at hcount
    omega
  have hprefix : RangeAll rewritten 1 (1 + middle)
      (fun item => isLess item swapped[0]! = true) := by
    intro index hindexStart hindexStop
    simp only [middle] at hindexStop
    rw [overwrite_get! swapped block.2 (1 + left) index hfit]
    by_cases hbefore : index < 1 + left
    · rw [if_neg (by omega)]
      exact hleftOrder index hindexStart hbefore
    · rw [if_pos (by
          constructor
          · omega
          · rw [hblockSize, hsourceSize]
            omega)]
      apply hblockOrder.1 (index - (1 + left))
      · omega
      · omega
  have hsuffix : RangeAll rewritten (1 + middle) rewritten.size
      (fun item => isLess item swapped[0]! = false) := by
    intro index hindexStart hindexStop
    rw [overwrite_get! swapped block.2 (1 + left) index hfit]
    by_cases hbeforeRight : index < 1 + right
    · rw [if_pos (by
          constructor
          · simp only [middle] at hindexStart
            omega
          · rw [hblockSize, hsourceSize]
            omega)]
      apply hblockOrder.2 (index - (1 + left))
      · simp only [middle] at hindexStart
        omega
      · rw [hblockSize, hsourceSize]
        omega
    · rw [if_neg (by
          rw [hblockSize, hsourceSize]
          omega)]
      apply hrightOrder index
      · omega
      · have hrightStop : 1 + (swapped.size - 1) = swapped.size := by
          omega
        rw [hrightStop]
        simpa only [rewritten, overwrite_size] using hindexStop
  have hpivotValue : (swp rewritten 0 middle)[middle]! = swapped[0]! := by
    rw [swp_get! rewritten 0 middle middle (by
      simpa only [rewritten, overwrite_size] using hpositive) hmiddle]
    have hzero : rewritten[0]! = swapped[0]! := by
      simp only [rewritten]
      rw [overwrite_get! swapped block.2 (1 + left) 0 hfit,
        if_neg (by omega)]
    by_cases hmiddleZero : middle = 0
    · simp [hmiddleZero, hzero]
    · simp [hmiddleZero, hzero]
  show
    RangeAll (swp rewritten 0 middle) 0 middle
        (fun item => isLess item (swp rewritten 0 middle)[middle]! = true) ∧
      RangeAll (swp rewritten 0 middle) (middle + 1)
        (swp rewritten 0 middle).size
        (fun item => isLess item (swp rewritten 0 middle)[middle]! = false)
  constructor
  · intro index hindexStart hindexStop
    rw [hpivotValue,
      swp_get! rewritten 0 middle index (by
        simpa only [rewritten, overwrite_size] using hpositive) hmiddle]
    by_cases hindexZero : index = 0
    · rw [if_pos hindexZero]
      exact hprefix middle (by omega) (by omega)
    · rw [if_neg hindexZero, if_neg (by omega)]
      exact hprefix index (by omega) (by omega)
  · intro index hindexStart hindexStop
    rw [hpivotValue,
      swp_get! rewritten 0 middle index (by
        simpa only [rewritten, overwrite_size] using hpositive) hmiddle,
      if_neg (by omega), if_neg (by omega)]
    apply hsuffix index
    · omega
    · simpa only [swp_size] using hindexStop

private def partitionEqualLoop
    (indices scanIndices : List ℕ)
    (pivot : T) (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    MProd Bool (MProd ℕ (MProd ℕ (Array T))) := Id.run do
  let mut state := state
  for _ in indices do
    let ⟨done, left, right, array⟩ := state
    if !done then
      let mut left := left
      for _ in scanIndices do
        if left < right &&
            !isLess pivot (array[1 + left]!) then
          left := left + 1
        else
          break
      let mut right := right
      for _ in scanIndices do
        if left < right &&
            isLess pivot (array[1 + (right - 1)]!) then
          right := right - 1
        else
          break
      if left ≥ right then
        state := ⟨true, left, right, array⟩
      else
        let swapRight := right - 1
        let nextArray := swp array (1 + left) (1 + swapRight)
        let nextLeft := left + 1
        state := ⟨done, nextLeft, swapRight, nextArray⟩
  return state

private def partitionEqualStep
    (scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    ForInStep (MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :=
  Id.run do
    let ⟨done, initialLeft, initialRight, array⟩ := state
    if !done then
      let mut left := initialLeft
      for _ in scanIndices do
        if left < initialRight &&
            !isLess pivot (array[1 + left]!) then
          left := left + 1
        else
          break
      let mut right := initialRight
      for _ in scanIndices do
        if left < right &&
            isLess pivot (array[1 + (right - 1)]!) then
          right := right - 1
        else
          break
      if left ≥ right then
        return .yield ⟨true, left, right, array⟩
      else
        return .yield ⟨done, left + 1, right - 1,
          swp array (1 + left) (1 + (right - 1))⟩
    else
      return .yield state

private theorem partitionEqualStep_isYield
    (scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    ∃ next, partitionEqualStep scanIndices pivot isLess state =
      .yield next := by
  rcases state with ⟨done, left, right, array⟩
  cases done with
  | true =>
      exact ⟨⟨true, left, right, array⟩,
        by simp [partitionEqualStep]⟩
  | false =>
      simp only [partitionEqualStep, Bool.not_false, ↓reduceIte]
      simp only [Id.run_bind]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

private theorem partitionEqualLoop_cons
    (index : ℕ) (indices scanIndices : List ℕ)
    (pivot : T) (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    partitionEqualLoop (index :: indices) scanIndices pivot isLess state =
      partitionEqualLoop indices scanIndices pivot isLess
        (partitionEqualStep scanIndices pivot isLess state).run := by
  rcases partitionEqualStep_isYield scanIndices pivot isLess state with
    ⟨next, hnext⟩
  rw [partitionEqualLoop]
  simp only [List.forIn_cons]
  simp only [Id.run_bind, Id.run_pure, LawfulMonad.pure_bind]
  have hbody := hnext
  simp [partitionEqualStep] at hbody
  simp only [Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq, ge_iff_le] at ⊢
  rw [hbody, hnext]
  simp only [ForInStep.run]
  rw [partitionEqualLoop]
  simp only [Id.run_bind, Id.run_pure, LawfulMonad.pure_bind,
    Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq,
    ge_iff_le]

private theorem partitionEqualLoop_perm
    (indices scanIndices : List ℕ) (bound : ℕ)
    (pivot : T) (isLess : T → T → Bool) :
    ∀ (done : Bool) (left right : ℕ) (array original : Array T),
      left < bound →
      right < bound →
      array.size = bound →
      List.Perm array.toList original.toList →
      let result :=
        partitionEqualLoop indices scanIndices pivot isLess
          ⟨done, left, right, array⟩
      result.2.1 < bound ∧
        List.Perm result.2.2.2.toList original.toList := by
  induction indices with
  | nil =>
      intro done left right array original hleft hright hsize hperm
      simpa [partitionEqualLoop] using And.intro hleft hperm
  | cons index indices ih =>
      intro done left right array original hleft hright hsize hperm
      cases done with
      | false =>
        let scannedLeft := Id.run <|
          forIn scanIndices left fun _ current =>
            if current < right &&
                !isLess pivot (array[1 + current]!) then do
              pure PUnit.unit
              pure (.yield (current + 1))
            else
              pure (.done current)
        let scannedRight := Id.run <|
          forIn scanIndices right fun _ current =>
            if scannedLeft < current &&
                isLess pivot (array[1 + (current - 1)]!) then do
              pure PUnit.unit
              pure (.yield (current - 1))
            else
              pure (.done current)
        have hleftEq :
            scannedLeft =
              scanLeft scanIndices left right pivot array isLess :=
          scanLeft_forIn scanIndices left right pivot array isLess
        have hrightEq :
            scannedRight =
              scanRight scanIndices scannedLeft right pivot array isLess :=
          scanRight_forIn scanIndices scannedLeft right pivot array isLess
        have hscannedLeft : scannedLeft < bound := by
          rw [hleftEq]
          exact scanLeft_lt scanIndices left right bound pivot array
            isLess hleft hright
        have hscannedRightLe : scannedRight ≤ right := by
          rw [hrightEq]
          exact scanRight_le scanIndices scannedLeft right pivot array
            isLess
        have hscannedRight : scannedRight < bound :=
          hscannedRightLe.trans_lt hright
        by_cases hfinished : scannedLeft ≥ scannedRight
        · have hstate :
              partitionEqualStep scanIndices pivot isLess
                  ⟨false, left, right, array⟩ =
                .yield ⟨true, scannedLeft, scannedRight, array⟩ := by
            unfold partitionEqualStep
            simp only [Bool.not_false, ↓reduceIte]
            change
              Id.run (if scannedRight ≤ scannedLeft then
                pure
                  (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
                    ForInStep
                      (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
              else
                pure
                  (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
                    swp array (1 + scannedLeft)
                      (1 + (scannedRight - 1))⟩)) = _
            rw [if_pos hfinished]
            rfl
          rw [partitionEqualLoop_cons, hstate]
          exact ih true scannedLeft scannedRight array original
            hscannedLeft hscannedRight hsize hperm
        · have hleftIndex : 1 + scannedLeft < bound := by
            omega
          have hrightIndex : 1 + (scannedRight - 1) < bound := by
            omega
          have hswap :=
            swp_perm array (1 + scannedLeft)
              (1 + (scannedRight - 1))
              (hsize ▸ hleftIndex) (hsize ▸ hrightIndex)
          have hnext :=
            ih false (scannedLeft + 1) (scannedRight - 1)
              (swp array (1 + scannedLeft)
                (1 + (scannedRight - 1))) original
              (by omega) (by omega)
              (by simpa [swp, Array.set!] using hsize)
              (hswap.trans hperm)
          have hstate :
              partitionEqualStep scanIndices pivot isLess
                  ⟨false, left, right, array⟩ =
                .yield ⟨false, scannedLeft + 1, scannedRight - 1,
                  swp array (1 + scannedLeft)
                    (1 + (scannedRight - 1))⟩ := by
            unfold partitionEqualStep
            simp only [Bool.not_false, ↓reduceIte]
            change
              Id.run (if scannedRight ≤ scannedLeft then
                pure
                  (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
                    ForInStep
                      (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
              else
                pure
                  (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
                    swp array (1 + scannedLeft)
                      (1 + (scannedRight - 1))⟩)) = _
            rw [if_neg hfinished]
            rfl
          rw [partitionEqualLoop_cons, hstate]
          exact hnext
      | true =>
        have hstate :
            partitionEqualStep scanIndices pivot isLess
                ⟨true, left, right, array⟩ =
              .yield ⟨true, left, right, array⟩ := by
          simp [partitionEqualStep]
        rw [partitionEqualLoop_cons, hstate]
        exact ih true left right array original
          hleft hright hsize hperm

private def EqualPartitionInvariant
    (key : T → ℕ) (pivot : T) (original : Array T)
    (left right : ℕ) (array : Array T) : Prop :=
  left ≤ right ∧ right < array.size ∧
    List.Perm array.toList original.toList ∧
    KeysGE key array.toList (key pivot) ∧
    RangeAll array 0 (1 + left)
      (fun item => key item = key pivot) ∧
    RangeAll array (1 + right) array.size
      (fun item => key pivot < key item)

private theorem equalPartitionScanStep
    (indices : List ℕ) (key : T → ℕ) (pivot : T)
    (original array : Array T) (left right : ℕ)
    (hcapacity : right - left ≤ indices.length)
    (hinvariant :
      EqualPartitionInvariant key pivot original left right array) :
    let scannedLeft :=
      scanLeft indices left right pivot array (lessBy key)
    let scannedRight :=
      scanRight indices scannedLeft right pivot array (lessBy key)
    let next :=
      if scannedLeft ≥ scannedRight then
        (scannedLeft, scannedRight, array)
      else
        (scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) scannedRight)
    EqualPartitionInvariant key pivot original
      next.1 next.2.1 next.2.2 := by
  rcases hinvariant with
    ⟨hle, hright, hperm, hglobal, hprefix, hsuffix⟩
  let scannedLeft :=
    scanLeft indices left right pivot array (lessBy key)
  let scannedRight :=
    scanRight indices scannedLeft right pivot array (lessBy key)
  have hscannedLeftLe : scannedLeft ≤ right :=
    scanLeft_le indices left right pivot array (lessBy key) hle
  have hscannedRightLe : scannedRight ≤ right :=
    scanRight_le indices scannedLeft right pivot array (lessBy key)
  have hscannedLeftRight : scannedLeft ≤ scannedRight :=
    scanRight_ge indices scannedLeft right pivot array (lessBy key)
      hscannedLeftLe
  have hleftScanRaw :=
    scanLeft_rangeAll indices left right pivot array (lessBy key)
  have hleftScan : RangeAll array (1 + left) (1 + scannedLeft)
      (fun item => key item = key pivot) := by
    intro position hpositionStart hpositionStop
    have hnotGreater := hleftScanRaw position hpositionStart hpositionStop
    change lessBy key pivot array[position]! = false at hnotGreater
    rw [lessBy_eq_false_iff] at hnotGreater
    have hlower := KeysGE.get! key array (key pivot) position hglobal
      (by omega)
    omega
  have hrightScanRaw :=
    scanRight_rangeAll indices scannedLeft right pivot array (lessBy key)
  have hrightScan : RangeAll array (1 + scannedRight) (1 + right)
      (fun item => key pivot < key item) := by
    intro position hpositionStart hpositionStop
    have hgreater := hrightScanRaw position hpositionStart hpositionStop
    simpa only [lessBy_eq_true_iff] using hgreater
  have hprefixScanned : RangeAll array 0 (1 + scannedLeft)
      (fun item => key item = key pivot) :=
    hprefix.append hleftScan
  have hsuffixScanned : RangeAll array (1 + scannedRight) array.size
      (fun item => key pivot < key item) :=
    hrightScan.append hsuffix
  show EqualPartitionInvariant key pivot original
    (if scannedLeft ≥ scannedRight then
      (scannedLeft, scannedRight, array)
    else
      (scannedLeft + 1, scannedRight - 1,
        swp array (1 + scannedLeft) scannedRight)).1
    (if scannedLeft ≥ scannedRight then
      (scannedLeft, scannedRight, array)
    else
      (scannedLeft + 1, scannedRight - 1,
        swp array (1 + scannedLeft) scannedRight)).2.1
    (if scannedLeft ≥ scannedRight then
      (scannedLeft, scannedRight, array)
    else
      (scannedLeft + 1, scannedRight - 1,
        swp array (1 + scannedLeft) scannedRight)).2.2
  split
  next hfinished =>
    exact ⟨hscannedLeftRight, hscannedRightLe.trans_lt hright,
      hperm, hglobal, hprefixScanned, hsuffixScanned⟩
  next hfinished =>
    have hstrict : scannedLeft < scannedRight := by omega
    have hleftGreater :
        key pivot < key array[scannedLeft + 1]! := by
      have hresult := scanLeft_stops_on_greater indices left right
        pivot array (lessBy key) hcapacity
        (hstrict.trans_le hscannedRightLe)
      simpa only [scannedLeft, lessBy_eq_true_iff, Nat.add_comm] using hresult
    have hrightNotGreater :
        key array[scannedRight]! ≤ key pivot := by
      have hresult := scanRight_stops_on_not_greater indices
        scannedLeft right pivot array (lessBy key)
        (by
          have hleftLe := scanLeft_ge indices left right pivot array
            (lessBy key)
          omega)
        hstrict
      simpa only [scannedRight, lessBy_eq_false_iff] using hresult
    have hrightLower := KeysGE.get! key array (key pivot) scannedRight
      hglobal (hscannedRightLe.trans_lt hright)
    have hrightEqual : key array[scannedRight]! = key pivot := by omega
    have hgap : scannedLeft + 1 < scannedRight := by
      by_contra hnot
      have heq : scannedRight = scannedLeft + 1 := by omega
      rw [heq] at hrightEqual
      omega
    let next := swp array (1 + scannedLeft) scannedRight
    have hleftIndex : 1 + scannedLeft < array.size := by omega
    have hrightIndex : scannedRight < array.size := by omega
    have hnextPerm : List.Perm next.toList original.toList :=
      (swp_perm array (1 + scannedLeft) scannedRight
        hleftIndex hrightIndex).trans hperm
    have hnextGlobal : KeysGE key next.toList (key pivot) :=
      KeysGE.perm key
        (swp_perm array (1 + scannedLeft) scannedRight
          hleftIndex hrightIndex).symm hglobal
    have hnextPrefixBase : RangeAll next 0 (1 + scannedLeft)
        (fun item => key item = key pivot) := by
      apply RangeAll.swp array (1 + scannedLeft) scannedRight
        0 (1 + scannedLeft) _ hleftIndex hrightIndex hprefixScanned
      · omega
      · omega
    have hnextPrefixPoint : RangeAll next (1 + scannedLeft)
        (1 + (scannedLeft + 1))
        (fun item => key item = key pivot) := by
      intro position hpositionStart hpositionStop
      have hposition : position = 1 + scannedLeft := by omega
      subst position
      rw [swp_get! array (1 + scannedLeft) scannedRight
        (1 + scannedLeft) hleftIndex hrightIndex, if_pos rfl]
      exact hrightEqual
    have hnextPrefix := hnextPrefixBase.append hnextPrefixPoint
    have hnextSuffixBase : RangeAll next (1 + scannedRight) next.size
        (fun item => key pivot < key item) := by
      rw [swp_size]
      apply RangeAll.swp array (1 + scannedLeft) scannedRight
        (1 + scannedRight) array.size _ hleftIndex hrightIndex
        hsuffixScanned
      · omega
      · omega
    have hnextSuffixPoint : RangeAll next (1 + (scannedRight - 1))
        (1 + scannedRight) (fun item => key pivot < key item) := by
      intro position hpositionStart hpositionStop
      have hposition : position = scannedRight := by omega
      subst position
      rw [swp_get! array (1 + scannedLeft) scannedRight scannedRight
        hleftIndex hrightIndex, if_neg (by omega), if_pos rfl]
      simpa only [Nat.add_comm] using hleftGreater
    have hnextSuffix : RangeAll next (1 + (scannedRight - 1)) next.size
        (fun item => key pivot < key item) := by
      exact hnextSuffixPoint.append hnextSuffixBase
    show EqualPartitionInvariant key pivot original
      (scannedLeft + 1) (scannedRight - 1) next
    exact ⟨by omega, by simpa [next, swp_size] using
        show scannedRight - 1 < array.size by omega,
      hnextPerm, hnextGlobal, hnextPrefix, hnextSuffix⟩

private def EqualPartitionStateInvariant
    (key : T → ℕ) (pivot : T) (original : Array T)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) : Prop :=
  EqualPartitionInvariant key pivot original
      state.2.1 state.2.2.1 state.2.2.2 ∧
    (state.1 = true → state.2.1 = state.2.2.1)

private theorem partitionEqualStep_stateInvariant
    (scanIndices : List ℕ) (key : T → ℕ) (pivot : T)
    (original : Array T)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hscanCapacity : state.2.2.2.size ≤ scanIndices.length)
    (hinvariant : EqualPartitionStateInvariant key pivot original state) :
    EqualPartitionStateInvariant key pivot original
      (partitionEqualStep scanIndices pivot (lessBy key) state).run := by
  rcases state with ⟨done, left, right, array⟩
  rcases hinvariant with ⟨hinvariant, hdoneEqual⟩
  cases done with
  | true =>
      simpa [partitionEqualStep, EqualPartitionStateInvariant] using
        And.intro hinvariant hdoneEqual
  | false =>
      have harrayCapacity : array.size ≤ scanIndices.length := by
        simpa using hscanCapacity
      let scannedLeft := Id.run <| forIn scanIndices left fun _ current =>
        if current < right &&
            !lessBy key pivot array[1 + current]! then do
          pure PUnit.unit
          pure (.yield (current + 1))
        else
          pure (.done current)
      let scannedRight := Id.run <|
        forIn scanIndices right fun _ current =>
          if scannedLeft < current &&
              lessBy key pivot array[1 + (current - 1)]! then do
            pure PUnit.unit
            pure (.yield (current - 1))
          else
            pure (.done current)
      have hleftEq : scannedLeft =
          scanLeft scanIndices left right pivot array (lessBy key) :=
        scanLeft_forIn scanIndices left right pivot array (lessBy key)
      have hrightEq : scannedRight =
          scanRight scanIndices scannedLeft right pivot array (lessBy key) :=
        scanRight_forIn scanIndices scannedLeft right pivot array (lessBy key)
      have hcapacity : right - left ≤ scanIndices.length := by
        have hright : right < array.size := by
          simpa using hinvariant.2.1
        omega
      have hsemantic := equalPartitionScanStep scanIndices key pivot
        original array left right hcapacity hinvariant
      dsimp only at hsemantic
      rw [← hleftEq] at hsemantic
      simp only [← hrightEq] at hsemantic
      by_cases hfinished : scannedLeft ≥ scannedRight
      · have hstep :
            partitionEqualStep scanIndices pivot (lessBy key)
                ⟨false, left, right, array⟩ =
              .yield ⟨true, scannedLeft, scannedRight, array⟩ := by
          unfold partitionEqualStep
          simp only [Bool.not_false, ↓reduceIte]
          change Id.run (if scannedRight ≤ scannedLeft then
            pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
              ForInStep
                (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
          else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
            swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) = _
          rw [if_pos hfinished]
          rfl
        rw [hstep]
        simp only [ForInStep.run]
        have hnextInvariant : EqualPartitionInvariant key pivot original
            scannedLeft scannedRight array := by
          simpa only [hfinished, if_true, Prod.fst, Prod.snd] using hsemantic
        refine ⟨hnextInvariant, ?_⟩
        · intro _
          show scannedLeft = scannedRight
          have hle := hnextInvariant.1
          omega
      · have hstep :
            partitionEqualStep scanIndices pivot (lessBy key)
                ⟨false, left, right, array⟩ =
              .yield ⟨false, scannedLeft + 1, scannedRight - 1,
                swp array (1 + scannedLeft) scannedRight⟩ := by
          unfold partitionEqualStep
          simp only [Bool.not_false, ↓reduceIte]
          change Id.run (if scannedRight ≤ scannedLeft then
            pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
              ForInStep
                (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
          else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
            swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) = _
          rw [if_neg hfinished]
          simp only [Id.run_pure]
          rw [show 1 + (scannedRight - 1) = scannedRight by omega]
        rw [hstep]
        simp only [ForInStep.run]
        refine ⟨?_, by simp⟩
        simpa only [scannedLeft, scannedRight, hfinished,
          if_false, Prod.fst, Prod.snd] using hsemantic

private theorem partitionEqualLoop_stateInvariant
    (indices scanIndices : List ℕ) (key : T → ℕ) (pivot : T)
    (original : Array T)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hscanCapacity : original.size ≤ scanIndices.length)
    (hinvariant : EqualPartitionStateInvariant key pivot original state) :
    EqualPartitionStateInvariant key pivot original
      (partitionEqualLoop indices scanIndices pivot (lessBy key) state) := by
  induction indices generalizing state with
  | nil => simpa [partitionEqualLoop] using hinvariant
  | cons index indices inductionHypothesis =>
      rw [partitionEqualLoop_cons]
      apply inductionHypothesis
      have hstateSize : state.2.2.2.size = original.size := by
        have hlength := hinvariant.1.2.2.1.length_eq
        simpa using hlength
      apply partitionEqualStep_stateInvariant
      · omega
      · exact hinvariant

private theorem partitionEqualStep_progress
    (scanIndices : List ℕ) (pivot : T) (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    let next := (partitionEqualStep scanIndices pivot isLess state).run
    next.1 = true ∨
      next.2.2.1 - next.2.1 < state.2.2.1 - state.2.1 := by
  rcases state with ⟨done, left, right, array⟩
  cases done with
  | true => simp [partitionEqualStep]
  | false =>
      let scannedLeft := Id.run <| forIn scanIndices left fun _ current =>
        if current < right && !isLess pivot array[1 + current]! then do
          pure PUnit.unit
          pure (.yield (current + 1))
        else
          pure (.done current)
      let scannedRight := Id.run <|
        forIn scanIndices right fun _ current =>
          if scannedLeft < current &&
              isLess pivot array[1 + (current - 1)]! then do
            pure PUnit.unit
            pure (.yield (current - 1))
          else
            pure (.done current)
      have hleftEq : scannedLeft =
          scanLeft scanIndices left right pivot array isLess :=
        scanLeft_forIn scanIndices left right pivot array isLess
      have hrightEq : scannedRight =
          scanRight scanIndices scannedLeft right pivot array isLess :=
        scanRight_forIn scanIndices scannedLeft right pivot array isLess
      have hleftGe : left ≤ scannedLeft := by
        have hbound := scanLeft_ge scanIndices left right pivot array isLess
        rwa [← hleftEq] at hbound
      have hrightLe : scannedRight ≤ right := by
        have hbound := scanRight_le scanIndices scannedLeft right pivot array isLess
        rwa [← hrightEq] at hbound
      by_cases hfinished : scannedLeft ≥ scannedRight
      · left
        unfold partitionEqualStep
        simp only [Bool.not_false, ↓reduceIte]
        change (Id.run (if scannedRight ≤ scannedLeft then
          pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
            ForInStep
              (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
        else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩))).run.1 = true
        rw [if_pos hfinished]
        rfl
      · right
        have hstrict : scannedLeft < scannedRight := by omega
        unfold partitionEqualStep
        simp only [Bool.not_false, ↓reduceIte]
        change (Id.run (if scannedRight ≤ scannedLeft then
          pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
            ForInStep
              (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
        else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) |>.run).2.2.1 -
            (Id.run (if scannedRight ≤ scannedLeft then
          pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
            ForInStep
              (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
        else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) |>.run).2.1 <
            right - left
        rw [if_neg hfinished]
        simp only [ForInStep.run]
        omega

private theorem partitionEqualLoop_done_of_done
    (indices scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hdone : state.1 = true) :
    (partitionEqualLoop indices scanIndices pivot isLess state).1 = true := by
  induction indices generalizing state with
  | nil => simpa [partitionEqualLoop] using hdone
  | cons index indices inductionHypothesis =>
      rw [partitionEqualLoop_cons]
      apply inductionHypothesis
      rcases state with ⟨done, left, right, array⟩
      cases done <;> simp_all [partitionEqualStep]

private theorem partitionEqualLoop_eventually_done
    (indices scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hsteps : state.2.2.1 - state.2.1 < indices.length) :
    (partitionEqualLoop indices scanIndices pivot isLess state).1 = true := by
  induction indices generalizing state with
  | nil => simp at hsteps
  | cons index indices inductionHypothesis =>
      rw [partitionEqualLoop_cons]
      let next := (partitionEqualStep scanIndices pivot isLess state).run
      show (partitionEqualLoop indices scanIndices pivot isLess next).1 = true
      have hprogress := partitionEqualStep_progress
        scanIndices pivot isLess state
      change next.1 = true ∨
        next.2.2.1 - next.2.1 < state.2.2.1 - state.2.1 at hprogress
      rcases hprogress with hdone | hsmaller
      · exact partitionEqualLoop_done_of_done
          indices scanIndices pivot isLess next hdone
      · apply inductionHypothesis
        simp only [List.length_cons] at hsteps
        omega

theorem partitionEqual_perm
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    List.Perm
      (partitionEqual array pivotIndex isLess).2.toList
      array.toList := by
  have hnonempty : 0 < array.size := by omega
  let swapped := swp array 0 pivotIndex
  have hswap : List.Perm swapped.toList array.toList :=
    swp_perm array 0 pivotIndex hnonempty hpivot
  have hsize : swapped.size = array.size := by
    simp [swapped, swp, Array.set!]
  have hloop :=
    partitionEqualLoop_perm (List.range (swapped.size + 1))
      (List.range swapped.size) swapped.size swapped[0]! isLess
      false 0 (swapped.size - 1) swapped array
      (by omega) (by omega) rfl hswap
  simpa [partitionEqual, partitionEqualLoop, scanLeft, scanRight,
    List.range'_eq_map_range, swapped] using hloop.2

theorem partitionEqual_bound
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    let result := partitionEqual array pivotIndex isLess
    1 ≤ result.1 ∧ result.1 ≤ result.2.size := by
  dsimp only
  have hnonempty : 0 < array.size := by omega
  let swapped := swp array 0 pivotIndex
  have hswap : List.Perm swapped.toList array.toList :=
    swp_perm array 0 pivotIndex hnonempty hpivot
  have hsize : swapped.size = array.size := by
    simp [swapped, swp, Array.set!]
  have hloop :=
    partitionEqualLoop_perm (List.range (swapped.size + 1))
      (List.range swapped.size) swapped.size swapped[0]! isLess
      false 0 (swapped.size - 1) swapped array
      (by omega) (by omega) rfl hswap
  have hmidle :
      (partitionEqual array pivotIndex isLess).1 ≤ swapped.size := by
    simpa [partitionEqual, partitionEqualLoop, scanLeft, scanRight,
      List.range'_eq_map_range, swapped] using
        Nat.succ_le_iff.mpr hloop.1
  have hresultSize :
      (partitionEqual array pivotIndex isLess).2.size = array.size := by
    have hperm :=
      partitionEqual_perm array pivotIndex isLess hpivot
    simpa using hperm.length_eq
  constructor
  · simp [partitionEqual]
  · omega

/-- Under the predecessor condition used by pdqsort, `partitionEqual`
returns an equality prefix followed by elements strictly greater than the
pivot. -/
theorem partitionEqual_ordered
    (array : Array T) (pivotIndex : ℕ) (key : T → ℕ)
    (hpivot : pivotIndex < array.size)
    (hlower : KeysGE key array.toList (key array[pivotIndex]!)) :
    let result := partitionEqual array pivotIndex (lessBy key)
    RangeAll result.2 0 result.1
        (fun item => key item = key array[pivotIndex]!) ∧
      RangeAll result.2 result.1 result.2.size
        (fun item => key array[pivotIndex]! < key item) := by
  have hnonempty : 0 < array.size := by omega
  let swapped := swp array 0 pivotIndex
  have hswap : List.Perm swapped.toList array.toList :=
    swp_perm array 0 pivotIndex hnonempty hpivot
  have hswappedSize : swapped.size = array.size := by
    simp [swapped, swp_size]
  have hpivotValue : swapped[0]! = array[pivotIndex]! := by
    simp only [swapped]
    rw [swp_get! array 0 pivotIndex 0 hnonempty hpivot, if_pos rfl]
  let initial : MProd Bool (MProd ℕ (MProd ℕ (Array T))) :=
    ⟨false, 0, swapped.size - 1, swapped⟩
  have hinitial : EqualPartitionStateInvariant key swapped[0]! array initial := by
    refine ⟨⟨?_, ?_, hswap, ?_, ?_, ?_⟩, by simp [initial]⟩
    · simp [initial]
    · simp [initial]
      omega
    · apply KeysGE.perm key hswap.symm
      simpa only [hpivotValue] using hlower
    · intro position hpositionStart hpositionStop
      have hposition : position = 0 := by
        simp only [initial] at hpositionStop
        omega
      subst position
      rfl
    · have hstart : 1 + (swapped.size - 1) = swapped.size := by omega
      rw [hstart]
      exact RangeAll.empty swapped swapped.size _
  let loopResult := partitionEqualLoop
    (List.range (swapped.size + 1)) (List.range swapped.size)
    swapped[0]! (lessBy key) initial
  have hloop : EqualPartitionStateInvariant key swapped[0]! array loopResult := by
    apply partitionEqualLoop_stateInvariant
    · simp [hswappedSize]
    · exact hinitial
  have hdone : loopResult.1 = true := by
    apply partitionEqualLoop_eventually_done
    simpa [initial, Nat.succ_eq_add_one] using
      Nat.sub_lt_succ swapped.size 1
  have hcursors : loopResult.2.1 = loopResult.2.2.1 :=
    hloop.2 hdone
  have hdefinition :
      partitionEqual array pivotIndex (lessBy key) =
        (loopResult.2.1 + 1, loopResult.2.2.2) := by
    simp [partitionEqual, partitionEqualLoop,
      List.range'_eq_map_range, swapped, initial, loopResult]
  clear hinitial hdone
  clear_value loopResult swapped
  rw [hdefinition]
  constructor
  · simpa only [hpivotValue, Nat.add_comm] using hloop.1.2.2.2.2.1
  · rw [hcursors]
    simpa only [hpivotValue, Nat.add_comm] using hloop.1.2.2.2.2.2

private def pivotSort2 (v : Array T) (isLess : T → T → Bool)
    (x y swaps : ℕ) : ℕ × ℕ × ℕ :=
  if isLess (v[y]!) (v[x]!) then
    (y, x, swaps + 1)
  else
    (x, y, swaps)

private def pivotSort3
    (sort2 : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ)
    (x y z swaps : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let (x, y, swaps) := sort2 x y swaps
  let (y, z, swaps) := sort2 y z swaps
  let (x, y, swaps) := sort2 x y swaps
  (x, y, z, swaps)

private def choosePivotCore (v : Array T)
    (sort3 : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) :
    (ℕ × Bool) × Array T := Id.run do
  let len := v.size
  let mut a := len / 4 * 1
  let mut b := len / 4 * 2
  let mut c := len / 4 * 3
  let mut swaps : ℕ := 0
  if len ≥ 8 then
    if len ≥ 50 then
      let (_, ya, _, sw) := sort3 (a - 1) a (a + 1) swaps
      a := ya
      swaps := sw
      let (_, yb, _, sw) := sort3 (b - 1) b (b + 1) swaps
      b := yb
      swaps := sw
      let (_, yc, _, sw) := sort3 (c - 1) c (c + 1) swaps
      c := yc
      swaps := sw
    let (xa, yb, zc, sw) := sort3 a b c swaps
    a := xa
    b := yb
    c := zc
    swaps := sw
  if swaps < 4 * 3 then
    return ((b, decide (swaps == 0)), v)
  else
    return ((len - 1 - b, true), v.reverse)

private theorem choosePivot_eq_core (v : Array T)
    (isLess : T → T → Bool) :
    choosePivot v isLess =
      choosePivotCore v (pivotSort3 (pivotSort2 v isLess)) := by
  rfl

omit [Inhabited T] in
private theorem choosePivotCore_perm (v : Array T)
    (sort3 : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) :
    List.Perm (choosePivotCore v sort3).2.toList v.toList := by
  unfold choosePivotCore
  by_cases h8 : v.size ≥ 8
  · simp only [h8, ↓reduceIte]
    by_cases h50 : v.size ≥ 50
    · simp only [h50, ↓reduceIte]
      generalize sort3 (v.size / 4 * 1 - 1) (v.size / 4 * 1)
          (v.size / 4 * 1 + 1) 0 = ra
      rcases ra with ⟨xa, ya, za, sa⟩
      generalize sort3 (v.size / 4 * 2 - 1) (v.size / 4 * 2)
          (v.size / 4 * 2 + 1) sa = rb
      rcases rb with ⟨xb, yb, zb, sb⟩
      generalize sort3 (v.size / 4 * 3 - 1) (v.size / 4 * 3)
          (v.size / 4 * 3 + 1) sb = rc
      rcases rc with ⟨xc, yc, zc, sc⟩
      generalize sort3 ya yb yc sc = r
      rcases r with ⟨x, y, z, swaps⟩
      split
      · exact List.Perm.refl _
      · change List.Perm v.reverse.toList v.toList
        rw [Array.toList_reverse]
        exact List.reverse_perm _
    · simp only [h50, ↓reduceIte]
      generalize sort3 (v.size / 4 * 1) (v.size / 4 * 2)
          (v.size / 4 * 3) 0 = r
      rcases r with ⟨x, y, z, swaps⟩
      split
      · exact List.Perm.refl _
      · change List.Perm v.reverse.toList v.toList
        rw [Array.toList_reverse]
        exact List.reverse_perm _
  · simp only [h8, ↓reduceIte]
    split
    · exact List.Perm.refl _
    · change List.Perm v.reverse.toList v.toList
      rw [Array.toList_reverse]
      exact List.reverse_perm _

theorem choosePivot_perm (v : Array T)
    (isLess : T → T → Bool) :
    List.Perm (choosePivot v isLess).2.toList v.toList := by
  rw [choosePivot_eq_core]
  exact choosePivotCore_perm v _

private theorem pivotSort2_bounds (v : Array T)
    (isLess : T → T → Bool) (x y swaps : ℕ)
    (hx : x < v.size) (hy : y < v.size) :
    let r := pivotSort2 v isLess x y swaps
    r.1 < v.size ∧ r.2.1 < v.size := by
  unfold pivotSort2
  split <;> simp_all

private theorem pivotSort3_bounds (v : Array T)
    (isLess : T → T → Bool) (x y z swaps : ℕ)
    (hx : x < v.size) (hy : y < v.size) (hz : z < v.size) :
    let r := pivotSort3 (pivotSort2 v isLess) x y z swaps
    r.1 < v.size ∧ r.2.1 < v.size ∧ r.2.2.1 < v.size := by
  unfold pivotSort3
  have hxy := pivotSort2_bounds v isLess x y swaps hx hy
  generalize hxyEq : pivotSort2 v isLess x y swaps = rxy at hxy ⊢
  rcases rxy with ⟨x₁, y₁, swaps₁⟩
  simp only at hxy
  have hyz := pivotSort2_bounds v isLess y₁ z swaps₁ hxy.2 hz
  generalize hyzEq : pivotSort2 v isLess y₁ z swaps₁ = ryz at hyz ⊢
  rcases ryz with ⟨y₂, z₂, swaps₂⟩
  simp only at hyz
  have hxy₂ := pivotSort2_bounds v isLess x₁ y₂ swaps₂ hxy.1 hyz.1
  generalize hxy₂Eq : pivotSort2 v isLess x₁ y₂ swaps₂ = rxy₂ at hxy₂ ⊢
  rcases rxy₂ with ⟨x₃, y₃, swaps₃⟩
  simp only [hyzEq, hxy₂Eq]
  exact ⟨hxy₂.1, hxy₂.2, hyz.2⟩

omit [Inhabited T] in
private theorem choosePivotCore_bound (v : Array T)
    (sort3 : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ)
    (hsort3 : ∀ x y z swaps, x < v.size → y < v.size → z < v.size →
      let r := sort3 x y z swaps
      r.1 < v.size ∧ r.2.1 < v.size ∧ r.2.2.1 < v.size)
    (hsize : 0 < v.size) :
    (choosePivotCore v sort3).1.1 < (choosePivotCore v sort3).2.size := by
  unfold choosePivotCore
  by_cases h8 : v.size ≥ 8
  · simp only [h8, ↓reduceIte]
    by_cases h50 : v.size ≥ 50
    · simp only [h50, ↓reduceIte]
      have ha := hsort3 (v.size / 4 * 1 - 1) (v.size / 4 * 1)
        (v.size / 4 * 1 + 1) 0 (by omega) (by omega) (by omega)
      generalize hra : sort3 (v.size / 4 * 1 - 1) (v.size / 4 * 1)
          (v.size / 4 * 1 + 1) 0 = ra at ha ⊢
      rcases ra with ⟨xa, ya, za, sa⟩
      simp only at ha
      have hb := hsort3 (v.size / 4 * 2 - 1) (v.size / 4 * 2)
        (v.size / 4 * 2 + 1) sa (by omega) (by omega) (by omega)
      generalize hrb : sort3 (v.size / 4 * 2 - 1) (v.size / 4 * 2)
          (v.size / 4 * 2 + 1) sa = rb at hb ⊢
      rcases rb with ⟨xb, yb, zb, sb⟩
      simp only at hb
      have hc := hsort3 (v.size / 4 * 3 - 1) (v.size / 4 * 3)
        (v.size / 4 * 3 + 1) sb (by omega) (by omega) (by omega)
      generalize hrc : sort3 (v.size / 4 * 3 - 1) (v.size / 4 * 3)
          (v.size / 4 * 3 + 1) sb = rc at hc ⊢
      rcases rc with ⟨xc, yc, zc, sc⟩
      simp only at hc
      have hfinal := hsort3 ya yb yc sc ha.2.1 hb.2.1 hc.2.1
      generalize hrf : sort3 ya yb yc sc = r at hfinal ⊢
      rcases r with ⟨x, y, z, swaps⟩
      simp only at hfinal
      split
      · change y < v.size
        exact hfinal.2.1
      · change v.size - 1 - y < v.reverse.size
        simp only [Array.size_reverse]
        omega
    · simp only [h50, ↓reduceIte]
      have hfinal := hsort3 (v.size / 4 * 1) (v.size / 4 * 2)
        (v.size / 4 * 3) 0 (by omega) (by omega) (by omega)
      generalize hrf : sort3 (v.size / 4 * 1) (v.size / 4 * 2)
          (v.size / 4 * 3) 0 = r at hfinal ⊢
      rcases r with ⟨x, y, z, swaps⟩
      simp only at hfinal
      split
      · change y < v.size
        exact hfinal.2.1
      · change v.size - 1 - y < v.reverse.size
        simp only [Array.size_reverse]
        omega
  · simp only [h8, ↓reduceIte]
    split
    · change v.size / 4 * 2 < v.size
      omega
    · omega

theorem choosePivot_bound (v : Array T)
    (isLess : T → T → Bool) (hsize : 0 < v.size) :
    (choosePivot v isLess).1.1 < (choosePivot v isLess).2.size := by
  rw [choosePivot_eq_core]
  exact choosePivotCore_bound v _ (pivotSort3_bounds v isLess) hsize

def PartitionInBlocksCountContract : Prop :=
  ∀ (array : Array T) (pivot : T)
      (isLess : T → T → Bool),
    (partitionInBlocks array pivot isLess).1 ≤ array.size

theorem partitionP_bound_of_blocks_count
    (hblocks : PartitionInBlocksCountContract (T := T))
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    (partitionP array pivotIndex isLess).1.1 <
      (partitionP array pivotIndex isLess).2.size := by
  simp only [partitionP,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, Id.run_bind]
  generalize hscanLeft :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size) 0
      fun _ left =>
        if decide (left < (swp array 0 pivotIndex).size - 1) &&
            isLess
              (swp array 0 pivotIndex)[1 + left]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (left + 1))
        else
          pure (.done left)) = left
  generalize hscanRight :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size)
      ((swp array 0 pivotIndex).size - 1)
      fun _ right =>
        if decide (left < right) &&
            !isLess
              (swp array 0 pivotIndex)[1 + (right - 1)]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (right - 1))
        else
          pure (.done right)) = right
  have hswappedSize :
      (swp array 0 pivotIndex).size = array.size := by
    simp [swp, Array.set!]
  have hrange :=
    partitionP_scan_bounds (swp array 0 pivotIndex) isLess
      (by omega)
  dsimp only at hrange
  rw [hscanLeft, hscanRight] at hrange
  generalize hblock :
    partitionInBlocks
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right))
      (swp array 0 pivotIndex)[0]! isLess = block
  have hcount := hblocks
    ((swp array 0 pivotIndex).extract
      (1 + left) (1 + right))
    (swp array 0 pivotIndex)[0]! isLess
  rw [hblock] at hcount
  have hsourceSize :
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right)).size =
        right - left := by
    simp only [Array.size_extract]
    omega
  have hmid :
      left + block.1 < (swp array 0 pivotIndex).size := by
    change block.1 ≤
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right)).size at hcount
    omega
  change left + block.1 <
    (swp
      (overwrite (swp array 0 pivotIndex) (1 + left) block.2)
      0 (left + block.1)).size
  rw [show
    (swp
      (overwrite (swp array 0 pivotIndex) (1 + left) block.2)
      0 (left + block.1)).size =
      (swp array 0 pivotIndex).size by
        simp [swp, Array.set!, overwrite_size]]
  exact hmid

omit [Inhabited T] in
private theorem array_extract_append_extract
    (a : Array T) (mid : ℕ) (hmid : mid ≤ a.size) :
    (a.extract 0 mid ++ a.extract mid a.size).toList = a.toList := by
  simp [hmid]

omit [Inhabited T] in
private theorem perm_extract_append_extract
    (a : Array T) (mid : ℕ) (hmid : mid ≤ a.size)
    (left' right' : Array T)
    (hleft : List.Perm left'.toList (a.extract 0 mid).toList)
    (hright : List.Perm right'.toList (a.extract mid a.size).toList) :
    List.Perm (left' ++ right').toList a.toList := by
  have heq := array_extract_append_extract a mid hmid
  rw [Array.toList_append] at heq ⊢
  exact (hleft.append hright).trans <|
    heq ▸ List.Perm.refl _

private theorem array_pivot_decomposition
    (a : Array T) (mid : ℕ) (hmid : mid < a.size) :
    (a.extract 0 mid ++ #[a[mid]!] ++ a.extract (mid + 1) a.size).toList =
      a.toList := by
  simp only [Array.toList_append, Array.toList_extract]
  simp only [List.extract, List.drop_zero, Nat.sub_zero]
  have hlen : a.toList.length = a.size := Array.length_toList
  have htail :
      List.take (a.size - (mid + 1)) (List.drop (mid + 1) a.toList) =
        List.drop (mid + 1) a.toList := by
    apply (List.take_eq_self_iff _).2
    simp [hlen]
  rw [htail]
  rw [show a[mid]! = a.toList[mid] by simp [hmid]]
  have hlist : mid < a.toList.length := by simpa [hlen] using hmid
  rw [List.take_concat_get' a.toList mid hlist,
    List.take_append_drop]

private theorem perm_pivot_decomposition
    (a : Array T) (mid : ℕ) (hmid : mid < a.size)
    (left' right' : Array T)
    (hleft : List.Perm left'.toList (a.extract 0 mid).toList)
    (hright : List.Perm right'.toList (a.extract (mid + 1) a.size).toList) :
    List.Perm (left' ++ #[a[mid]!] ++ right').toList a.toList := by
  have heq := array_pivot_decomposition a mid hmid
  simp only [Array.toList_append] at heq ⊢
  exact
    ((hleft.append (List.Perm.refl [a[mid]!])).append hright).trans <|
      heq ▸ List.Perm.refl _

/-- The contracts needed by the recursive pdqsort driver.  This deliberately
mentions only multiset preservation and the bounds needed to split arrays. -/
structure DriverContracts (T : Type) [Inhabited T] where
  insertionSort_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (insertionSort v isLess).toList v.toList
  heapsort_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (heapsort v isLess).toList v.toList
  breakPatterns_perm :
    ∀ (v : Array T), List.Perm (breakPatterns v).toList v.toList
  choosePivot_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (choosePivot v isLess).2.toList v.toList
  choosePivot_bound :
    ∀ (v : Array T) (isLess : T → T → Bool), 0 < v.size →
      (choosePivot v isLess).1.1 < (choosePivot v isLess).2.size
  partialInsertionSort_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (partialInsertionSort v isLess).2.toList v.toList
  partitionEqual_perm :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      List.Perm (partitionEqual v pivot isLess).2.toList v.toList
  partitionEqual_bound :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      let mid := (partitionEqual v pivot isLess).1
      1 ≤ mid ∧ mid ≤ (partitionEqual v pivot isLess).2.size
  partitionP_perm :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      List.Perm (partitionP v pivot isLess).2.toList v.toList
  partitionP_bound :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      (partitionP v pivot isLess).1.1 < (partitionP v pivot isLess).2.size

omit [Inhabited T] in
private theorem size_eq_of_perm {a b : Array T}
    (h : List.Perm a.toList b.toList) : a.size = b.size := by
  simpa using h.length_eq

private theorem partitionEqual_branch_perm
    (contracts : DriverContracts T)
    (v : Array T) (pivot : ℕ) (isLess : T → T → Bool)
    (hpivot : pivot < v.size)
    (tail' : Array T)
    (htail :
      List.Perm tail'.toList
        ((partitionEqual v pivot isLess).2.extract
          (partitionEqual v pivot isLess).1
          (partitionEqual v pivot isLess).2.size).toList) :
    List.Perm
      ((partitionEqual v pivot isLess).2.extract 0
          (partitionEqual v pivot isLess).1 ++ tail').toList
      v.toList := by
  let result := partitionEqual v pivot isLess
  have hbounds := contracts.partitionEqual_bound v pivot isLess hpivot
  have hresult := contracts.partitionEqual_perm v pivot isLess hpivot
  have hassembled :
      List.Perm
        (result.2.extract 0 result.1 ++ tail').toList
        result.2.toList := by
    exact perm_extract_append_extract result.2 result.1 hbounds.2
      _ _ (List.Perm.refl _) htail
  exact hassembled.trans hresult

private theorem partitionP_branch_perm
    (contracts : DriverContracts T)
    (v : Array T) (pivot : ℕ) (isLess : T → T → Bool)
    (hpivot : pivot < v.size)
    (left' right' : Array T)
    (hleft :
      List.Perm left'.toList
        ((partitionP v pivot isLess).2.extract 0
          (partitionP v pivot isLess).1.1).toList)
    (hright :
      List.Perm right'.toList
        ((partitionP v pivot isLess).2.extract
          ((partitionP v pivot isLess).1.1 + 1)
          (partitionP v pivot isLess).2.size).toList) :
    let result := partitionP v pivot isLess
    List.Perm
      (left' ++ #[result.2[result.1.1]!] ++ right').toList
      v.toList := by
  let result := partitionP v pivot isLess
  have hmid := contracts.partitionP_bound v pivot isLess hpivot
  have hresult := contracts.partitionP_perm v pivot isLess hpivot
  have hassembled :
      List.Perm
        (left' ++ #[result.2[result.1.1]!] ++ right').toList
        result.2.toList := by
    exact perm_pivot_decomposition result.2 result.1.1 hmid
      left' right' hleft hright
  exact hassembled.trans hresult

private theorem recursePartition_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len pivot : ℕ) (hpivot : pivot < v.size) :
    List.Perm
      (recursePartition rec v isLess pred limit len pivot).toList
      v.toList := by
  unfold recursePartition
  generalize hresult : partitionP v pivot isLess = result
  rcases result with ⟨⟨mid, wasP⟩, v4⟩
  dsimp only
  have hbranch :=
    partitionP_branch_perm contracts v pivot isLess hpivot
  rw [hresult] at hbranch
  dsimp only at hbranch
  split
  · apply hbranch
    · exact hrec _ _ _ _ _
    · exact hrec _ _ _ _ _
  · apply hbranch
    · exact hrec _ _ _ _ _
    · exact hrec _ _ _ _ _

private theorem recursePred_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (pivot : ℕ) (hpivot : pivot < v.size) :
    List.Perm
      (recursePred rec v isLess pred limit len
        wasBalanced wasPartitioned pivot).toList
      v.toList := by
  cases pred with
  | none =>
      simp only [recursePred]
      exact recursePartition_perm contracts rec hrec
        v isLess none limit len pivot hpivot
  | some p =>
      simp only [recursePred]
      split
      · exact partitionEqual_branch_perm contracts
          v pivot isLess hpivot _
          (hrec _ _ _ _ _)
      · exact recursePartition_perm contracts rec hrec
          v isLess (some p) limit len pivot hpivot

private theorem recurseAfterPivot_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned likelySorted : Bool)
    (pivot : ℕ) (hpivot : pivot < v.size) :
    List.Perm
      (recurseAfterPivot rec v isLess pred limit len
        wasBalanced wasPartitioned likelySorted pivot).toList
      v.toList := by
  cases wasBalanced <;> cases wasPartitioned <;> cases likelySorted
  all_goals
    simp only [recurseAfterPivot, Bool.false_and, Bool.true_and,
      if_true]
  all_goals
    first
    | exact recursePred_perm contracts rec hrec
        v isLess pred limit len _ _ pivot hpivot
    | skip
  generalize hpartial :
    partialInsertionSort v isLess = partialResult
  rcases partialResult with ⟨sorted, v2⟩
  have hpartialPerm :=
    contracts.partialInsertionSort_perm v isLess
  rw [hpartial] at hpartialPerm
  dsimp only at hpartialPerm
  split
  · exact hpartialPerm
  · have hsize : v2.size = v.size :=
      size_eq_of_perm hpartialPerm
    exact
      (recursePred_perm contracts rec hrec
        v2 isLess pred limit len true true
        pivot (by omega)).trans hpartialPerm

private theorem recurseChoose_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < v.size) :
    List.Perm
      (recurseChoose rec v isLess pred limit len
        wasBalanced wasPartitioned).toList
      v.toList := by
  unfold recurseChoose
  generalize hchoose : choosePivot v isLess = result
  rcases result with ⟨⟨pivot, likelySorted⟩, v1⟩
  have hchoosePerm := contracts.choosePivot_perm v isLess
  rw [hchoose] at hchoosePerm
  dsimp only at hchoosePerm
  have hpivot := contracts.choosePivot_bound v isLess hsize
  rw [hchoose] at hpivot
  dsimp only at hpivot
  exact
    (recurseAfterPivot_perm contracts rec hrec
      v1 isLess pred limit len wasBalanced wasPartitioned
      likelySorted pivot hpivot).trans hchoosePerm

private theorem recurseLong_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < v.size) :
    List.Perm
      (recurseLong rec v isLess pred limit len
        wasBalanced wasPartitioned).toList
      v.toList := by
  cases wasBalanced with
  | false =>
      simp only [recurseLong, Bool.not_false, ↓reduceIte]
      have hbreak := contracts.breakPatterns_perm v
      have hbreakSize : 0 < (breakPatterns v).size := by
        have := size_eq_of_perm hbreak
        omega
      exact
        (recurseChoose_perm contracts rec hrec
          (breakPatterns v) isLess pred (limit - 1) len
          false wasPartitioned hbreakSize).trans hbreak
  | true =>
      simp only [recurseLong, Bool.not_true]
      exact recurseChoose_perm contracts rec hrec
        v isLess pred limit len true wasPartitioned hsize

private theorem recurseStep_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit : ℕ) (wasBalanced wasPartitioned : Bool) :
    List.Perm
      (recurseStep rec v isLess pred limit
        wasBalanced wasPartitioned).toList
      v.toList := by
  unfold recurseStep
  by_cases hsmall : v.size ≤ 20
  · simp only [hsmall, ↓reduceIte]
    exact contracts.insertionSort_perm v isLess
  · simp only [hsmall, ↓reduceIte]
    by_cases hlimit : limit == 0
    · simp only [hlimit]
      exact contracts.heapsort_perm v isLess
    · simp only [hlimit]
      exact recurseLong_perm contracts rec hrec
        v isLess pred limit v.size wasBalanced wasPartitioned
        (by omega)

theorem recurse_perm_of_contracts (contracts : DriverContracts T) :
    ∀ (fuel : ℕ) (v : Array T) (isLess : T → T → Bool)
      (pred : Option T) (limit : ℕ) (wasBalanced wasPartitioned : Bool),
      List.Perm
        (recurse fuel v isLess pred limit wasBalanced wasPartitioned).toList
        v.toList := by
  intro fuel
  induction fuel with
  | zero =>
      intro v isLess pred limit wasBalanced wasPartitioned
      exact contracts.heapsort_perm v isLess
  | succ fuel ih =>
      intro v isLess pred limit wasBalanced wasPartitioned
      rw [recurse]
      exact recurseStep_perm contracts
        (fun v pred limit wasBalanced wasPartitioned =>
          recurse fuel v isLess pred limit wasBalanced wasPartitioned)
        (fun v pred limit wasBalanced wasPartitioned =>
          ih v isLess pred limit wasBalanced wasPartitioned)
        v isLess pred limit wasBalanced wasPartitioned

theorem quicksort_perm_of_contracts
    (contracts : DriverContracts T)
    (v : Array T) (isLess : T → T → Bool) :
    List.Perm (quicksort v isLess).toList v.toList := by
  unfold quicksort
  split
  · exact List.Perm.refl _
  · exact recurse_perm_of_contracts contracts
      (v.size + 1) v isLess none
      (Nat.log2 v.size + 1) true true

variable {T : Type} [Inhabited T]

private theorem blocks_count_contract
    (hblocks : PartitionInBlocksPermContract (T := T)) :
    PartitionInBlocksCountContract (T := T) := by
  intro array pivot isLess
  exact (hblocks array pivot isLess).1

def driverContractsOfBlocksContract
    (hblocks : PartitionInBlocksPermContract (T := T)) :
    DriverContracts T where
  insertionSort_perm := insertionSort_perm
  heapsort_perm := heapsort_perm
  breakPatterns_perm := breakPatterns_perm
  choosePivot_perm := choosePivot_perm
  choosePivot_bound := choosePivot_bound
  partialInsertionSort_perm := partialInsertionSort_perm
  partitionEqual_perm := partitionEqual_perm
  partitionEqual_bound := partitionEqual_bound
  partitionP_perm := partitionP_perm_of_blocks_contract hblocks
  partitionP_bound :=
    partitionP_bound_of_blocks_count
      (blocks_count_contract hblocks)

theorem quicksort_perm
    (array : Array T) (isLess : T → T → Bool) :
    List.Perm (quicksort array isLess).toList array.toList :=
  quicksort_perm_of_contracts
    (driverContractsOfBlocksContract partitionInBlocks_perm_contract)
    array isLess

/-! ## Ordering correctness of the recursive driver -/

/-- The predecessor carried by pdqsort is a lower bound for the current
recursive slice. -/
def PredecessorBound
    (key : T → ℕ) (array : Array T) : Option T → Prop
  | none => True
  | some predecessor => KeysGE key array.toList (key predecessor)

omit [Inhabited T] in
theorem PredecessorBound.perm
    (key : T → ℕ) {left right : Array T} {pred : Option T}
    (hperm : left.toList.Perm right.toList)
    (h : PredecessorBound key left pred) :
    PredecessorBound key right pred := by
  cases pred with
  | none => trivial
  | some predecessor =>
      exact KeysGE.perm key hperm h

theorem PredecessorBound.extract
    (key : T → ℕ) (array : Array T) (start stop : ℕ)
    {pred : Option T} (h : PredecessorBound key array pred)
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    PredecessorBound key (array.extract start stop) pred := by
  cases pred with
  | none => trivial
  | some predecessor =>
      exact KeysGE.extract key array start stop (key predecessor)
        h hstart hstop

/-- The two ordering facts not supplied by the recursive partition proof:
heapsort's fallback and the successful nearly-sorted fast path. -/
structure OrderingContracts (T : Type) [Inhabited T] (key : T → ℕ) where
  heapsort_sorted :
    ∀ array, KeySorted key (heapsort array (lessBy key)).toList
  partialInsertionSort_sorted :
    ∀ array, (partialInsertionSort array (lessBy key)).1 = true →
      KeySorted key (partialInsertionSort array (lessBy key)).2.toList

variable {key : T → ℕ}

private def legacyDriverContracts : DriverContracts T :=
  driverContractsOfBlocksContract partitionInBlocks_perm_contract

theorem recurse_perm
    (fuel : ℕ) (array : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit : ℕ)
    (wasBalanced wasPartitioned : Bool) :
    List.Perm
      (recurse fuel array isLess pred limit
        wasBalanced wasPartitioned).toList
      array.toList :=
  recurse_perm_of_contracts legacyDriverContracts
    fuel array isLess pred limit wasBalanced wasPartitioned

private theorem recursePartition_sorted
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len pivot : ℕ)
    (hpivot : pivot < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recursePartition rec array (lessBy key) pred limit len pivot).toList := by
  unfold recursePartition
  generalize hpartition :
    partitionP array pivot (lessBy key) = result
  rcases result with ⟨⟨middle, wasPartitioned⟩, partitioned⟩
  dsimp only
  have hpartitionPerm :=
    legacyDriverContracts.partitionP_perm array pivot (lessBy key) hpivot
  have hmiddle :=
    legacyDriverContracts.partitionP_bound array pivot (lessBy key) hpivot
  have hpartitionOrder :=
    partitionP_order array pivot (lessBy key) hpivot
  rw [hpartition] at hpartitionPerm hmiddle hpartitionOrder
  dsimp only at hpartitionPerm hmiddle hpartitionOrder
  let pivotValue := partitioned[middle]!
  let left := partitioned.extract 0 middle
  let right := partitioned.extract (middle + 1) partitioned.size
  have hleftRange : RangeAll partitioned 0 middle
      (fun item => key item ≤ key pivotValue) := by
    intro index hstart hstop
    have hless := hpartitionOrder.1 index hstart hstop
    change lessBy key partitioned[index]! partitioned[middle]! = true at hless
    rw [lessBy_eq_true_iff] at hless
    simpa only [pivotValue] using hless.le
  have hrightRange : RangeAll partitioned (middle + 1) partitioned.size
      (fun item => key pivotValue ≤ key item) := by
    intro index hstart hstop
    have hnotLess := hpartitionOrder.2 index hstart hstop
    change lessBy key partitioned[index]! partitioned[middle]! = false at hnotLess
    rw [lessBy_eq_false_iff] at hnotLess
    simpa only [pivotValue] using hnotLess
  have hleftBound : KeysLE key left.toList (key pivotValue) := by
    apply RangeAll.keysLE_extract key partitioned 0 middle
      (key pivotValue) hleftRange <;> omega
  have hrightBound : KeysGE key right.toList (key pivotValue) := by
    apply RangeAll.keysGE_extract key partitioned (middle + 1)
      partitioned.size (key pivotValue) hrightRange <;> omega
  have hpartitionedLower : PredecessorBound key partitioned pred :=
    PredecessorBound.perm key hpartitionPerm.symm hlower
  have hleftLower : PredecessorBound key left pred := by
    apply PredecessorBound.extract key partitioned 0 middle
      hpartitionedLower <;> omega
  have hleftSorted := hrecSorted left pred limit true true hleftLower
  have hrightSorted (balanced partitionedFlag : Bool) :=
    hrecSorted right (some pivotValue) limit balanced partitionedFlag hrightBound
  have hleftOutputBound (balanced partitionedFlag : Bool) :
      KeysLE key
        (rec left pred limit balanced partitionedFlag).toList
        (key pivotValue) :=
    KeysLE.perm key
      (hrecPerm left pred limit balanced partitionedFlag).symm
      hleftBound
  have hrightOutputBound (balanced partitionedFlag : Bool) :
      KeysGE key
        (rec right (some pivotValue) limit balanced partitionedFlag).toList
        (key pivotValue) :=
    KeysGE.perm key
      (hrecPerm right (some pivotValue) limit balanced partitionedFlag).symm
      hrightBound
  split
  · simp only [Array.toList_append, List.append_assoc]
    exact KeySorted.append_pivot key _ pivotValue _
      hleftSorted (hrightSorted _ _)
      (hleftOutputBound _ _) (hrightOutputBound _ _)
  · simp only [Array.toList_append, List.append_assoc]
    exact KeySorted.append_pivot key _ pivotValue _
      (hrecSorted left pred limit _ _ hleftLower)
      (hrightSorted true true)
      (hleftOutputBound _ _) (hrightOutputBound true true)

private theorem recursePred_sorted
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) (pivot : ℕ)
    (hpivot : pivot < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recursePred rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned pivot).toList := by
  cases pred with
  | none =>
      simp only [recursePred]
      exact recursePartition_sorted rec hrecSorted hrecPerm
        array none limit len pivot hpivot hlower
  | some predecessor =>
      simp only [recursePred]
      split
      next hfast =>
        have hpivotLower : key predecessor ≤ key array[pivot]! :=
          KeysGE.get! key array (key predecessor) pivot hlower hpivot
        have hpivotUpper : key array[pivot]! ≤ key predecessor := by
          change (!lessBy key predecessor array[pivot]!) = true at hfast
          cases hcomparison : lessBy key predecessor array[pivot]! with
          | false =>
              rw [lessBy_eq_false_iff] at hcomparison
              exact hcomparison
          | true => simp_all
        have hpivotKey : key array[pivot]! = key predecessor := by omega
        have hpartitionOrder := partitionEqual_ordered
          array pivot key hpivot (by
            intro item hitem
            rw [hpivotKey]
            exact hlower item hitem)
        have hpartitionPerm :=
          legacyDriverContracts.partitionEqual_perm
            array pivot (lessBy key) hpivot
        have hpartitionBounds :=
          legacyDriverContracts.partitionEqual_bound
            array pivot (lessBy key) hpivot
        generalize hpartition :
          partitionEqual array pivot (lessBy key) = result
        rcases result with ⟨middle, partitioned⟩
        rw [hpartition] at hpartitionOrder hpartitionPerm hpartitionBounds
        dsimp only at hpartitionOrder hpartitionPerm hpartitionBounds ⊢
        let head := partitioned.extract 0 middle
        let tail := partitioned.extract middle partitioned.size
        have hheadEqual : ∀ item ∈ head.toList,
            key item = key predecessor := by
          intro item hitem
          have hmember := hpartitionOrder.1.forall_mem_extract
            (by omega) (by omega) item hitem
          exact hmember.trans hpivotKey
        have hheadSorted : KeySorted key head.toList :=
          KeySorted.of_constant key head.toList (key predecessor) hheadEqual
        have hheadBound : KeysLE key head.toList (key predecessor) := by
          intro item hitem
          exact (hheadEqual item hitem).le
        have htailBound : KeysGE key tail.toList (key predecessor) := by
          apply RangeAll.keysGE_extract key partitioned middle
            partitioned.size (key predecessor) _ (by omega) (by omega)
          intro index hstart hstop
          have hgreater := hpartitionOrder.2 index hstart hstop
          omega
        have htailSorted := hrecSorted tail (some predecessor) limit
          wasBalanced wasPartitioned htailBound
        have htailOutputBound : KeysGE key
            (rec tail (some predecessor) limit
              wasBalanced wasPartitioned).toList
            (key predecessor) :=
          KeysGE.perm key
            (hrecPerm tail (some predecessor) limit
              wasBalanced wasPartitioned).symm htailBound
        simp only [Array.toList_append]
        exact KeySorted.append key head.toList _ hheadSorted htailSorted (by
          intro leftItem hleftItem rightItem hrightItem
          exact (hheadBound leftItem hleftItem).trans
            (htailOutputBound rightItem hrightItem))
      next _ =>
        exact recursePartition_sorted rec hrecSorted hrecPerm
          array (some predecessor) limit len pivot hpivot hlower

private theorem recurseAfterPivot_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned likelySorted : Bool) (pivot : ℕ)
    (hpivot : pivot < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseAfterPivot rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned likelySorted pivot).toList := by
  cases wasBalanced <;> cases wasPartitioned <;> cases likelySorted
  all_goals
    simp only [recurseAfterPivot, Bool.false_and, Bool.true_and,
      if_true]
  all_goals
    first
    | exact recursePred_sorted rec hrecSorted hrecPerm
        array pred limit len _ _ pivot hpivot hlower
    | skip
  generalize hpartial :
    partialInsertionSort array (lessBy key) = partialResult
  rcases partialResult with ⟨sorted, partiallySorted⟩
  split
  next hsorted =>
    have hresult := contracts.partialInsertionSort_sorted array
    rw [hpartial] at hresult
    exact hresult hsorted
  next _ =>
    have hpartialPerm :=
      legacyDriverContracts.partialInsertionSort_perm
        array (lessBy key)
    rw [hpartial] at hpartialPerm
    dsimp only at hpartialPerm
    have hpartialLower :
        PredecessorBound key partiallySorted pred :=
      PredecessorBound.perm key hpartialPerm.symm hlower
    have hpartialSize : partiallySorted.size = array.size :=
      size_eq_of_perm hpartialPerm
    exact recursePred_sorted rec hrecSorted hrecPerm
      partiallySorted pred limit len true true pivot
      (by omega) hpartialLower

private theorem recurseChoose_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseChoose rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned).toList := by
  unfold recurseChoose
  generalize hchoose : choosePivot array (lessBy key) = result
  rcases result with ⟨⟨pivot, likelySorted⟩, chosen⟩
  have hchoosePerm :=
    legacyDriverContracts.choosePivot_perm array (lessBy key)
  have hpivot :=
    legacyDriverContracts.choosePivot_bound array (lessBy key) hsize
  rw [hchoose] at hchoosePerm hpivot
  dsimp only at hchoosePerm hpivot ⊢
  have hchosenLower : PredecessorBound key chosen pred :=
    PredecessorBound.perm key hchoosePerm.symm hlower
  exact recurseAfterPivot_sorted contracts rec hrecSorted hrecPerm
    chosen pred limit len wasBalanced wasPartitioned likelySorted pivot
    hpivot hchosenLower

private theorem recurseLong_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseLong rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned).toList := by
  cases wasBalanced with
  | false =>
      simp only [recurseLong, Bool.not_false, ↓reduceIte]
      have hbreak := legacyDriverContracts.breakPatterns_perm array
      have hbreakSize : 0 < (breakPatterns array).size := by
        have := size_eq_of_perm hbreak
        omega
      have hbreakLower :
          PredecessorBound key (breakPatterns array) pred :=
        PredecessorBound.perm key hbreak.symm hlower
      exact recurseChoose_sorted contracts rec hrecSorted hrecPerm
        (breakPatterns array) pred (limit - 1) len false wasPartitioned
        hbreakSize hbreakLower
  | true =>
      simp only [recurseLong, Bool.not_true]
      exact recurseChoose_sorted contracts rec hrecSorted hrecPerm
        array pred limit len true wasPartitioned hsize hlower

private theorem recurseStep_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit : ℕ)
    (wasBalanced wasPartitioned : Bool)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseStep rec array (lessBy key) pred limit
        wasBalanced wasPartitioned).toList := by
  unfold recurseStep
  by_cases hsmall : array.size ≤ 20
  · simp only [hsmall, ↓reduceIte]
    exact insertionSort_sorted array key
  · simp only [hsmall, ↓reduceIte]
    by_cases hlimit : limit == 0
    · simp only [hlimit]
      exact contracts.heapsort_sorted array
    · simp only [hlimit]
      exact recurseLong_sorted contracts rec hrecSorted hrecPerm
        array pred limit array.size wasBalanced wasPartitioned
        (by omega) hlower

theorem recurse_sorted_of_contracts
    (contracts : OrderingContracts T key) :
    ∀ (fuel : ℕ) (array : Array T) (pred : Option T) (limit : ℕ)
      (wasBalanced wasPartitioned : Bool),
      PredecessorBound key array pred →
      KeySorted key
        (recurse fuel array (lessBy key) pred limit
          wasBalanced wasPartitioned).toList := by
  intro fuel
  induction fuel with
  | zero =>
      intro array pred limit wasBalanced wasPartitioned hlower
      exact contracts.heapsort_sorted array
  | succ fuel inductionHypothesis =>
      intro array pred limit wasBalanced wasPartitioned hlower
      rw [recurse]
      exact recurseStep_sorted contracts
        (fun array pred limit wasBalanced wasPartitioned =>
          recurse fuel array (lessBy key) pred limit
            wasBalanced wasPartitioned)
        (fun array pred limit wasBalanced wasPartitioned =>
          inductionHypothesis array pred limit
            wasBalanced wasPartitioned)
        (fun array pred limit wasBalanced wasPartitioned =>
          recurse_perm fuel array (lessBy key) pred limit
            wasBalanced wasPartitioned)
        array pred limit wasBalanced wasPartitioned hlower

theorem quicksort_sorted_of_contracts
    (contracts : OrderingContracts T key) (array : Array T) :
    KeySorted key (quicksort array (lessBy key)).toList := by
  unfold quicksort
  split
  next hzero =>
    have hsize : array.size = 0 := by simpa using hzero
    have hempty : array.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hsize
    rw [hempty]
    exact KeySorted.nil key
  next _ =>
    exact recurse_sorted_of_contracts contracts
      (array.size + 1) array none (Nat.log2 array.size + 1)
      true true trivial

end Pdqsort

end Halo2.FloorPlanner
