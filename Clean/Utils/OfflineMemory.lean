import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Primes
import Clean.Utils.Tactics
import Mathlib.Data.List.Sort

/-
The purpose of this file is to define a memory model that can be checked using the Memory in the Head paradigm,
often also called "offline memory checking". [Blu+91]

This file roughly aims to prove the following theorem.

Given an ordered list of memory accesses (timestamp, address, readValue, writeValue), where at each access,
we read the current value at the address, and then write a new value to the address, considering that
the initial memory is all zero, then checking the consistency of the memory accesses is equivalent to checking
the following decision procedure:
there exists a permutation of the original list, such that it is sorted first by address and then by timestamp,
 and such that the following property holds for each pair of consecutive elements of this array
  (t2, addr2, readValue2, writeValue2) :: (t1, addr1, readValue1, writeValue1) :: rest
if addr1 = addr2, then readValue2 = writeValue1, and if addr1 ≠ addr2, then readValue2 = 0.
Additionally, the first value of the array (t, addr, readValue, writeValue) must have readValue = 0.


[Blu+91] Manuel Blum et al. "Checking the correctness of memories"
-/

/--
  A memory access consists of an address, a read value, and a write value.
  The semantics are that at this address, we read the readValue, and then write the writeValue.
-/
def MemoryAccess := ℕ × ℕ × ℕ × ℕ -- (timestamp, addr, readValue, writeValue)

/--
A memory list is canonically represented in reverse order, so that the most recent access is at the head of the list.
-/
def MemoryAccessList := List MemoryAccess

/--
  A memory access list is timestamp sorted if the timestamps are strictly decreasing.
-/
def MemoryAccessList.isTimestampSorted (accesses : MemoryAccessList) : Prop :=
  accesses.Sorted (fun (t2, _, _, _) (t1, _, _, _) => t1 < t2)


def TimestampSortedMemoryAccessList := {accesses : MemoryAccessList // accesses.isTimestampSorted}

/--
  A memory access list is address sorted if the addresses are sorted, and for equal addresses,
  the timestamps are strictly decreasing.
-/
def MemoryAccessList.isAddressTimestampSorted (accesses : MemoryAccessList) : Prop :=
  accesses.Sorted (fun (t2, addr2, _, _) (t1, addr1, _, _) => if addr1 = addr2 then t1 < t2 else addr1 < addr2)

def AddressSortedMemoryAccessList := {accesses : MemoryAccessList // accesses.isAddressTimestampSorted}

def MemoryAccessList.lastWriteValue (accesses : MemoryAccessList) (h : accesses.isTimestampSorted) (addr : ℕ) : ℕ := match accesses with
  -- initially the memory is all zero
  | [] => 0
  | (_t, addr', _readValue, writeValue) :: rest =>
    if addr' = addr then
      -- since the list is timestamp sorted, the first operation we find for this address is the most recent one
      writeValue
    else
      MemoryAccessList.lastWriteValue rest (List.Sorted.of_cons h) addr

-- now, we need a way to express that the memory access list is consistent
def MemoryAccessList.isConsistentOnline (accesses : MemoryAccessList) (h : accesses.isTimestampSorted) : Prop := match accesses with
  | [] => True -- no memory access is trivially consistent
  | (_timestamp, addr, readValue, _writeValue) :: rest =>
    -- here we need to check that the readValue is consistent with the previous writes to the same address
    readValue = MemoryAccessList.lastWriteValue rest (List.Sorted.of_cons h) addr
    ∧ MemoryAccessList.isConsistentOnline rest (List.Sorted.of_cons h)


example : MemoryAccessList.isConsistentOnline [] (by simp [MemoryAccessList.isTimestampSorted]) := by trivial

example : MemoryAccessList.isConsistentOnline [
  (0, 0, 0, 42),
  (1, 1, 0, 43),
  (2, 0, 42, 44),
  (3, 2, 0, 45),
  (4, 1, 43, 46)
].reverse (by simp [MemoryAccessList.isTimestampSorted]):= by
  simp_all [MemoryAccessList.isConsistentOnline, MemoryAccessList.lastWriteValue]

example : ¬ MemoryAccessList.isConsistentOnline [
  (0, 0, 0, 42),
  (1, 1, 0, 43),
  (2, 0, 43, 44), -- inconsistent read
  (3, 2, 0, 45),
  (4, 1, 43, 46)
].reverse (by simp [MemoryAccessList.isTimestampSorted]):= by
  simp_all [MemoryAccessList.isConsistentOnline, MemoryAccessList.lastWriteValue]

/--
  Filter a memory access list to only include accesses to a specific address.
-/
def MemoryAccessList.filterAddress (accesses : MemoryAccessList) (addr : ℕ) : MemoryAccessList :=
  accesses.filter (fun (_timestamp, addr', _readValue, _writeValue) => addr' = addr)


#eval MemoryAccessList.filterAddress [
  (0, 0, 0, 42),
  (1, 1, 0, 43),
  (2, 0, 42, 44),
  (3, 2, 0, 45),
  (4, 1, 43, 46)
].reverse 0

/--
  A filtered sorted memory access list is sorted as well.
-/
theorem MemoryAccessList.filterAddress_sorted (accesses : MemoryAccessList)
    (h : accesses.isTimestampSorted) (addr : ℕ) :
    (MemoryAccessList.filterAddress accesses addr).isTimestampSorted := by
  simp only [isTimestampSorted]
  apply List.Sorted.filter
  exact h

theorem MemoryAccessList.filterAddress_cons (head : MemoryAccess) (tail : MemoryAccessList) (addr : ℕ) :
    MemoryAccessList.filterAddress (head :: tail) addr =
    match head with
    | ⟨_t, a, _r, _w⟩ => ((if a = addr then
      (head :: (MemoryAccessList.filterAddress tail addr))
        else (MemoryAccessList.filterAddress tail addr))) := by
  obtain ⟨_t, a, _r, _w⟩ := head
  simp [filterAddress, List.filter_cons]

/--
  A memory access list is consistent for a single address if the reads and writes to that address are consistent.
  This variant of the consistency check is simpler, and holds only when the array contains only accesses to a single address.
  This function checks the following:
  - the first memory access must read 0
  - for each pair of consecutive accesses, the read of the most recent access must equal the write of the previous access
-/
def MemoryAccessList.isConsistentSingleAddress (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) : Prop := match accesses with
  -- no memory access is trivially consistent
  | [] => True
  -- if there's only one access, the read must be zero
  | (_timestamp, _addr, readValue, _writeValue) :: [] => readValue = 0
  -- if there are multiple accesses, the read of the most recent access must equal the write of the previous access
  | (_t2, _addr2, readValue2, _writeValue2) :: (t1, addr1, readValue1, writeValue1) :: rest =>
    readValue2 = writeValue1 ∧
    MemoryAccessList.isConsistentSingleAddress ((t1, addr1, readValue1, writeValue1) :: rest) (List.Sorted.of_cons h_sorted)

/--
  If a memory access list contains only accesses to a single address, then the following two consistency are equivalent:
  - the online consistency check
  - the single address consistency check
-/
theorem MemoryAccessList.isConsistentSingleAddress_iff (accesses : MemoryAccessList) (addr : ℕ) (h_sorted : accesses.isTimestampSorted)
    (h_eq : accesses.all (fun (_t, addr', _readValue, _writeValue) => addr' = addr)) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    MemoryAccessList.isConsistentSingleAddress accesses h_sorted := by
  induction accesses with
  | nil => simp only [isConsistentOnline, isConsistentSingleAddress]
  | cons head tail ih =>
    constructor
    · intro h
      cases tail with
      | nil =>
        obtain ⟨t, a, r, w⟩ := head
        simp_all only [List.all_nil, isConsistentOnline, isConsistentSingleAddress, imp_self,
          implies_true, List.all_cons, Bool.and_true, decide_eq_true_eq, lastWriteValue, and_true]
      | cons head2 tail2 =>
        obtain ⟨t2, a2, r2, w2⟩ := head
        obtain ⟨t1, a1, r1, w1⟩ := head2
        simp [isConsistentOnline, isConsistentSingleAddress, lastWriteValue] at ⊢ h h_eq ih
        have h_sorted' : isTimestampSorted ((t1, a1, r1, w1) :: tail2) := by
          unfold isTimestampSorted at h_sorted
          exact List.Sorted.of_cons h_sorted
        obtain ⟨h_eq1, h_eq2, h_eq3⟩ := h_eq
        specialize ih h_sorted' h_eq2 h_eq3
        rw [←ih]
        simp_all only [↓reduceIte, and_self, true_iff]
    · intro h
      cases tail with
      | nil =>
        obtain ⟨t, a, r, w⟩ := head
        simp_all only [List.all_nil, isConsistentOnline, isConsistentSingleAddress, imp_self,
          implies_true, List.all_cons, Bool.and_true, decide_eq_true_eq, lastWriteValue, and_true]
      | cons head2 tail2 =>
        obtain ⟨t2, a2, r2, w2⟩ := head
        obtain ⟨t1, a1, r1, w1⟩ := head2
        simp [isConsistentOnline, isConsistentSingleAddress, lastWriteValue] at ⊢ h h_eq ih
        have h_sorted' : isTimestampSorted ((t1, a1, r1, w1) :: tail2) := by
          unfold isTimestampSorted at h_sorted
          exact List.Sorted.of_cons h_sorted
        obtain ⟨h_eq1, h_eq2, h_eq3⟩ := h_eq
        specialize ih h_sorted' h_eq2 h_eq3
        rw [ih]
        simp_all only [↓reduceIte, and_self]

/--
  The last write value for a specific address is the same whether we compute it on the full list
  or on the filtered list on that address.
-/
theorem MemoryAccessList.lastWriteValue_filter (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted) (addr : ℕ) (h_sorted' : ((MemoryAccessList.filterAddress accesses addr).isTimestampSorted))  :
    MemoryAccessList.lastWriteValue accesses h_sorted addr =
    MemoryAccessList.lastWriteValue (MemoryAccessList.filterAddress accesses addr) h_sorted' addr := by
  induction accesses with
  | nil =>
    simp only [filterAddress, List.filter_nil, lastWriteValue]
  | cons head tail ih =>
    obtain ⟨t, a, r, w⟩ := head
    simp [filterAddress, List.filter_cons, lastWriteValue] at ⊢ ih
    -- is the current address the one we are filtering for?
    by_cases h_addr : a = addr
    · simp_all only [↓reduceIte, lastWriteValue]
    · have h_sorted_tail : isTimestampSorted tail := by
        unfold isTimestampSorted at h_sorted
        exact List.Sorted.of_cons h_sorted
      have h_sorted_tail' : (MemoryAccessList.filterAddress tail addr).isTimestampSorted := by
        simp only [filterAddress]
        apply List.Sorted.filter
        exact h_sorted_tail
      specialize ih h_sorted_tail h_sorted_tail'
      simp only [h_addr, ↓reduceIte, ih]


/--
  If a memory access list is online consistent, then the filtered list for a specific address is
  online consistent as well.
-/
theorem MemoryAccessList.isConsistentOnline_filter_of_consistentOnline (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted)
    (h_consistent : MemoryAccessList.isConsistentOnline accesses h_sorted) (addr : ℕ) :
    MemoryAccessList.isConsistentOnline (MemoryAccessList.filterAddress accesses addr) (MemoryAccessList.filterAddress_sorted accesses h_sorted addr) := by
  induction accesses with
  | nil =>
    simp only [filterAddress, List.filter_nil, isConsistentOnline]
  | cons head tail ih =>
    obtain ⟨t, a, r, w⟩ := head
    simp [filterAddress, List.filter_cons, isConsistentOnline] at ⊢ h_consistent ih
    have h_sorted' : isTimestampSorted tail := by
      unfold isTimestampSorted at h_sorted
      exact List.Sorted.of_cons h_sorted
    -- is the current address the one we are filtering for?
    by_cases h_addr : a = addr
    ·
      specialize ih h_sorted' (And.right h_consistent)
      simp [h_addr, isConsistentOnline, ih]
      have h := MemoryAccessList.lastWriteValue_filter
      simp [h_consistent.left]
      rw [MemoryAccessList.lastWriteValue_filter]
      · simp [filterAddress, h_addr]
      · have h_sorted_tail' : (MemoryAccessList.filterAddress tail addr).isTimestampSorted := by
          simp only [filterAddress]
          apply List.Sorted.filter
          exact h_sorted'
        rw [h_addr]
        exact h_sorted_tail'
    · simp_all only [forall_const, forall_true_left, ↓reduceIte]

theorem MemoryAccessList.isTimestampSorted_cons (head : MemoryAccess) (tail : MemoryAccessList) :
    isTimestampSorted (head :: tail) → isTimestampSorted tail := by
  simp_all only [isTimestampSorted, List.sorted_cons, implies_true]

theorem MemoryAccessList.isConsistentSingleAddress_cons (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : isTimestampSorted (head :: tail)) (h_sorted' : tail.isTimestampSorted)
    (h : isConsistentSingleAddress (head :: tail) h_sorted) :
    isConsistentSingleAddress tail h_sorted' := by
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  cases tail with
  | nil =>
    simp_all [isConsistentSingleAddress]
  | cons head2 tail2 =>
    obtain ⟨t1, a1, r1, w1⟩ := head2
    simp_all [isConsistentSingleAddress]

theorem MemoryAccessList.isConsistentSingleAddress_cons_forall (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : isTimestampSorted (head :: tail))
    : (∀ addr : ℕ, (filterAddress (head :: tail) addr).isConsistentSingleAddress (MemoryAccessList.filterAddress_sorted (head :: tail) h_sorted addr)) →
    (∀ addr : ℕ, isConsistentSingleAddress (filterAddress tail addr) (MemoryAccessList.filterAddress_sorted tail (by simp_all only [isTimestampSorted,
      List.sorted_cons]) addr)) := by
  intro h addr'
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  simp_all [MemoryAccessList.filterAddress_cons]
  specialize h addr'
  by_cases h_addr : a_head = addr'
  · sorry
  · sorry

/--
  A memory access list is consistent if and only if, for each possible address, considering
  only the accesses to that address, the single address consistency check holds.
-/
theorem MemoryAccessList.isConsistent_iff_all_single_address (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    (∀ addr : ℕ, MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress accesses addr) (MemoryAccessList.filterAddress_sorted accesses h_sorted addr)) := by
  constructor
  · intro h addr
    have h' := MemoryAccessList.isConsistentSingleAddress_iff (accesses.filterAddress addr) addr (MemoryAccessList.filterAddress_sorted accesses h_sorted addr)
        (by simp only [filterAddress, List.all_filter, Bool.not_or_self, List.all_eq_true,
          implies_true])
    exact h'.mp (MemoryAccessList.isConsistentOnline_filter_of_consistentOnline accesses h_sorted h addr)
  · intro h

    -- by induction on the list of accesses
    induction accesses with
    | nil =>
      simp [isConsistentOnline]
    | cons head tail ih =>
      obtain ⟨t, a, r, w⟩ := head
      have h_sorted' : isTimestampSorted tail := by
        unfold isTimestampSorted at h_sorted
        exact List.Sorted.of_cons h_sorted
      specialize ih h_sorted'
      have h_tail := MemoryAccessList.isConsistentSingleAddress_cons (t, a, r, w) tail h_sorted h
      specialize ih h_tail
      simp only [isConsistentOnline, ih, and_true]
      specialize h a
      rw [← MemoryAccessList.isConsistentSingleAddress_iff _ a _ (by simp [filterAddress])] at h
      simp [filterAddress_cons, isConsistentOnline] at h
      simp [h.left]
      rw [←MemoryAccessList.lastWriteValue_filter]

/--
  Offline version of memory consistency checking.
-/
def MemoryAccessList.isConsistentOffline (accesses : MemoryAccessList) (h_sorted : accesses.isAddressTimestampSorted) : Prop := match accesses with
  | [] => True -- no memory access is trivially consistent
  | (_timestamp, _addr, readValue, _writeValue) :: [] => readValue = 0
  | (_t2, addr2, readValue2, _writeValue2) :: (t1, addr1, readValue1, writeValue1) :: rest =>
    (if addr1 = addr2 then readValue2 = writeValue1 else readValue2 = 0) ∧
    MemoryAccessList.isConsistentOffline ((t1, addr1, readValue1, writeValue1) :: rest) (List.Sorted.of_cons h_sorted)


/--
  This is the main theorem of this file.

  A list of timestamp-sorted memory accesses is consistent if and only if there exists a permutation of the list
  that is address-sorted, and such that the offline consistency check holds.
-/
theorem MemoryAccessList.isConsistentOnline_iff_isConsistentOffline (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    ∃ permuted : AddressSortedMemoryAccessList,
      permuted.val.Perm accesses ∧
      MemoryAccessList.isConsistentOffline permuted.val permuted.property := by
  sorry
