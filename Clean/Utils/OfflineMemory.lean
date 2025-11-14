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

abbrev timestamp_ordering (x y : MemoryAccess) := match x, y with
| (t2, _a2, _r2, _w2), (t1, _a1, _r1, _w1) => t1 < t2

/--
  A memory access list is timestamp sorted if the timestamps are strictly decreasing.
-/
def MemoryAccessList.isTimestampSorted (accesses : MemoryAccessList) : Prop :=
  accesses.Sorted timestamp_ordering

def TimestampSortedMemoryAccessList := {accesses : MemoryAccessList // accesses.isTimestampSorted}

def MemoryAccessList.timestamps_neq (x y: MemoryAccess) : Prop :=
  match x, y with
  | (t_x, _a_x, _r_x, _w_x), (t_y, _a_y, _r_y, _w_y) => t_x ≠ t_y

def MemoryAccessList.Notimestampdup (accesses : MemoryAccessList) : Prop :=
  List.Pairwise timestamps_neq accesses

abbrev address_timestamp_ordering (x y : MemoryAccess) := match x, y with
| (t2, a2, _, _), (t1, a1, _, _) => if a1 = a2 then t1 ≤ t2 else a1 < a2

/--
  A strict version of the address-timestamp ordering, where timestamps are strictly decreasing
  for equal addresses. This relation is not used for sorting, as it is not total.
  However, if the input list is timestamp strictly sorted, then the address-timestamp sorted
  list is also address-strict-timestamp sorted.
-/
abbrev address_strict_timestamp_ordering (x y : MemoryAccess) := match x, y with
| (t2, a2, _, _), (t1, a1, _, _) => if a1 = a2 then t1 < t2 else a1 < a2

instance (x y : MemoryAccess) : Decidable (address_timestamp_ordering x y) := by
  obtain ⟨t2, a2, _r2, _w2⟩ := x
  obtain ⟨t1, a1, _r1, _w1⟩ := y
  simp only [address_timestamp_ordering]
  split
  · apply Nat.decLe
  · apply Nat.decLt

instance : IsTrans MemoryAccess address_timestamp_ordering := by
  constructor
  intros a b c hab hbc
  obtain ⟨t_a, a_a, _r_a, _w_a⟩ := a
  obtain ⟨t_b, a_b, _r_b, _w_b⟩ := b
  obtain ⟨t_c, a_c, _r_c, _w_c⟩ := c
  simp only [address_timestamp_ordering] at hab hbc ⊢
  split
  · by_cases h : a_a = a_b
    · simp_all only [↓reduceIte]
      linarith
    · simp_all only [↓reduceIte]
      rw [eq_comm] at h
      simp only [h, ↓reduceIte] at hab
      linarith
  · by_cases h : a_b = a_c
    · simp_all only [↓reduceIte]
    · by_cases h' : a_a = a_b
      · simp_all only [↓reduceIte]
      · rw [eq_comm] at h'
        simp only [h', ↓reduceIte] at hab
        rw [eq_comm] at h
        simp only [h, ↓reduceIte] at hbc
        linarith

instance : IsTotal MemoryAccess address_timestamp_ordering := by
  constructor
  intros a b
  obtain ⟨t_a, a_a, _r_a, _w_a⟩ := a
  obtain ⟨t_b, a_b, _r_b, _w_b⟩ := b
  simp only [address_timestamp_ordering]
  by_cases h : a_a = a_b
  · simp_all only [↓reduceIte]
    apply Nat.le_total
  · simp_all only [↓reduceIte]
    rw [eq_comm] at h
    simp only [h, ↓reduceIte]
    apply Nat.lt_or_lt_of_ne (by simp only [ne_eq, h, not_false_eq_true])

instance : IsAntisymm MemoryAccess timestamp_ordering := by
  constructor
  intros a b hab hba
  obtain ⟨t_a, a_a, _r_a, _w_a⟩ := a
  obtain ⟨t_b, a_b, _r_b, _w_b⟩ := b
  simp only [timestamp_ordering] at hab hba
  linarith

instance : IsIrrefl MemoryAccess timestamp_ordering := by
  constructor
  intros a ha
  obtain ⟨t_a, a_a, _r_a, _w_a⟩ := a
  simp only [timestamp_ordering] at ha
  linarith

instance : IsIrrefl MemoryAccess address_strict_timestamp_ordering := by
  constructor
  intros a ha
  obtain ⟨t_a, a_a, _r_a, _w_a⟩ := a
  simp only [address_strict_timestamp_ordering] at ha
  split_ifs at ha
  · linarith
  · linarith

instance : IsAntisymm MemoryAccess address_strict_timestamp_ordering := by
  constructor
  intros a b hab hba
  obtain ⟨t_a, a_a, _r_a, _w_a⟩ := a
  obtain ⟨t_b, a_b, _r_b, _w_b⟩ := b
  simp only [address_strict_timestamp_ordering] at hab hba
  split_ifs at hab hba
  · linarith
  · linarith
  · linarith
  · linarith

instance {x y : MemoryAccess} : Decidable (address_strict_timestamp_ordering x y) := by
  obtain ⟨t2, a2, _r2, _w2⟩ := x
  obtain ⟨t1, a1, _r1, _w1⟩ := y
  simp only [address_strict_timestamp_ordering]
  split
  · by_cases h : a1 = a2
    · simp_all only
      apply Nat.decLt
    · simp_all only
  · by_cases h : a1 = a2
    · simp_all only
      apply Nat.decLt
    · simp_all only
      apply Nat.decLt

/--
  A memory access list is address sorted if the addresses are sorted, and for equal addresses,
  the timestamps are decreasing.
-/
@[reducible]
def MemoryAccessList.isAddressTimestampSorted (accesses : MemoryAccessList) : Prop :=
  accesses.Sorted address_timestamp_ordering

/--
  A memory access list is strictly address-timestamp sorted if the addresses are sorted, and for
  equal addresses, the timestamps are strictly decreasing.
-/
@[reducible]
def MemoryAccessList.isAddressStrictTimestampSorted (accesses : MemoryAccessList) : Prop :=
  accesses.Sorted address_strict_timestamp_ordering

def AddressSortedMemoryAccessList := {accesses : MemoryAccessList // accesses.isAddressTimestampSorted}

/--
  Sort a memory access list by address and timestamp.
-/
def MemoryAccessList.addressTimestampSort (accesses : MemoryAccessList) : MemoryAccessList :=
  List.insertionSort address_timestamp_ordering accesses

theorem MemoryAccessList.addressTimestampSort_sorted (accesses : MemoryAccessList) :
    (MemoryAccessList.addressTimestampSort accesses).Sorted address_timestamp_ordering := by
  apply List.sorted_insertionSort

theorem MemoryAccessList.addressTimestampSort_perm (accesses : MemoryAccessList) :
    (MemoryAccessList.addressTimestampSort accesses).Perm accesses := by
  apply List.perm_insertionSort

theorem MemoryAccessList.addressStrictTimestampSorted_of_AddressTimestampSorted_noTimestampDup
    (accesses : MemoryAccessList) (h_sorted : accesses.isAddressTimestampSorted)
    (h_no_timestamp_dup : accesses.Notimestampdup) :
    accesses.isAddressStrictTimestampSorted := by
  have h : List.Pairwise address_strict_timestamp_ordering accesses := h_sorted.imp₂ (fun x y hxy => by
    obtain ⟨t_x, a_x, _r_x, _w_x⟩ := x
    obtain ⟨t_y, a_y, _r_y, _w_y⟩ := y
    intro h
    simp [address_strict_timestamp_ordering, timestamps_neq, address_timestamp_ordering] at *
    split_ifs with h_eq
    · simp_all only [↓reduceIte]
      rw [eq_comm] at h
      apply Nat.lt_of_le_of_ne hxy h
    · simp_all only [↓reduceIte]
    ) h_no_timestamp_dup
  exact h

theorem MemoryAccessList.noTimestampDup_perm (l1 l2 : MemoryAccessList)
    (h_l1_nodup : l1.Notimestampdup) (h_perm : l1.Perm l2) :
    l2.Notimestampdup := by
  simp only [Notimestampdup] at *
  apply List.Pairwise.perm h_l1_nodup h_perm
  intro x y hxy
  simp only [timestamps_neq, ne_eq] at *
  obtain ⟨t_x, a_x, _r_x, _w_x⟩ := x
  obtain ⟨t_y, a_y, _r_y, _w_y⟩ := y
  simp_all only [eq_comm, not_false_eq_true]

theorem MemoryAccessList.noTimestampDup_of_cons (head : MemoryAccess) (tail : MemoryAccessList)
    (h : Notimestampdup (head :: tail)) :
    Notimestampdup tail := by
  simp only [Notimestampdup] at *
  exact List.Pairwise.of_cons h

theorem MemoryAccessList.isAddressTimestampSorted_of_cons (head : MemoryAccess) (tail : MemoryAccessList)
    (h : isAddressTimestampSorted (head :: tail)) :
    isAddressTimestampSorted tail := by
  simp only [isAddressTimestampSorted] at *
  exact List.Sorted.of_cons h

theorem MemoryAccessList.noTimestampDup_of_TimestampSorted
    (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) :
    accesses.Notimestampdup := by
  simp only [Notimestampdup, isTimestampSorted, List.Sorted] at *
  have sort_imp_nodup : ∀ {x y : MemoryAccess}, timestamp_ordering x y → timestamps_neq x y := by
    intros x y hxy
    obtain ⟨t_x, a_x, _r_x, _w_x⟩ := x
    obtain ⟨t_y, a_y, _r_y, _w_y⟩ := y
    simp only [timestamp_ordering, timestamps_neq, ne_eq] at *
    linarith
  apply List.Pairwise.imp sort_imp_nodup
  simp_all only


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

theorem MemoryAccessList.isConsistentSingleAddress_filterAddress_of_cons (head : MemoryAccess) (tail : MemoryAccessList)
    (addr : ℕ)
    (h_sorted : isTimestampSorted (head :: tail))
    (h : isConsistentSingleAddress (filterAddress (head :: tail) addr)
         (filterAddress_sorted (head :: tail) h_sorted addr)) :
    isConsistentSingleAddress (filterAddress tail addr)
      (filterAddress_sorted tail (isTimestampSorted_cons head tail h_sorted) addr) := by
  obtain ⟨t, a, r, w⟩ := head
  have h_sorted_tail := isTimestampSorted_cons (t, a, r, w) tail h_sorted
  simp only [filterAddress, List.filter_cons] at h
  split_ifs at h with h_addr
  · exact isConsistentSingleAddress_cons (t, a, r, w) (filterAddress tail addr) _
      (filterAddress_sorted tail h_sorted_tail addr) h
  · exact h

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
  · simp_all only [↓reduceIte]
    rw [h_addr] at h_sorted
    have tail_sorted : tail.isTimestampSorted := by
      unfold isTimestampSorted at h_sorted
      exact List.Sorted.of_cons h_sorted
    have filtered_tail_sorted : (MemoryAccessList.filterAddress tail addr').isTimestampSorted := by
      simp only [filterAddress]
      apply List.Sorted.filter
      exact tail_sorted

    have filter_eq_head : MemoryAccessList.filterAddress (⟨t_head, addr', r_head, w_head⟩ :: tail) addr' =
      (⟨t_head, addr', r_head, w_head⟩ :: (MemoryAccessList.filterAddress tail addr')) := by
      simp only [filterAddress, decide_true, List.filter_cons_of_pos]

    have h_filtered_sorted : MemoryAccessList.isTimestampSorted (⟨t_head, addr', r_head, w_head⟩ :: (MemoryAccessList.filterAddress tail addr')) := by
      rw [←filter_eq_head]
      apply MemoryAccessList.filterAddress_sorted
      assumption

    have h' := MemoryAccessList.isConsistentSingleAddress_cons ⟨t_head, addr', r_head, w_head⟩ (tail.filterAddress addr') h_filtered_sorted filtered_tail_sorted
    specialize h' h
    simp_all only
  · simp_all only [↓reduceIte]

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
      have h_tail := MemoryAccessList.isConsistentSingleAddress_cons_forall (t, a, r, w) tail h_sorted h
      specialize ih h_tail
      simp only [isConsistentOnline, ih, and_true]

      have h_tail_filter_sorted : (MemoryAccessList.filterAddress tail a).isTimestampSorted := by
        simp only [filterAddress]
        apply List.Sorted.filter
        exact h_sorted'

      have h_filtered_sorted : MemoryAccessList.isTimestampSorted ((t, a, r, w) :: (MemoryAccessList.filterAddress tail a)) := by
        simp only [isTimestampSorted, List.sorted_cons, filterAddress, List.mem_filter,
          and_imp] at ⊢ h_sorted
        simp_all only [implies_true, true_and]
        apply List.Sorted.filter
        assumption


      have h' := MemoryAccessList.lastWriteValue_filter tail h_sorted' a h_tail_filter_sorted

      specialize h a
      simp [filterAddress_cons] at h
      -- rw [h']

      have h_iff := MemoryAccessList.isConsistentSingleAddress_iff ((t, a, r, w) :: filterAddress tail a) a h_filtered_sorted
      simp only [filterAddress, List.all_cons, decide_true, List.all_filter, Bool.not_or_self,
        Bool.true_and, List.all_eq_true, implies_true, forall_const] at h_iff
      have is_consistent_online_full := h_iff.mpr h
      simp only [isConsistentOnline] at is_consistent_online_full
      simp only [is_consistent_online_full.left]
      rw [eq_comm]
      apply MemoryAccessList.lastWriteValue_filter

/--
  Offline version of memory consistency checking.
-/
def MemoryAccessList.isConsistentOffline (accesses : MemoryAccessList) (h_sorted : accesses.isAddressTimestampSorted) : Prop := match accesses with
  | [] => True -- no memory access is trivially consistent
  | (_timestamp, _addr, readValue, _writeValue) :: [] => readValue = 0
  | (_t2, addr2, readValue2, _writeValue2) :: (t1, addr1, readValue1, writeValue1) :: rest =>
    (if addr1 = addr2 then readValue2 = writeValue1 else readValue2 = 0) ∧
    MemoryAccessList.isConsistentOffline ((t1, addr1, readValue1, writeValue1) :: rest) (List.Sorted.of_cons h_sorted)

theorem MemoryAccessList.filterAddress_sorted_from_addressTimestampSorted
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isAddressTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (addr : ℕ) :
    (accesses.filterAddress addr).isTimestampSorted := by
  have h_strict := addressStrictTimestampSorted_of_AddressTimestampSorted_noTimestampDup accesses h_sorted h_nodup
  simp only [isAddressStrictTimestampSorted, filterAddress, isTimestampSorted] at h_strict ⊢
  induction accesses with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨t, a, r, w⟩ := head
    simp only [List.filter_cons]
    split_ifs with h_addr
    · simp only [List.sorted_cons]
      constructor
      · intro z hz
        simp only [List.mem_filter] at hz
        obtain ⟨hz_mem, hz_addr⟩ := hz
        obtain ⟨t_z, a_z, r_z, w_z⟩ := z
        simp only [decide_eq_true_eq] at hz_addr
        simp only [List.sorted_cons] at h_strict
        have h_ord := h_strict.1 (t_z, a_z, r_z, w_z) hz_mem
        simp only [address_strict_timestamp_ordering] at h_ord
        simp only [decide_eq_true_eq] at h_addr
        rw [hz_addr, h_addr] at h_ord
        simp only [↓reduceIte] at h_ord
        simp only [timestamp_ordering]
        exact h_ord
      · apply ih
        · simp only [isAddressTimestampSorted] at h_sorted ⊢
          exact List.Sorted.of_cons h_sorted
        · simp only [Notimestampdup] at h_nodup ⊢
          exact List.Pairwise.of_cons h_nodup
        · exact List.Sorted.of_cons h_strict
    · apply ih
      · simp only [isAddressTimestampSorted] at h_sorted ⊢
        exact List.Sorted.of_cons h_sorted
      · simp only [Notimestampdup] at h_nodup ⊢
        exact List.Pairwise.of_cons h_nodup
      · exact List.Sorted.of_cons h_strict

theorem MemoryAccessList.isConsistentSingleAddress_filterAddress_forall_of_cons
    (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : isAddressTimestampSorted (head :: tail))
    (h_nodup : Notimestampdup (head :: tail))
    (h : ∀ addr, isConsistentSingleAddress (filterAddress (head :: tail) addr)
         (filterAddress_sorted_from_addressTimestampSorted (head :: tail) h_sorted h_nodup addr)) :
    ∀ addr, isConsistentSingleAddress (filterAddress tail addr)
      (filterAddress_sorted_from_addressTimestampSorted tail
        (isAddressTimestampSorted_of_cons head tail h_sorted)
        (noTimestampDup_of_cons head tail h_nodup) addr) := by
  intro addr
  obtain ⟨t, a, r, w⟩ := head
  have h_sorted_tail := isAddressTimestampSorted_of_cons (t, a, r, w) tail h_sorted
  have h_nodup_tail := noTimestampDup_of_cons (t, a, r, w) tail h_nodup
  have h_addr_spec := h addr
  simp only [filterAddress, List.filter_cons] at h_addr_spec
  split_ifs at h_addr_spec with h_eq
  · exact isConsistentSingleAddress_cons (t, a, r, w) (filterAddress tail addr) _
      (filterAddress_sorted_from_addressTimestampSorted tail h_sorted_tail h_nodup_tail addr) h_addr_spec
  · exact h_addr_spec

theorem MemoryAccessList.filterAddress_empty_when_address_changes
    (head : MemoryAccess) (second : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : isAddressTimestampSorted (head :: second :: tail))
    (h_addr_ne : head.2.1 ≠ second.2.1) :
    filterAddress (second :: tail) head.2.1 = [] := by
  obtain ⟨t1, a1, r1, w1⟩ := head
  obtain ⟨t2, a2, r2, w2⟩ := second
  simp at h_addr_ne
  simp only [filterAddress]
  -- Show that no element in (second :: tail) has address = a1
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  obtain ⟨tx, ax, rx, wx⟩ := x
  intro h_eq
  -- Convert decide (ax = a1) = true to ax = a1
  rw [decide_eq_true_eq] at h_eq
  subst h_eq
  -- Now we have ax = a1 and x ∈ (second :: tail)
  -- Get the ordering between (t1, ax, r1, w1) and (t2, a2, r2, w2)
  simp only [isAddressTimestampSorted, List.sorted_cons] at h_sorted
  have h_ord_first := h_sorted.1 (t2, a2, r2, w2) List.mem_cons_self
  simp only [address_timestamp_ordering] at h_ord_first
  split_ifs at h_ord_first with h_eq_addr
  · -- Case: a2 = ax, but we have h_addr_ne : ax ≠ a2
    exact h_addr_ne h_eq_addr.symm
  · -- Case: ax < a2
    -- Now get ordering between (t2, a2, r2, w2) and (tx, ax, rx, wx)
    -- x is in (second :: tail), so it's either second or in tail
    cases hx with
    | head =>
      -- x = second, so (tx, ax, rx, wx) = (t2, a2, r2, w2)
      -- This means ax = a2, but we have h_addr_ne : ax ≠ a2
      linarith
    | tail _ hx_tail =>
      -- x ∈ tail
      have h_ord_second := h_sorted.2.1 (tx, ax, rx, wx) hx_tail
      simp only [address_timestamp_ordering] at h_ord_second
      split_ifs at h_ord_second; linarith

theorem MemoryAccessList.isConsistentOffline_of_cons
    (head : MemoryAccess) (tail : MemoryAccessList)
    (h_sorted : isAddressTimestampSorted (head :: tail))
    (h_offline : isConsistentOffline (head :: tail) h_sorted) :
    isConsistentOffline tail (isAddressTimestampSorted_of_cons head tail h_sorted) := by
  obtain ⟨t_head, a_head, r_head, w_head⟩ := head
  cases tail with
  | nil => simp [isConsistentOffline]
  | cons second tail_rest =>
    obtain ⟨t_second, a_second, r_second, w_second⟩ := second
    simp only [isConsistentOffline] at h_offline ⊢
    exact h_offline.2

theorem MemoryAccessList.isConsistentOffline_implies_single_address
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isAddressTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (h_offline : accesses.isConsistentOffline h_sorted)
    (addr : ℕ) :
    (accesses.filterAddress addr).isConsistentSingleAddress
      (filterAddress_sorted_from_addressTimestampSorted accesses h_sorted h_nodup addr) := by
  induction accesses with
  | nil =>
    simp [filterAddress, isConsistentSingleAddress]
  | cons head tail ih =>
    obtain ⟨t_head, a_head, r_head, w_head⟩ := head
    simp only [filterAddress, List.filter_cons]
    split_ifs with h_addr
    · -- head has the target address
      rw [decide_eq_true_eq] at h_addr
      subst h_addr
      -- Now we need to show consistency for (head :: filterAddress tail addr)
      cases tail with
      | nil =>
        simp [isConsistentSingleAddress]
        -- For a singleton list, need to show r_head = 0
        exact h_offline
      | cons second tail_rest =>
        obtain ⟨t_second, a_second, r_second, w_second⟩ := second
        -- Filter the tail
        simp only [List.filter_cons]
        split_ifs with h_second_addr
        · -- second also has address a_head
          rw [decide_eq_true_eq] at h_second_addr
          subst h_second_addr
          -- Now we show consistency for (head :: second :: filterAddress tail_rest a_head)
          simp only [isConsistentSingleAddress]
          constructor
          · -- Show r_second = w_head from offline consistency
            simp only [isConsistentOffline] at h_offline
            simp at h_offline
            exact h_offline.1
          · -- Apply IH to (second :: tail_rest)
            have ih_applied := ih
              (isAddressTimestampSorted_of_cons (t_head, a_second, r_head, w_head) ((t_second, a_second, r_second, w_second) :: tail_rest) h_sorted)
              (noTimestampDup_of_cons (t_head, a_second, r_head, w_head) ((t_second, a_second, r_second, w_second) :: tail_rest) h_nodup)
              (isConsistentOffline_of_cons (t_head, a_second, r_head, w_head) ((t_second, a_second, r_second, w_second) :: tail_rest) h_sorted h_offline)
            simp only [filterAddress, List.filter_cons, decide_true] at ih_applied
            exact ih_applied
        · -- second has a different address
          -- Need to show isConsistentSingleAddress for (head :: filterAddress tail_rest a_head)
          -- Key insight: since a_head ≠ a_second and list is address-sorted,
          -- all elements in (second :: tail_rest) have address ≠ a_head
          have h_addr_ne : ¬(a_second = a_head) := by
            simp only [decide_eq_true_eq] at h_second_addr
            exact h_second_addr
          -- Use filterAddress_empty_when_address_changes to show filterAddress (second :: tail_rest) a_head = []
          have h_empty := filterAddress_empty_when_address_changes
            (t_head, a_head, r_head, w_head) (t_second, a_second, r_second, w_second) tail_rest h_sorted
            (by simp; intro h_eq; exact h_addr_ne h_eq.symm)
          simp only [filterAddress, List.filter_cons] at h_empty
          have h_second_ne : decide (a_second = a_head) = false := by
            simp [h_addr_ne]
          simp only [h_second_ne] at h_empty
          have h_empty_simplified : List.filter (fun x => match x with | (_, addr', _, _) => decide (addr' = a_head)) tail_rest = [] := by
            simp at h_empty
            exact h_empty
          simp only [h_empty_simplified, isConsistentSingleAddress]
          simp only [isConsistentOffline] at h_offline
          simp [h_addr_ne] at h_offline
          exact h_offline.1
    · -- head doesn't have the target address
      -- Apply IH to tail
      apply ih (isAddressTimestampSorted_of_cons (t_head, a_head, r_head, w_head) tail h_sorted)
        (noTimestampDup_of_cons (t_head, a_head, r_head, w_head) tail h_nodup)
      exact isConsistentOffline_of_cons (t_head, a_head, r_head, w_head) tail h_sorted h_offline

theorem MemoryAccessList.isConsistentOffline_iff_all_single_addresses (accesses : MemoryAccessList) (h_sorted : accesses.isAddressTimestampSorted) (h_nodup : accesses.Notimestampdup) :
    MemoryAccessList.isConsistentOffline accesses h_sorted ↔
    ∀ addr, MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress accesses addr) (filterAddress_sorted_from_addressTimestampSorted accesses h_sorted h_nodup addr) := by
  constructor
  · intro h_offline addr
    exact isConsistentOffline_implies_single_address accesses h_sorted h_nodup h_offline addr
  · induction accesses
    · simp [isConsistentOffline]
    rename_i hd tl h_ih
    intro h
    rcases tl
    · rcases hd with ⟨ hd_t, hd_a, hd_r, hd_w ⟩
      simp only [isConsistentOffline]
      specialize h hd_a
      simp only [filterAddress, List.filter, decide_true, isConsistentSingleAddress] at h
      assumption
    rename_i snd tl
    rcases hd with ⟨ hd_t, hd_a, hd_r, hd_w ⟩
    rcases snd with ⟨ snd_t, snd_a, snd_r, snd_w ⟩
    simp only [isConsistentOffline]
    and_intros
    · split
      · rename_i addr_eq
        subst addr_eq
        specialize h snd_a
        simp only [filterAddress, List.filter, decide_true, isConsistentSingleAddress] at h
        aesop
      · -- addresstimestampsorted, and seeing two different addresses, then the first address will never appear again
        -- Since hd_a ≠ snd_a and the list is address-timestamp sorted, hd_a won't appear in (snd :: tl)
        -- Therefore filterAddress ((hd :: snd :: tl)) hd_a = [hd]
        -- And since isConsistentSingleAddress [hd] must hold, we get hd_r = 0
        rename_i h_addr_ne
        -- Use the lemma to show filterAddress (snd :: tl) hd_a is empty
        have h_empty := filterAddress_empty_when_address_changes (hd_t, hd_a, hd_r, hd_w) (snd_t, snd_a, snd_r, snd_w) tl h_sorted (by simp; intro h_eq; exact h_addr_ne h_eq.symm)
        specialize h hd_a
        simp only [filterAddress, List.filter_cons, decide_true] at h
        have h_snd_ne : decide (snd_a = hd_a) = false := by
          simp only [decide_eq_false_iff_not]
          exact h_addr_ne
        simp only [h_snd_ne, ↓reduceIte] at h
        simp only [filterAddress, List.filter_cons, h_snd_ne] at h_empty
        simp only [h_empty, isConsistentSingleAddress] at h
        exact h
    apply h_ih
    · exact isConsistentSingleAddress_filterAddress_forall_of_cons (hd_t, hd_a, hd_r, hd_w) ((snd_t, snd_a, snd_r, snd_w) :: tl) h_sorted h_nodup h
    · exact noTimestampDup_of_cons (hd_t, hd_a, hd_r, hd_w) ((snd_t, snd_a, snd_r, snd_w) :: tl) h_nodup

theorem MemoryAccessList.addressTimestampSort_noTimestampDup
    (accesses : MemoryAccessList)
    (h_nodup : accesses.Notimestampdup) :
    accesses.addressTimestampSort.Notimestampdup := by
  apply noTimestampDup_perm accesses accesses.addressTimestampSort h_nodup
  exact (addressTimestampSort_perm accesses).symm

theorem MemoryAccessList.filterAddress_addressTimestampSort_eq
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_nodup : accesses.Notimestampdup)
    (addr : ℕ) :
    (accesses.filterAddress addr).isConsistentSingleAddress
      (filterAddress_sorted accesses h_sorted addr) ↔
    (accesses.addressTimestampSort.filterAddress addr).isConsistentSingleAddress
      (filterAddress_sorted_from_addressTimestampSorted accesses.addressTimestampSort
        (addressTimestampSort_sorted accesses)
        (addressTimestampSort_noTimestampDup accesses h_nodup) addr) := by
  sorry

/--
  Constructive version of the theorem below.
-/
theorem MemoryAccessList.isConsistentOnline_iff_sorted_isConsistentOffline
    (accesses : MemoryAccessList)
    (h_sorted : accesses.isTimestampSorted)
    (h_nodup : accesses.Notimestampdup) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    MemoryAccessList.isConsistentOffline (MemoryAccessList.addressTimestampSort accesses) (MemoryAccessList.addressTimestampSort_sorted accesses) := by
  rw [isConsistent_iff_all_single_address]
  -- Use isConsistentOffline_iff_all_single_addresses
  rw [isConsistentOffline_iff_all_single_addresses (addressTimestampSort accesses)
    (addressTimestampSort_sorted accesses)
    (addressTimestampSort_noTimestampDup accesses h_nodup)]
  -- Now use filterAddress_addressTimestampSort_eq to relate the two sides
  constructor
  · intro h addr
    rw [← filterAddress_addressTimestampSort_eq accesses h_sorted h_nodup addr]
    exact h addr
  · intro h addr
    rw [filterAddress_addressTimestampSort_eq accesses h_sorted h_nodup addr]
    exact h addr

/--
  Technical lemma for soundness: if there exists two address-timestamp sorted lists of memory accesses
  that are both permutations of the same timestamp-sorted list, then they must be equal.

  Intuition: since the input list is timestamp strictly sorted, then there are no two timestamps in l1
  that are equal, and therefore, for that class of lists, any address-timestamp sorted list is unique.
  (This is true in general, if the initial list contains no duplicates, then any sorting is unique.)
-/
lemma MemoryAccessList.eq_of_perm_of_sorted {l1 l2 l3 : MemoryAccessList} (h_l1_sorted: l1.isTimestampSorted)
    (h_l2_sorted : l2.isAddressTimestampSorted) (h_l3_sorted : l3.isAddressTimestampSorted)
    (h_perm1 : l1.Perm l2) (h_perm2 : l1.Perm l3) : l2 = l3 := by
  simp [isAddressTimestampSorted] at *
  rw [List.perm_comm] at h_perm1
  have l1_nodup := List.Sorted.nodup h_l1_sorted

  have thm1 := List.Sorted.insertionSort_eq h_l2_sorted
  have h_l2_nodup := (List.Perm.nodup_iff h_perm1).mpr l1_nodup
  have h_l3_nodup := (List.Perm.nodup_iff h_perm2).mp l1_nodup

  have l2_perm_l3 := List.Perm.trans h_perm1 h_perm2

  have l1_notimestampdup := MemoryAccessList.noTimestampDup_of_TimestampSorted l1 h_l1_sorted
  have l2_notimestampdup := MemoryAccessList.noTimestampDup_perm l1 l2 l1_notimestampdup (List.Perm.symm h_perm1)
  have l3_notimestampdup := MemoryAccessList.noTimestampDup_perm l1 l3 l1_notimestampdup h_perm2

  have l2_strict_sorted := MemoryAccessList.addressStrictTimestampSorted_of_AddressTimestampSorted_noTimestampDup l2 h_l2_sorted l2_notimestampdup
  have l3_strict_sorted := MemoryAccessList.addressStrictTimestampSorted_of_AddressTimestampSorted_noTimestampDup l3 h_l3_sorted l3_notimestampdup
  exact List.eq_of_perm_of_sorted l2_perm_l3 l2_strict_sorted l3_strict_sorted
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
  constructor
  · intro h
    use ⟨MemoryAccessList.addressTimestampSort accesses, MemoryAccessList.addressTimestampSort_sorted accesses⟩
    constructor
    · simp only
      apply MemoryAccessList.addressTimestampSort_perm
    · simp only
      have h' := MemoryAccessList.isConsistentOnline_iff_sorted_isConsistentOffline accesses h_sorted
      rw [←h']
      assumption
  · rintro ⟨⟨permuted, h_permuted_sorted⟩, h_perm, h_offline⟩
    simp_all only
    rw [List.perm_comm] at h_perm
    have h_eq := MemoryAccessList.eq_of_perm_of_sorted h_sorted h_permuted_sorted (MemoryAccessList.addressTimestampSort_sorted accesses)
      h_perm (by rw [List.perm_comm]; apply MemoryAccessList.addressTimestampSort_perm)
    simp only [h_eq] at h_offline
    simp_rw [←MemoryAccessList.isConsistentOnline_iff_sorted_isConsistentOffline accesses h_sorted] at h_offline
    assumption
