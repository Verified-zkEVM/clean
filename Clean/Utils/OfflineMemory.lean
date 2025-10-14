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

/--
  A memory access list is consistent for a single address if the reads and writes to that address are consistent.
-/
def MemoryAccessList.isConsistentSingleAddress (accesses : MemoryAccessList) : Prop := match accesses with
  -- no memory access is trivially consistent
  | [] => True
  -- if there's only one access, the read must be zero
  | (_timestamp, _addr, readValue, _writeValue) :: [] => readValue = 0
  -- if there are multiple accesses, the read of the most recent access must equal the write of the previous access
  | (_t2, _addr2, readValue2, _writeValue2) :: (t1, addr1, readValue1, writeValue1) :: rest =>
    readValue2 = writeValue1 ∧ MemoryAccessList.isConsistentSingleAddress ((t1, addr1, readValue1, writeValue1) :: rest)


theorem MemoryAccessList.isConsistentSingleAddress_iff (accesses : MemoryAccessList) (addr : ℕ) (h_sorted : accesses.isTimestampSorted)
    (h_eq : accesses.all (fun (addr', _readValue, _writeValue) => addr' = addr)) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔ MemoryAccessList.isConsistentSingleAddress accesses := by
  sorry


theorem MemoryAccessList.isConsistent_iff_all_single_address (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) :
    MemoryAccessList.isConsistentOnline accesses h_sorted ↔
    (∀ addr : ℕ, MemoryAccessList.isConsistentSingleAddress (MemoryAccessList.filterAddress accesses addr)) := by
  sorry


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
