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
      writeValue
    else
      MemoryAccessList.lastWriteValue rest (List.Sorted.of_cons h) addr

-- now, we need a way to express that the memory access list is consistent
def MemoryAccessList.isConsistentOnline (accesses : MemoryAccessList) (h : accesses.isTimestampSorted) : Prop := match accesses with
  | [] => True -- no memory access is trivially consistent
  | (timestamp, addr, readValue, _writeValue) :: rest =>
    -- here we need to check that the readValue is consistent with the previous writes to the same address
    timestamp = rest.length ∧
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
