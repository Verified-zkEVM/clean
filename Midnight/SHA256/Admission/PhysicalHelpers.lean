import Clean.Halo2.Keygen.Layout

/-! Lifts the Nat-valued region fixed writes back to the field writes they map. -/
namespace Midnight.SHA256.Admission.PhysicalHelpers
open Halo2 Halo2.Layout
variable {F : Type}

def mapValue (f : F → Nat) (assignment : FixedAssignment F) : FixedAssignment Nat :=
  (assignment.1, assignment.2.1, f assignment.2.2)

theorem regionAssignFixed_refines (f : F → Nat) (starts : List Nat)
    (regions : List (Nat × RegionOperations F))
    (write : FixedAssignment Nat) (member : write ∈ regionAssignFixed f starts regions) :
    ∃ original ∈ regionAssignments starts regions, mapValue f original = write := by
  obtain ⟨⟨index,body⟩,region,member⟩ := List.mem_flatMap.mp member
  obtain ⟨operation,mem,eq⟩ := List.mem_filterMap.mp member
  cases operation <;> try simp at eq
  rename_i column row value
  cases eq
  refine ⟨(column.index,place starts index + row,value),?_,rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨(index,body),region,?_⟩
  exact List.mem_filterMap.mpr ⟨.assignFixed column row value,mem,rfl⟩

end Midnight.SHA256.Admission.PhysicalHelpers
