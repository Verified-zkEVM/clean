import Midnight.Keygen.ConfigureLawful

/-! Reuse previously checked local gate validity when certifying configuration
registration; this avoids repeating the polynomial structural check. -/
namespace Midnight.SHA256.Admission
open Midnight.Keygen
open Halo2 (Expression)

theorem gateLawful_of_valid (source : CS) (gate : GateSpec)
    (valid : gate.valid = true) (allocated : gate.SelectorsAllocated source)
    (registered : gate.queries.toList.Forall source.RegistersQuery) : gate.Lawful source := by
  refine ⟨allocated, ?_, ?_⟩
  · apply List.forall_iff_forall_mem.mpr
    intro query member
    exact ⟨List.all_eq_true.mp (Bool.and_eq_true_iff.mp valid).1 query member,
      List.forall_iff_forall_mem.mp registered query member⟩
  · apply List.forall_iff_forall_mem.mpr
    rintro ⟨name, constraint⟩ member
    obtain ⟨free, declared⟩ := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp (Bool.and_eq_true_iff.mp valid).2 (name, constraint) member)
    exact ⟨free, (Expression.declared_iff constraint _).mp declared⟩

end Midnight.SHA256.Admission
