import Midnight.Math.Witness.Execute
import Std.Data.TreeSet.Lemmas

/-! Balanced-tree acceleration of the ordered dependency check. Unlike native
hash primitives, these keys reduce in Lean's kernel. The refinement proof
preserves the list check used by the constructive execution theorem. -/
namespace Midnight.Math.Witness.Fast
open Halo2 Execute
variable {F : Type}
attribute [local instance] lexOrd

def key (location : Address) : Nat × Nat × Int :=
  ((match location.1.kind with | .advice => 0 | .fixed => 1 | .instance => 2),
    location.1.index, location.2)

theorem key_injective : Function.Injective key := by
  rintro ⟨⟨leftKind,leftIndex⟩,leftRow⟩ ⟨⟨rightKind,rightIndex⟩,rightRow⟩ same
  cases leftKind <;> cases rightKind <;> simp_all [key]

def ordered (place : RegionIndex → Nat) : Std.TreeSet (Nat × Nat × Int) → List (Assignment F) → Bool
  | _, [] => true
  | known, assignment :: rest =>
    !known.contains (key assignment.destination) &&
      Reads.program (fun cell => known.contains (key (address place cell))) assignment.program &&
      ordered place (known.insert (key assignment.destination)) rest

theorem refines (place : RegionIndex → Nat) (assignments : List (Assignment F))
    (known : Std.TreeSet (Nat × Nat × Int)) (prior : List Address)
    (same : ∀ location, known.contains (key location) = decide (location ∈ prior))
    (accepted : ordered place known assignments = true) :
    Execute.ordered place prior assignments = true := by
  induction assignments generalizing known prior with
  | nil => rfl
  | cons assignment rest ih =>
    obtain ⟨⟨fresh,reads⟩,tail⟩ := Bool.and_eq_true_iff.mp accepted |>.imp_left Bool.and_eq_true_iff.mp
    apply (ordered_cons place prior assignment rest).mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [same, Bool.not_eq_true', decide_eq_false_iff_not] using fresh
    · have equal : (fun cell : AssignedCell F => known.contains (key (address place cell))) = allowed place prior := by
        funext cell
        exact same _
      rw [equal] at reads
      exact reads
    · apply ih (known.insert (key assignment.destination)) (assignment.destination :: prior) ?_ tail
      intro location
      apply Bool.eq_iff_iff.mpr
      simp only [Std.TreeSet.contains_insert, same, Bool.or_eq_true, beq_iff_eq,
        Std.compare_eq_iff_eq, key_injective.eq_iff, decide_eq_true_eq, List.mem_cons]
      exact or_congr eq_comm Iff.rfl

theorem empty_refines (place : RegionIndex → Nat) (assignments : List (Assignment F))
    (accepted : ordered place ∅ assignments = true) : Execute.ordered place [] assignments = true :=
  refines place assignments ∅ [] (by intro location; simp) accepted

end Midnight.Math.Witness.Fast
