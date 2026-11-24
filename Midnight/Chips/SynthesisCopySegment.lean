import Midnight.Chips.SynthesisShapeLawful
import Midnight.Math.Operations.RegionalCopy
import Clean.Halo2.Lemmas

/-! Bounded checking of copy provenance over exact source-derived chunks. -/
namespace Midnight.Chips.SynthesisCopySegment
open Halo2 SynthesisCheckpoint SynthesisShapeLawful Midnight.Math.Operations.RegionalCopy

theorem decode_append (left right : List Step) : decode (left ++ right) = decode left ++ decode right := by
  induction left with
  | nil => rfl
  | cons step rest ih => cases step <;> simp only [List.cons_append, decode, ih]

def Segment (table : Table) (before after : Nat) (chunk : List Step) : Prop :=
  check table before (decode chunk) = true ∧ before + (decode chunk).regionCount = after

theorem Segment.empty (table : Table) (index : Nat) : Segment table index index [] := by
  exact ⟨rfl, Nat.add_zero _⟩

theorem Segment.append (table : Table) (before middle after : Nat) (left right : List Step)
    (first : Segment table before middle left) (next : Segment table middle after right) :
    Segment table before after (left ++ right) := by
  constructor
  · rw [decode_append, check_append, first.1, first.2, next.1]
    rfl
  · rw [decode_append, Operations.regionCount_append, ← Nat.add_assoc, first.2]
    exact next.2

theorem Segment.accepted (table : Table) (before after : Nat) (chunk : List Step)
    (segment : Segment table before after chunk) : check table before (decode chunk) = true := segment.1

end Midnight.Chips.SynthesisCopySegment
