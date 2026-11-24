import Midnight.SHA256.Semantics.Initialize
import Midnight.SHA256.Semantics.ScheduleSpec

/-! Pure list/Fin-fold bridge for the 64 compression rounds. The source constants
are related to Clean's K vector before the list traversal is equated to the spec. -/
namespace Midnight.SHA256.Semantics.RoundsSpec

attribute [local irreducible] Specs.SHA256.sha256Round Specs.SHA256.sha256Compress
  Specs.SHA256.K Synthesis.roundConstants

/-- Nat-indexed form of the exact native round inputs. The loop theorem only
uses indices below 64, so neither array default is read. -/
def step (words : Vector Nat 64) (state : Vector Nat 8) (index : Nat) : Vector Nat 8 :=
  Specs.SHA256.sha256Round state Synthesis.roundConstants[index]! words.toArray[index]!

def fold (words : Vector Nat 64) (items : List Nat) (state : Vector Nat 8) : Vector Nat 8 :=
  items.foldl (step words) state

theorem constant_at (index : Fin 64) :
    Synthesis.roundConstants[index.val]! = Specs.SHA256.K[index].toNat := by
  rw [Initialize.roundConstants_eq_K]
  rw [getElem!_pos (Specs.SHA256.K.map UInt32.toNat).toArray index.val (by simp)]
  simp only [Vector.getElem_toArray, Vector.getElem_map]
  rfl

theorem step_at (words : Vector Nat 64) (state : Vector Nat 8) (index : Fin 64) :
    step words state index.val = Specs.SHA256.sha256Round state
      Specs.SHA256.K[index].toNat words[index] := by
  unfold step
  rw [constant_at, getElem!_pos words.toArray index.val (by simp)]
  rfl

theorem fold_append_one (words : Vector Nat 64) (items : List Nat)
    (state : Vector Nat 8) (index : Nat) :
    fold words (items ++ [index]) state = step words (fold words items state) index := by
  simp only [fold, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem fold_reference (words : Vector Nat 64) (state : Vector Nat 8) :
    fold words (List.range 64) state = Specs.SHA256.sha256Compress state words := by
  unfold Specs.SHA256.sha256Compress fold
  have body : (fun s (i : Fin 64) => Specs.SHA256.sha256Round s
      Specs.SHA256.K[i].toNat words[i]) =
      (fun s (i : Fin 64) => step words s (i.val + 0)) := by
    funext s i
    simpa only [Nat.add_zero] using (step_at words s i).symm
  rw [body, ScheduleSpec.foldl_range 64 0 (fun i s => step words s i)]
  rw [List.range_eq_range']

end Midnight.SHA256.Semantics.RoundsSpec
