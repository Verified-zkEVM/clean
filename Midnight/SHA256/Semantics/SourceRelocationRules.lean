import Midnight.SHA256.WitnessErasureCore
import Midnight.Chips.Relocation
import Midnight.SHA256.Semantics.LinearNormalization

/-! Kernel-checked normalization rules for symbolic region starts. The rules are
opt-in proof reductions; they do not change the circuit or the field operations.
Keeping configured activations opaque prevents unrelated constraint ASTs from
being expanded while comparing the circuit's source schedule. -/
namespace Midnight.SHA256.Semantics.SourceRelocation.Rules
open Halo2

theorem nat_add_assoc (a b c : Nat) :
    Nat.add (Nat.add a b) c = Nat.add a (Nat.add b c) := Nat.add_assoc a b c

theorem nat_add_zero (a : Nat) : Nat.add a 0 = a := Nat.add_zero a

theorem map_append {α β : Type} (f : α → β) (left right : List α) :
    List.map f (List.append left right) =
      List.append (List.map f left) (List.map f right) := List.map_append

theorem nil_append {α : Type} (right : List α) :
    List.append ([] : List α) right = right := rfl

theorem cons_append {α : Type} (head : α) (left right : List α) :
    List.append (head :: left) right = head :: List.append left right := rfl

theorem append_nil {α : Type} (left : List α) :
    List.append left [] = left := List.append_nil left

theorem erase_apply (op : RegionOperation F) :
    WitnessErasure.regionOperation op = (match op with
      | .assignAdvice column row _ => .assignAdvice column row (.ofFExpr (.const 0))
      | op => op) := rfl

theorem relocate_apply (offset : Nat) (op : RegionOperation F) :
    Chips.Relocation.regionOperation offset op = (match op with
      | .constrainEqual left right =>
          .constrainEqual (Chips.Relocation.cell offset left) (Chips.Relocation.cell offset right)
      | .constrainConstant source value =>
          .constrainConstant (Chips.Relocation.cell offset source) value
      | .constrainInstance source column row =>
          .constrainInstance (Chips.Relocation.cell offset source) column row
      | op => op) := by cases op <;> rfl

theorem activation_relocate (offset selector row : Nat) :
    (SHA256.activation selector row).map (Chips.Relocation.regionOperation offset) =
      SHA256.activation selector row := by
  simp only [SHA256.activation, List.map_append, List.map_map, Function.comp_def,
    Chips.Relocation.regionOperation]

/-- Expanding the proposition, rather than `decide`, lets the proof evaluator
cancel a common symbolic region offset before evaluating source cell filters. -/
theorem assigned_eq (left right : AssignedCell F) :
    (left = right) =
      (left.cell.regionIndex = right.cell.regionIndex ∧
       left.cell.rowOffset = right.cell.rowOffset ∧ left.cell.column = right.cell.column) := by
  apply propext
  cases left with | mk left =>
    cases right with | mk right =>
      cases left with | mk lr lo lc =>
        cases right with | mk rr ro rc =>
          simp only [AssignedCell.mk.injEq, Cell.mk.injEq]

theorem nat_add_left_eq (a b c : Nat) :
    (Nat.add a b = Nat.add a c) = (b = c) := propext (by simp)

theorem nat_add_self_eq (a b : Nat) :
    (Nat.add a b = a) = (b = 0) := propext (by simp)

theorem nat_self_add_eq (a b : Nat) :
    (a = Nat.add a b) = (0 = b) := propext (by simp [eq_comm])

end Midnight.SHA256.Semantics.SourceRelocation.Rules
