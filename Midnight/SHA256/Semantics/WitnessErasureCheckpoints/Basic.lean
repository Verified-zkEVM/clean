import Midnight.SHA256.WitnessErasureCore
import Midnight.SHA256.Semantics.LinearNormalization
import Midnight.SHA256.Semantics.StructuralNormalization

/-! The exact observation used by bounded erasure comparisons. This lowers
the original keygen schedule with its actual configured activations before
encoding it. Unlike a shape observation, fixed values and complete gate,
lookup, table and copy payloads remain present. -/
namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

def observe (steps : Array Chips.Synthesis.Step) : List WitnessErasure.Code.Top :=
  (Chips.Synthesis.scheduleToOperations steps SHA256.activation).map WitnessErasure.Code.encode

abbrev Checked {α : Type} (action : Synthesis.Build α)
    (before : Chips.SynthesisCheckpoint.Cursor) (output : α)
    (after : Chips.SynthesisCheckpoint.Cursor) (chunk : List WitnessErasure.Code.Top) : Prop :=
  Midnight.Math.Checkpoint.Checked Chips.SynthesisCheckpoint.frame observe
    action before output after chunk

theorem Checked.observed {α : Type} (action : Synthesis.Build α)
    (before : Chips.SynthesisCheckpoint.Cursor) (output : α)
    (after : Chips.SynthesisCheckpoint.Cursor) (chunk : List WitnessErasure.Code.Top)
    (checked : Checked action before output after chunk) :
    observe (action (before.state #[])).2.steps = chunk := by
  have result := (checked #[]).2.2
  change observe (action (before.state #[])).2.steps = observe #[] ++ chunk at result
  simpa only [observe, Chips.Synthesis.scheduleToOperations,
    Array.toList_empty, List.map_nil, List.nil_append] using result

theorem encode_erased_region (operation : RegionOperation F) :
    WitnessErasure.Code.encodeRegion (WitnessErasure.regionOperation operation) =
      WitnessErasure.Code.encodeRegion operation := by
  cases operation <;> rfl

theorem encode_erased_operation (operation : Operation F) :
    WitnessErasure.Code.encode (WitnessErasure.operation operation) =
      WitnessErasure.Code.encode operation := by
  cases operation <;> simp only [WitnessErasure.operation, WitnessErasure.Code.encode,
    List.map_map, Function.comp_def, encode_erased_region]

theorem encode_erased (operations : Operations F) :
    (WitnessErasure.operations operations).map WitnessErasure.Code.encode =
      operations.map WitnessErasure.Code.encode := by
  simp only [WitnessErasure.operations, List.map_map, Function.comp_def,
    encode_erased_operation]

theorem encode_eq_of_erased_eq (left right : Operations F)
    (equality : WitnessErasure.operations left = WitnessErasure.operations right) :
    left.map WitnessErasure.Code.encode = right.map WitnessErasure.Code.encode :=
  (encode_erased left).symm.trans
    ((congrArg (List.map WitnessErasure.Code.encode) equality).trans (encode_erased right))

theorem input_independent (left right : Vector (WitgenIR F 1) 24) :
    ((WitnessCircuit.preimageCircuit left).operations).map WitnessErasure.Code.encode =
      ((WitnessCircuit.preimageCircuit right).operations).map WitnessErasure.Code.encode :=
  encode_eq_of_erased_eq
    ((WitnessCircuit.preimageCircuit left).operations)
    ((WitnessCircuit.preimageCircuit right).operations)
    (WitnessErasure.preimage_operations_independent left right 0)

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
