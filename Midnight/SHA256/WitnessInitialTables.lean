import Midnight.SHA256.WitnessInitial
import Midnight.SHA256.WitnessErasure
import Midnight.Math.Witness.Operations

/-! Discharge the executor's full-stream table obligation from the exact source
operation identity. Advice erasure preserves every load and table value. -/
namespace Midnight.SHA256.WitnessInitial
open Halo2

attribute [local irreducible] Synthesis.schedule SHA256.activation WitnessCircuit.preimageCircuit

private theorem tables_erasure (env : Environment F) (ops : Operations F) :
    Midnight.Math.Witness.Operations.tables env (WitnessErasure.operations ops) ↔ Midnight.Math.Witness.Operations.tables env ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    simp only [WitnessErasure.operations] at ih ⊢
    cases op <;> simp only [List.map_cons, WitnessErasure.operation, Midnight.Math.Witness.Operations.tables, ih]

private theorem tables_append (env : Environment F) (left right : Operations F) :
    Midnight.Math.Witness.Operations.tables env (left ++ right) ↔ Midnight.Math.Witness.Operations.tables env left ∧ Midnight.Math.Witness.Operations.tables env right := by
  induction left with
  | nil => simp only [List.nil_append, Midnight.Math.Witness.Operations.tables, true_and]
  | cons op rest ih =>
    cases op <;> simp only [List.cons_append, Midnight.Math.Witness.Operations.tables, ih, and_assoc]

private theorem schedule_tables (env : Environment F) (schedule : Array Chips.Synthesis.Step)
    (activate : Nat → Nat → List (RegionOperation F)) :
    Midnight.Math.Witness.Operations.tables env (Chips.Synthesis.scheduleToOperations schedule activate) := by
  unfold Chips.Synthesis.scheduleToOperations
  generalize schedule.toList = steps
  induction steps with
  | nil => trivial
  | cons step rest ih => cases step <;> exact ih

/-- All table equations in the actual source stream hold initially. The source
identity retains literal table values; no captured fixture is an input. -/
theorem source_tables (hint : ProverHint F) (input : Vector (WitgenIR F 1) 24) :
    Midnight.Math.Witness.Operations.tables (initial hint).toEnvironment ((WitnessCircuit.preimageCircuit input).operations 0) := by
  rw [← tables_erasure, WitnessErasure.preimage_operations_eq_source]
  rw [Synthesis.operations, tables_append]
  refine ⟨?_, ?_⟩
  · unfold Synthesis.toOperations
    exact schedule_tables (initial hint).toEnvironment Synthesis.schedule SHA256.activation
  · change Midnight.Math.Witness.Operations.tables (initial hint).toEnvironment (Semantics.Preimage.tables.operations 0)
    exact (Midnight.Math.Witness.Operations.extendsWitnesses_iff (fun _ => 0) 0 (initial hint) _).mp
      (tables_witnesses hint (fun _ => 0) 0) |>.2

end Midnight.SHA256.WitnessInitial
