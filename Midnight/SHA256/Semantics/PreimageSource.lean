import Midnight.SHA256.Semantics.Inputs
import Midnight.SHA256.Semantics.GatesLookup
import Midnight.SHA256.Spec

/-! Exact external-hint, table and public-copy boundary of the native preimage
example. The wrapper supplies only external hints; arbitrary cell-reading input
programs are deliberately not exposed as the public prover interface. -/
namespace Midnight.SHA256.Semantics.Preimage
open Halo2 WitnessCircuit

abbrev Cell := WitnessCircuit.Cell

attribute [local irreducible] WitnessCircuit.synthesize WitnessCircuit.body

def hintKey : String := "midnight.sha256.preimage"

def privatePrograms : Vector (WitgenIR F 1) 24 :=
  Vector.ofFn fun i : Fin 24 => .ofFExpr (.hintGet hintKey 24 (.const 0) i)

/-- The one external row supplied by the prover, defaulting to zero when absent
under the existing Clean hint semantics. -/
def hintFields (hint : ProverHint F) : Vector F 24 :=
  (hint hintKey 24)[0]?.getD default

def hintMessage (hint : ProverHint F) : Spec.Message :=
  (hintFields hint).map ZMod.val

theorem privatePrograms_eval (env : Placed ProverEnvironment F) (i : Fin 24) :
    ((privatePrograms[i]).eval env)[0] = (hintFields env.env.hint)[i] := by
  simp only [privatePrograms, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [eval_ofFExpr_zero]
  rfl

theorem privatePrograms_honest (env : Placed ProverEnvironment F)
    (bytes : Spec.Bytes (hintMessage env.env.hint)) :
    Inputs.HonestBytes env privatePrograms.toList := by
  intro program member
  obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp member
  have bound : i < 24 := by simpa using hi
  have eq' : privatePrograms[i] = program := by simpa using eq
  rw [← eq']
  have value := privatePrograms_eval env ⟨i,bound⟩
  simp only [Fin.getElem_fin] at value
  rw [value]
  simpa only [hintMessage, Vector.getElem_map, Fin.getElem_fin] using bytes ⟨i,bound⟩

/-- The actual five table loads, with exactly their native source columns. -/
def tables : Circuit F Unit := shaTables

def Capacity (env : Environment F) : Prop :=
  byteRangeRows.length ≤ env.usableRows ∧ spreadRows.length ≤ env.usableRows

theorem tables_sound (self : RegionIndex) (env : Placed Environment F)
    (capacity : Capacity env.env)
    (loaded : Constraints env.place env.env (tables.operations self) self) :
    Range.ByteTable env.env ∧ Gates.SpreadTable env.env := by
  have range : Constraints env.place env.env
      ((loadRange ⟨⟨11⟩⟩ ⟨⟨12⟩⟩ [8]).operations self) self := by
    simp only [tables, shaTables, circuit_norm] at loaded
    simp only [loadRange, circuit_norm]
    exact ⟨loaded.1,loaded.2.1,loaded.2.2.1,loaded.2.2.2.1⟩
  have spread : Constraints env.place env.env
      ((loadSpread ⟨⟨13⟩⟩ ⟨⟨14⟩⟩ ⟨⟨15⟩⟩).operations self) self := by
    simp only [tables, shaTables, circuit_norm] at loaded
    simpa only [loadSpread, circuit_norm] using loaded.2.2.2.2
  exact ⟨Range.byteTable_of_load self range capacity.1,
    Gates.spreadTable_of_load self spread capacity.2⟩

theorem tables_complete (self : RegionIndex) (env : Placed ProverEnvironment F)
    (witnesses : ExtendsWitnesses env.place env.env (tables.operations self) self) :
    Constraints env.place env.env.toEnvironment (tables.operations self) self := by
  exact witnesses

def exposeLoop (outputs : Array Cell) (indices : List Nat) : Circuit F PUnit :=
  forIn indices PUnit.unit fun i _ => do
    constrainInstance outputs[i]! ⟨1⟩ i
    return .yield PUnit.unit

theorem exposeLoop_run (outputs : Array Cell) (indices : List Nat) (self : RegionIndex) :
    exposeLoop outputs indices self =
      (PUnit.unit, indices.map (fun i => Operation.constrainInstance outputs[i]!.cell ⟨1⟩ i), self) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    unfold exposeLoop
    rw [List.forIn_cons]
    change ((exposeLoop outputs rest self).1, Operation.constrainInstance outputs[index]!.cell ⟨1⟩ index ::
      (exposeLoop outputs rest self).2.1, (exposeLoop outputs rest self).2.2) = _
    rw [ih]
    rfl

/-- Exactly the source range loop that publishes the returned digest cells. -/
def expose (outputs : Array Cell) : Circuit F PUnit := do
  for i in [:outputs.size] do constrainInstance outputs[i]! ⟨1⟩ i

theorem expose_loop (outputs : Array Cell) : expose outputs = exposeLoop outputs (List.range outputs.size) := by
  unfold expose exposeLoop
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have range : List.range' 0 [:outputs.size].size = List.range outputs.size := by
    simp [List.range'_eq_map_range]
  rw [range]
  funext self
  change (PUnit.unit, (exposeLoop outputs (List.range outputs.size) self).2.1 ++ [],
    (exposeLoop outputs (List.range outputs.size) self).2.2) =
    exposeLoop outputs (List.range outputs.size) self
  rw [exposeLoop_run]
  simp only [List.append_nil]

theorem expose_operations (outputs : Array Cell) (self : RegionIndex) :
    (expose outputs).operations self =
      (List.range outputs.size).map (fun i => Operation.constrainInstance outputs[i]!.cell ⟨1⟩ i) := by
  rw [expose_loop]
  exact congrArg (fun result => result.2.1) (exposeLoop_run outputs _ self)

theorem expose_next (outputs : Array Cell) (self : RegionIndex) :
    (expose outputs).nextRegionIndex self = self := by
  rw [expose_loop]
  exact congrArg (fun result => result.2.2) (exposeLoop_run outputs _ self)

theorem expose_count (outputs : Array Cell) (self : RegionIndex) :
    ((expose outputs).operations self).regionCount = 0 := by
  rw [expose_operations]
  generalize List.range outputs.size = indices
  induction indices with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem copyList_constraints (outputs : Array Cell) (indices : List Nat)
    (env : Placed Environment F) (self : RegionIndex) :
    Constraints env.place env.env
      (indices.map fun i => Operation.constrainInstance outputs[i]!.cell ⟨1⟩ i) self ↔
      ∀ i ∈ indices, outputs[i]!.eval env.place env.env = env.env.inst ⟨1⟩ i := by
  induction indices with
  | nil => simp [Constraints]
  | cons index rest ih =>
    simp only [List.map_cons, Constraints, Environment.get_inst, ih, List.mem_cons, forall_eq_or_imp]
    rfl

theorem expose_constraints (outputs : Array Cell) (env : Placed Environment F) (self : RegionIndex) :
    Constraints env.place env.env ((expose outputs).operations self) self ↔
      ∀ i, i < outputs.size → outputs[i]!.eval env.place env.env = env.env.inst ⟨1⟩ i := by
  rw [expose_operations, copyList_constraints]
  simp only [List.mem_range]

theorem expose_witnesses (outputs : Array Cell) (env : Placed ProverEnvironment F) (self : RegionIndex) :
    ExtendsWitnesses env.place env.env ((expose outputs).operations self) self := by
  rw [expose_operations]
  generalize List.range outputs.size = indices
  induction indices with
  | nil => trivial
  | cons _ _ ih => exact ih

def finish (outputs : Array Cell) : Circuit F (Array Cell) := do
  expose outputs
  tables
  return outputs

private theorem circuit_bind_assoc {α β γ : Type} (first : Circuit F α)
    (next : α → Circuit F β) (last : β → Circuit F γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  funext self
  change (_, (_ ++ _) ++ _, _) = (_, _ ++ (_ ++ _), _)
  simp only [List.append_assoc]

private theorem circuit_pure_bind {α β : Type} (value : α) (next : α → Circuit F β) :
    (pure value >>= next) = next value := rfl

-- Reassociate the boundary before substituting the large SHA program. Keeping
-- that program abstract prevents kernel conversion from expanding its body.
private theorem finish_source (source : Circuit F (Array Cell)) :
    (do
      let outputs ← source
      for i in [:outputs.size] do constrainInstance outputs[i]! ⟨1⟩ i
      shaTables
      return outputs) = (do
      let outputs ← source
      finish outputs) := by
  unfold finish expose tables
  simp only [circuit_bind_assoc, circuit_pure_bind]

theorem preimage_source (input : Vector (WitgenIR F 1) 24) :
    WitnessCircuit.preimageCircuit input = (do
      let outputs ← WitnessCircuit.synthesize input
      finish outputs) :=
  finish_source (WitnessCircuit.synthesize input)

/-- The public program retains all native source assignments, public copies and
loads; only its 24 private input recipes are fixed to external hint reads. -/
def circuit : Circuit F (Array Cell) := WitnessCircuit.preimageCircuit privatePrograms

end Midnight.SHA256.Semantics.Preimage
