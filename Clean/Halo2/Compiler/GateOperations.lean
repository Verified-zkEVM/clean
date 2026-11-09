import Clean.Halo2.Compiler.ConstraintFamilies
import Clean.Halo2.TopLevel

/-! # Gate activations and their operation semantics -/

namespace Halo2

/-- One custom-gate activation in the placed operation stream. -/
structure EnabledGate (F : Type) where
  gate : Gate F
  region : RegionIndex
  row : ℕ

namespace EnabledGate

variable {F : Type} [FiniteField F]

/-- Clean's semantic relation for one enabled gate. -/
def Satisfied (place : RegionIndex → ℕ) (env : Environment F)
    (enabled : EnabledGate F) : Prop :=
  enabled.gate.constraints.Forall fun constraint =>
    constraint.poly.eval
      (Query.eval env
        (fun index => if index = enabled.gate.selector.index then 1 else 0)
        (place enabled.region + enabled.row : ℕ)) = 0

end EnabledGate

/-- Gate activations in one region, retaining the region index used by placement. -/
def regionEnabledGates {F : Type} (self : RegionIndex) :
    RegionOperations F → List (EnabledGate F)
  | [] => []
  | .enableGate gate row :: rest =>
      ⟨gate, self, row⟩ :: regionEnabledGates self rest
  | _ :: rest => regionEnabledGates self rest

/-- Gate activations in a complete layouter stream, with exact region-index threading. -/
def operationEnabledGates {F : Type} :
    Operations F → RegionIndex → List (EnabledGate F)
  | [], _ => []
  | .region _ body :: rest, i =>
      regionEnabledGates i body ++ operationEnabledGates rest (i + 1)
  | .constrainInstance _ _ _ :: rest, i => operationEnabledGates rest i
  | .loadTable _ _ :: rest, i => operationEnabledGates rest i

namespace CircuitConstraintFamily

variable {F : Type} [FiniteField F]

/-- One region's gate-family projection is exactly its extracted enabled gates. -/
theorem region_gate_constraints_iff
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment F)
    (ops : RegionOperations F) :
    RegionConstraints .gate place self env ops ↔
      (regionEnabledGates self ops).Forall (EnabledGate.Satisfied place env) := by
  induction ops with
  | nil => simp [RegionConstraints, regionEnabledGates]
  | cons op rest ih =>
      cases op <;>
        simp_all [RegionConstraints, RegionConstraint, RegionOperation.Constraints,
          regionEnabledGates, EnabledGate.Satisfied]

/-- The complete gate-family projection is satisfaction of all extracted activations. -/
theorem gate_constraints_iff_enabledGates
    (place : RegionIndex → ℕ) (env : Environment F)
    (ops : Operations F) (i : RegionIndex) :
    Constraints .gate place env ops i ↔
      (operationEnabledGates ops i).Forall (EnabledGate.Satisfied place env) := by
  induction ops generalizing i with
  | nil => simp [Constraints, operationEnabledGates]
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [Constraints, ih, region_gate_constraints_iff]
          simp [operationEnabledGates, List.forall_append]
      | constrainInstance cell col row =>
          rw [Constraints, ih]
          simp [operationEnabledGates]
      | loadTable table values =>
          rw [Constraints, ih]
          simp [operationEnabledGates]

end CircuitConstraintFamily

namespace OperationsKeygenCoherent

/-- A coherent region registers every extracted enabled gate. -/
theorem mem_gates_of_mem_regionEnabledGates
    {F : Type} {cs : ConstraintSystem F}
    {self : RegionIndex} {body : RegionOperations F}
    (hcoherent :
      body.Forall (RegionOperation.KeygenCoherent cs))
    {enabled : EnabledGate F}
    (henabled : enabled ∈ regionEnabledGates self body) :
    enabled.gate ∈ cs.gates := by
  induction body with
  | nil => simp [regionEnabledGates] at henabled
  | cons operation rest ih =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | enableGate gate row =>
          simp only [RegionOperation.KeygenCoherent] at hcoherent
          simp only [regionEnabledGates, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · exact hcoherent.1
          · exact ih hcoherent.2 henabled
      | assignAdvice column row witness =>
          exact ih hcoherent.2 henabled
      | assignFixed column row value =>
          exact ih hcoherent.2 henabled
      | enableLookup argument selectors row =>
          exact ih hcoherent.2 henabled
      | constrainEqual left right =>
          exact ih hcoherent.2 henabled
      | constrainConstant cell value =>
          exact ih hcoherent.2 henabled
      | constrainInstance cell column row =>
          exact ih hcoherent.2 henabled

/-- A coherent operation stream registers every extracted enabled gate. -/
theorem mem_gates_of_mem_operationEnabledGates
    {F : Type} {cs : ConstraintSystem F}
    {operations : Operations F} {i : RegionIndex}
    (hcoherent : OperationsKeygenCoherent cs operations)
    {enabled : EnabledGate F}
    (henabled : enabled ∈ operationEnabledGates operations i) :
    enabled.gate ∈ cs.gates := by
  induction operations generalizing i with
  | nil => simp [operationEnabledGates] at henabled
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          rcases (region_cons
            cs name body rest).mp hcoherent with
            ⟨hoperation, hrest⟩
          simp only [operationEnabledGates, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · exact mem_gates_of_mem_regionEnabledGates hoperation henabled
          · exact ih hrest henabled
      | constrainInstance cell column row =>
          have hrest := (constrainInstance_cons
            cs cell column row rest).mp hcoherent
          exact ih hrest.2.2 henabled
      | loadTable table values =>
          have hrest := (loadTable_cons
            cs table values rest).mp hcoherent
          exact ih hrest.2 henabled

end OperationsKeygenCoherent

/-- A region gate activation occurs in the keygen selector-activation table. -/
theorem mem_regionActivations_of_mem_enabledGate
    {F : Type} (starts : List ℕ)
    {self : RegionIndex} {body : RegionOperations F}
    {enabled : EnabledGate F}
    (henabled : enabled ∈ regionEnabledGates self body) :
    (enabled.gate.selector.index,
      starts.getD enabled.region 0 + enabled.row) ∈
      activations starts [(self, body)] := by
  simp only [activations, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  induction body with
  | nil =>
      simp [regionEnabledGates] at henabled
  | cons operation rest ih =>
      cases operation with
      | enableGate gate row =>
          simp only [regionEnabledGates, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · simp
          · exact List.mem_append_right _ (ih henabled)
      | assignAdvice column row witness =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | assignFixed column row value =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | enableLookup argument selectors row =>
          exact List.mem_append_right _ (ih henabled)
      | constrainEqual left right =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | constrainConstant cell value =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled
      | constrainInstance cell column row =>
          simpa only [List.flatMap_cons, List.nil_append] using ih henabled

/--
Every extracted enabled gate occurs in the selector activations derived from the
same operation stream and V1 placement inputs.
-/
theorem mem_activations_of_mem_operationEnabledGate
    {F : Type} (starts : List ℕ)
    {operations : Operations F} {i : RegionIndex}
    {enabled : EnabledGate F}
    (henabled : enabled ∈ operationEnabledGates operations i) :
    (enabled.gate.selector.index,
      starts.getD enabled.region 0 + enabled.row) ∈
      activations starts (indexedRegions operations i).1 := by
  induction operations generalizing i with
  | nil =>
      simp [operationEnabledGates] at henabled
  | cons operation rest ih =>
      cases operation with
      | region name body =>
          simp only [operationEnabledGates, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · have hregion :=
              mem_regionActivations_of_mem_enabledGate starts henabled
            have hregion' :
                (enabled.gate.selector.index,
                  starts.getD enabled.region 0 + enabled.row) ∈
                  body.flatMap fun operation =>
                    match operation with
                    | .enableGate gate row =>
                        [(gate.selector.index, starts.getD i 0 + row)]
                    | .enableLookup _ selectors row =>
                        selectors.map fun selector =>
                          (selector.index, starts.getD i 0 + row)
                    | _ => [] := by
              simpa only [activations, List.flatMap_cons,
                List.flatMap_nil, List.append_nil] using hregion
            exact List.mem_append_left _ hregion'
          · have hrest := ih (i := i + 1) henabled
            exact List.mem_append_right _ hrest
      | constrainInstance cell column row =>
          exact ih (i := i) henabled
      | loadTable table values =>
          exact ih (i := i) henabled

end Halo2
