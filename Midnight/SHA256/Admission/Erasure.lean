import Midnight.Chips.CertifiedCircuit
import Midnight.SHA256.WitnessPlacement

/-! Native admission is insensitive to advice witness recipes. The transfer
retains every fixed value, configured gate/lookup, copy, placement and table. -/
namespace Midnight.SHA256.Admission.Erasure
open Halo2 Midnight.Chips
open WitnessErasure

theorem regions (ops : Operations F) (self : Nat) :
    (indexedRegions (operations ops) self).1 =
      (indexedRegions ops self).1.map (fun pair => (pair.1, pair.2.map regionOperation)) := by
  induction ops generalizing self with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp only [operations, List.map_cons, operation, indexedRegions,
      List.map_cons, ih] at *
    all_goals exact ih self

private theorem regionActivations (starts : List Nat) (index : Nat) (body : RegionOperations F) :
    Halo2.activations starts [(index,body.map regionOperation)] =
      Halo2.activations starts [(index,body)] := by
  simp only [Halo2.activations, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.flatMap_map]
  apply List.flatMap_congr
  intro op _
  cases op <;> rfl

theorem activations (starts : List Nat) (regions : List (Nat × RegionOperations F)) :
    Halo2.activations starts (regions.map fun pair => (pair.1,pair.2.map regionOperation)) =
      Halo2.activations starts regions := by
  induction regions with
  | nil => rfl
  | cons pair rest ih =>
    have head := regionActivations starts pair.1 pair.2
    simpa only [List.map_cons, Halo2.activations, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using congrArg₂ (fun (a b : List (Nat × Nat)) => a ++ b) head ih

private theorem regionGate (body : RegionOperations F) (gate : Gate F) (row : Nat) :
    .enableGate gate row ∈ body.map regionOperation ↔ .enableGate gate row ∈ body := by
  induction body with
  | nil => simp
  | cons op rest ih => cases op <;> simp [regionOperation, ih]

private theorem regionLookup (body : RegionOperations F) (lookup : LookupArgument F)
    (enabled : List Selector) (row : Nat) :
    .enableLookup lookup enabled row ∈ body.map regionOperation ↔
      .enableLookup lookup enabled row ∈ body := by
  induction body with
  | nil => simp
  | cons op rest ih => cases op <;> simp [regionOperation, ih]

private theorem activationClosed (body : RegionOperations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    OperationsLawful.ActivationClosed gates lookups (body.map regionOperation) ↔
      OperationsLawful.ActivationClosed gates lookups body := by
  unfold OperationsLawful.ActivationClosed OperationsLawful.localActivations
  rw [regionActivations]
  simp only [OperationsLawful.GateEnabled, OperationsLawful.LookupEnabled,
    regionGate, regionLookup]

private theorem regionValid (body : RegionOperations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (counts : ConfigureCounts) (starts : List Nat) (usable index : Nat) :
    OperationsLawful.RegionValid gates lookups counts starts usable index
        (body.map regionOperation) ↔
      OperationsLawful.RegionValid gates lookups counts starts usable index body := by
  unfold OperationsLawful.RegionValid
  rw [activationClosed, List.forall_map_iff, Function.comp_def]
  have instruction (op : RegionOperation F) :
      OperationsLawful.InstructionValid counts (starts.getD index 0) usable (regionOperation op) ↔
        OperationsLawful.InstructionValid counts (starts.getD index 0) usable op := by
    cases op <;> rfl
  simp only [instruction]

private theorem tableValid (op : Operation F) (counts : ConfigureCounts) (usable : Nat) :
    OperationsLawful.TableValid counts usable (operation op) ↔
      OperationsLawful.TableValid counts usable op := by
  cases op <;> rfl

theorem tableColumns (ops : Operations F) :
    OperationsLawful.tableColumns (operations ops) = OperationsLawful.tableColumns ops := by
  simp only [operations, OperationsLawful.tableColumns, List.filterMap_map]
  congr 1
  funext op
  cases op <;> rfl

private theorem instanceCopiesLocal (region : Nat) (body : RegionOperations F) :
    OperationsLawful.instanceCopiesLocal region (body.map regionOperation) =
      OperationsLawful.instanceCopiesLocal region body := by
  have assigned : (fun cell => (body.map regionOperation).any (OperationsLawful.assignsAdvice cell)) =
      fun cell => body.any (OperationsLawful.assignsAdvice cell) := by
    funext cell
    rw [List.any_map]
    congr 1
    funext op
    cases op <;> rfl
  unfold OperationsLawful.instanceCopiesLocal
  rw [assigned, List.all_map]
  congr 1
  funext op
  cases op <;> rfl

def operationsLawful (ops : Operations F) (gates : List (Gate F))
    (lookups : List (LookupArgument F)) (counts : ConfigureCounts) (starts : List Nat) (usable : Nat)
    (checked : OperationsLawful.Lawful (operations ops) gates lookups counts starts usable) :
    OperationsLawful.Lawful ops gates lookups counts starts usable where
  regions := by
    have h := checked.regions
    rw [regions, List.forall_map_iff, Function.comp_def] at h
    simpa only [regionValid] using h
  tables := by
    have h := checked.tables
    simpa only [operations, List.forall_map_iff, Function.comp_def, tableValid] using h
  tablesDistinct := by
    have h := checked.tablesDistinct
    rwa [tableColumns] at h
  instanceCopies := by
    have h := checked.instanceCopies
    rw [regions, List.forall_map_iff, Function.comp_def] at h
    simpa only [instanceCopiesLocal] using h

private theorem regionSources (body : RegionOperations F) :
    Halo2.regionDeclaredCopies (body.map regionOperation) = Halo2.regionDeclaredCopies body := by
  simp only [Halo2.regionDeclaredCopies, List.filterMap_map]
  congr 1
  funext operation
  cases operation <;> rfl

theorem sources (ops : Operations F) : Halo2.operationDeclaredCopies (operations ops) = Halo2.operationDeclaredCopies ops := by
  simp only [operations, Halo2.operationDeclaredCopies, List.flatMap_map]
  congr 1
  funext instruction
  cases instruction <;> simp only [operation, regionSources]

private theorem regionConstant (body : RegionOperations F) (cell : Cell) (value : F) :
    .constrainConstant cell value ∈ body.map regionOperation ↔
      .constrainConstant cell value ∈ body := by
  induction body with
  | nil => simp
  | cons op rest ih => cases op <;> simp [regionOperation, ih]

theorem noConstants (ops : Operations F) :
    CopyLawful.NoDeferredConstants (operations ops) ↔ CopyLawful.NoDeferredConstants ops := by
  unfold CopyLawful.NoDeferredConstants CopyLawful.RegionNoDeferredConstants
  constructor
  · intro checked name body member cell value present
    exact checked name (body.map regionOperation)
      (List.mem_map.mpr ⟨.region name body, member, rfl⟩) cell value
      ((regionConstant body cell value).mpr present)
  · intro checked name body member cell value present
    obtain ⟨op, sourceMember, equality⟩ := List.mem_map.mp member
    cases op <;> simp only [operation, reduceCtorEq] at equality
    obtain ⟨rfl,rfl⟩ := equality
    exact checked _ _ sourceMember cell value ((regionConstant _ _ _).mp present)

private theorem regionConstants (body : RegionOperations F) :
    FloorPlanner.regionConstantValues (body.map regionOperation) =
      FloorPlanner.regionConstantValues body := by
  induction body with
  | nil => rfl
  | cons op rest ih => cases op <;> simp [regionOperation, FloorPlanner.regionConstantValues, ih]

private theorem measured (index : Nat) (body : RegionOperations F) :
    FloorPlanner.measureRegion index (body.map regionOperation) =
      FloorPlanner.measureRegion index body := by
  simp only [FloorPlanner.measureRegion, region_summary]

theorem plan (column : Nat) (ops : Operations F) :
    FloorPlanner.SimpleFloorPlanner.plan column (operations ops) =
      FloorPlanner.SimpleFloorPlanner.plan column ops := by
  unfold FloorPlanner.SimpleFloorPlanner.plan
  rw [regions, List.foldl_map]
  apply congrArg (fun step => List.foldl step _ _)
  funext state region
  obtain ⟨index, body⟩ := region
  simp only [FloorPlanner.SimpleFloorPlanner.planStep, measured, regionConstants]

private theorem regionLaidOut (index : Nat) (body : RegionOperations F) :
    (body.map regionOperation).all (CopyLawful.regionLaidOut index) =
      body.all (CopyLawful.regionLaidOut index) := by
  rw [List.all_map]
  congr 1
  funext op
  cases op <;> rfl

theorem laidOut (index : Nat) (ops : Operations F) :
    CopyLawful.laidOut index (operations ops) = CopyLawful.laidOut index ops := by
  induction ops generalizing index with
  | nil => rfl
  | cons op rest ih =>
    have ih' : ∀ index, CopyLawful.laidOut index (rest.map operation) = CopyLawful.laidOut index rest := ih
    cases op <;> simp only [operations, List.map_cons, operation, CopyLawful.laidOut, regionLaidOut, ih']

def copiesLawful (ops : Operations F) (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixed : List (Column .fixed)) (permutation : List Halo2.Layout.ColRef)
    (starts : List Nat) (usable : Nat) (constant : Option Nat)
    (checked : CopyLawful.Lawful (operations ops) gates lookups fixed permutation starts usable constant) :
    CopyLawful.Lawful ops gates lookups fixed permutation starts usable constant where
  registered := (WitnessErasure.keygen ops gates lookups fixed _).mp checked.registered
  laidOut := (Erasure.laidOut 0 ops).symm.trans checked.laidOut
  constants := by
    cases constant with
    | none => exact (noConstants ops).mp checked.constants
    | some column =>
      have placed : (FloorPlanner.SimpleFloorPlanner.plan column (operations ops)).constants.Forall
          (fun placed => placed.2.2 < usable) := checked.constants
      show (FloorPlanner.SimpleFloorPlanner.plan column ops).constants.Forall _
      rwa [plan] at placed
  endpoints := by simpa only [CopyLawful.EndpointsValid, sources] using checked.endpoints

theorem tableFixed (ops : Operations F) (usable : Nat) :
    Halo2.Layout.tableFixed scalarNat usable (operations ops) = Halo2.Layout.tableFixed scalarNat usable ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih => cases op <;> simp only [operations, List.map_cons, operation,
      Halo2.Layout.tableFixed, ih] at *

theorem regionFixed (starts : List Nat) (regions : List (Nat × RegionOperations F)) :
    Halo2.Layout.regionAssignFixed scalarNat starts
        (regions.map fun pair => (pair.1,pair.2.map regionOperation)) =
      Halo2.Layout.regionAssignFixed scalarNat starts regions := by
  simp only [Halo2.Layout.regionAssignFixed, List.flatMap_map, List.filterMap_map]
  apply List.flatMap_congr
  intro pair _
  apply List.filterMap_congr
  intro op _
  cases op <;> rfl

theorem starts (constant : Option Nat) (ops : Operations F) :
    Layout.Planner.simple.starts constant (operations ops) = Layout.Planner.simple.starts constant ops := by
  cases constant with
  | none =>
    change FloorPlanner.SimpleFloorPlanner.starts (operations ops) = FloorPlanner.SimpleFloorPlanner.starts ops
    rw [← Midnight.Math.FloorPlanner.SimplePlacement.starts_eq_native,
      ← Midnight.Math.FloorPlanner.SimplePlacement.starts_eq_native]
    exact Midnight.Math.FloorPlanner.SimpleShapes.source_starts_eq _ _ (WitnessPlacement.observe_erasure ops)
  | some column => simp only [Layout.Planner.starts, plan]

theorem constants (constant : Option Nat) (ops : Operations F) :
    Layout.Planner.simple.constants constant (operations ops) =
      Layout.Planner.simple.constants constant ops := by
  cases constant with
  | none => rfl
  | some column => simp only [Layout.Planner.constants, plan]

theorem streamFixed (usable : Nat) (starts : List Nat) (ops : Operations F) :
    ∀ (constants : List (Nat × Nat × Nat)) (index : Nat),
    Layout.streamFixedWrites usable starts constants index (operations ops) =
      Layout.streamFixedWrites usable starts constants index ops := by
  induction ops with
  | nil => intro constants index; rfl
  | cons op rest ih =>
    intro constants index
    simp only [operations] at ih ⊢
    cases op with
    | region name body =>
      have fixed := regionFixed starts [(index, body)]
      simp only [List.map_cons, List.map_nil] at fixed
      simp only [List.map_cons, operation, Layout.streamFixedWrites, regionConstants, fixed, ih]
    | loadTable table values =>
      simp only [List.map_cons, operation, Layout.streamFixedWrites, ih]
    | constrainInstance cell column row =>
      simp only [List.map_cons, operation, Layout.streamFixedWrites, ih]

theorem sourceFixed (ops : Operations F) (config : Layout.Config) :
    Layout.sourceFixedWrites (operations ops) config .simple = Layout.sourceFixedWrites ops config .simple := by
  show Layout.streamFixedWrites _ (Layout.Planner.simple.starts config.constant (operations ops))
      (Layout.Planner.simple.constants config.constant (operations ops)) 0 (operations ops) =
    Layout.streamFixedWrites _ (Layout.Planner.simple.starts config.constant ops)
      (Layout.Planner.simple.constants config.constant ops) 0 ops
  rw [constants, starts, streamFixed]

theorem sourceActivations (ops : Operations F) (constant : Option Nat) :
    Layout.sourceActivations (operations ops) constant .simple =
      Layout.sourceActivations ops constant .simple := by
  unfold Layout.sourceActivations
  rw [starts, regions, activations]

/-- Lift the unchanged native admission certificate to the original witness-bearing
operation stream. This theorem removes no certificate obligations. -/
def certificate (source : Keygen.CS) (ops : Operations F) (k : Nat)
    (checked : CertifiedCircuit.Certificate source (operations ops) k .simple) :
    CertifiedCircuit.Certificate source ops k .simple where
  configuration := checked.configuration
  rows := checked.rows
  layout := ⟨by
    have fixed := checked.layout.fixedCertificate
    rw [sourceFixed, sourceActivations] at fixed
    exact fixed⟩
  copies := by
    have copies := checked.copies
    rw [starts] at copies
    exact copiesLawful ops _ _ _ _ _ _ _ copies
  operations := by
    have valid := checked.operations
    rw [starts] at valid
    exact operationsLawful ops _ _ _ _ _ valid

end Midnight.SHA256.Admission.Erasure
