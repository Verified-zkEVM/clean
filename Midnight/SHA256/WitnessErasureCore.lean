import Midnight.SHA256.WitnessErasureCodeCore

/-! Exact advice-only erasure of the real witness circuit. All fixed values,
full configured gate/lookup objects, copies and operation ordering are retained. -/
namespace Midnight.SHA256.WitnessErasure
open Halo2

def regionOperation : RegionOperation F → RegionOperation F
  | .assignAdvice column row _ => .assignAdvice column row (.ofFExpr (.const 0))
  | operation => operation

def operation : Operation F → Operation F
  | .region name body => .region name (body.map regionOperation)
  | operation => operation

def operations (ops : Operations F) : Operations F := ops.map operation

def region {α : Type} (body : RegionCircuit F α) : RegionCircuit F α :=
  fun self => ((body self).1, (body self).2.map regionOperation)

def circuit {α : Type} (body : Circuit F α) : Circuit F α :=
  fun self => ((body self).1, operations (body self).2.1, (body self).2.2)

def build {α : Type} (body : WitnessCircuit.Build α) : WitnessCircuit.Build α :=
  fun cache => circuit (body cache)

@[simp] theorem region_pure {α : Type} (value : α) :
    region (pure value) = pure value := rfl

@[simp] theorem region_bind {α β : Type} (first : RegionCircuit F α)
    (next : α → RegionCircuit F β) :
    region (first >>= next) = region first >>= fun value => region (next value) := by
  funext self
  change (_, ((first self).2 ++ (next (first self).1 self).2).map regionOperation) = _
  simp only [List.map_append]
  rfl

@[simp] theorem circuit_pure {α : Type} (value : α) :
    circuit (pure value) = pure value := rfl

@[simp] theorem circuit_bind {α β : Type} (first : Circuit F α)
    (next : α → Circuit F β) :
    circuit (first >>= next) = circuit first >>= fun value => circuit (next value) := by
  funext self
  change (_, operations ((first self).2.1 ++ (next (first self).1 (first self).2.2).2.1), _) = _
  simp only [operations, List.map_append]
  rfl

@[simp] theorem build_pure {α : Type} (value : α) :
    build (pure value) = pure value := rfl

@[simp] theorem build_bind {α β : Type} (first : WitnessCircuit.Build α)
    (next : α → WitnessCircuit.Build β) :
    build (first >>= next) = build first >>= fun value => build (next value) := by
  funext cache
  exact circuit_bind (first cache) (fun result => next result.1 result.2)

@[simp] theorem assignAdvice (column : Column .advice) (row : Nat) (program : WitgenIR F 1) :
    region (Halo2.assignAdvice column row program) =
      Halo2.assignAdvice column row (.ofFExpr (.const 0)) := rfl

@[simp] theorem assignFixed (column : Column .fixed) (row : Nat) (value : F) :
    region (Halo2.assignFixed column row value) = Halo2.assignFixed column row value := rfl

@[simp] theorem assignRegion {α : Type} (name : String) (body : RegionCircuit F α) :
    circuit (Halo2.assignRegion name body) = Halo2.assignRegion name (region body) := rfl

@[simp] theorem build_region {α : Type} (name : String) (body : RegionCircuit F α) :
    build (WitnessCircuit.region name body) = WitnessCircuit.region name (region body) := rfl

@[simp] theorem activation (selector row : Nat) :
    (SHA256.activation selector row).map regionOperation = SHA256.activation selector row := by
  simp only [SHA256.activation, List.map_append, List.map_map, Function.comp_def,
    regionOperation]

@[simp] theorem enable (selector row : Nat) :
    region (WitnessCircuit.enable selector row) = WitnessCircuit.enable selector row := by
  funext self
  simp only [region, WitnessCircuit.enable, activation]

/-- A monad transformation preserving pure/bind also preserves loops. -/
structure Hom (M N : Type → Type) [Monad M] [Monad N] where
  map : {α : Type} → M α → N α
  pure : ∀ {α : Type} (value : α), map (pure value) = pure value
  bind : ∀ {α β : Type} (first : M α) (next : α → M β),
    map (first >>= next) = map first >>= fun value => map (next value)

theorem Hom.forIn_list {M N : Type → Type} [Monad M] [Monad N]
    (hom : Hom M N) {α β : Type} (items : List α) (initial : β)
    (step : α → β → M (ForInStep β)) :
    hom.map (forIn items initial step) =
      forIn items initial (fun item state => hom.map (step item state)) := by
  induction items generalizing initial with
  | nil => simp only [List.forIn_nil, hom.pure]
  | cons item rest ih =>
    simp only [List.forIn_cons, hom.bind]
    congr 1
    funext result
    cases result with
    | done result => exact hom.pure result
    | yield result => exact ih result

theorem Hom.forIn_array {M N : Type → Type} [Monad M] [Monad N]
    (hom : Hom M N) {α β : Type} (items : Array α) (initial : β)
    (step : α → β → M (ForInStep β)) :
    hom.map (forIn items initial step) =
      forIn items initial (fun item state => hom.map (step item state)) := by
  rcases items with ⟨items⟩
  simp only [List.forIn_toArray]
  exact hom.forIn_list items initial step

def buildHom : Hom WitnessCircuit.Build WitnessCircuit.Build :=
  ⟨build, build_pure, build_bind⟩

/-- A loop ignoring item values depends only on its length. -/
theorem forIn_same_length {M : Type → Type} [Monad M] {α β γ : Type}
    (left : List α) (right : List β) (same : left.length = right.length)
    (initial : γ) (step : γ → M (ForInStep γ)) :
    forIn left initial (fun _ => step) = forIn right initial (fun _ => step) := by
  induction left generalizing right initial with
  | nil =>
    have : right = [] := List.eq_nil_of_length_eq_zero same.symm
    subst right
    rfl
  | cons head tail ih =>
    cases right with
    | nil => simp at same
    | cons head' tail' =>
      simp only [List.forIn_cons]
      congr 1
      funext result
      cases result with
      | done result => rfl
      | yield result => exact ih tail' (by simpa using same) result

@[simp] theorem build_forIn {α β : Type} (items : Array α) (initial : β)
    (step : α → β → WitnessCircuit.Build (ForInStep β)) :
    build (forIn items initial step) =
      forIn items initial (fun item state => build (step item state)) :=
  buildHom.forIn_array items initial step

theorem forIn_array_same_size {M : Type → Type} [Monad M] {α β γ : Type}
    (left : Array α) (right : Array β) (same : left.size = right.size)
    (initial : γ) (step : γ → M (ForInStep γ)) :
    forIn left initial (fun _ => step) = forIn right initial (fun _ => step) := by
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  simp only [List.forIn_toArray]
  exact forIn_same_length left right same initial step

/-- Input programs never control allocation, constant caching or continuation
outputs. Erasure makes the input assignment loop independent of every program. -/
theorem assignBytes_independent (left right : Vector (WitgenIR F 1) 24) :
    build (WitnessCircuit.assignBytes left) = build (WitnessCircuit.assignBytes right) := by
  simp only [WitnessCircuit.assignBytes, build_bind, build_pure, build_forIn,
    build_region, region_bind, enable, assignFixed, assignAdvice]
  congr 1
  apply forIn_array_same_size
  simp

theorem body_independent (left right : Vector (WitgenIR F 1) 24) :
    build (WitnessCircuit.body left) = build (WitnessCircuit.body right) := by
  simp only [WitnessCircuit.body, build_bind]
  rw [assignBytes_independent left right]

theorem synthesize_independent (left right : Vector (WitgenIR F 1) 24) :
    circuit (WitnessCircuit.synthesize left) = circuit (WitnessCircuit.synthesize right) := by
  have h := congrFun (body_independent left right) []
  change circuit (WitnessCircuit.body left []) = circuit (WitnessCircuit.body right []) at h
  simp only [WitnessCircuit.synthesize, circuit_bind, StateT.run]
  rw [h]

/-- Universal input-program independence of all keygen-relevant operations,
including public digest copies and every loaded table. -/
theorem preimage_independent (left right : Vector (WitgenIR F 1) 24) :
    circuit (WitnessCircuit.preimageCircuit left) = circuit (WitnessCircuit.preimageCircuit right) := by
  simp only [WitnessCircuit.preimageCircuit, circuit_bind]
  rw [synthesize_independent left right]

@[simp] theorem circuit_operations {α : Type} (body : Circuit F α) (start : RegionIndex) :
    (circuit body).operations start = operations (body.operations start) := rfl

@[simp] theorem circuit_output {α : Type} (body : Circuit F α) (start : RegionIndex) :
    (circuit body).output start = body.output start := rfl

/-- Project before instantiating the full source circuit, keeping kernel
conversion independent of its 690-region implementation. -/
private theorem operations_eq_of_circuit_eq {α : Type} (left right : Circuit F α)
    (same : circuit left = circuit right) (start : RegionIndex) :
    operations (left.operations start) = operations (right.operations start) := by
  have h := congrArg (fun program : Circuit F α => program.operations start) same
  simpa only [circuit_operations] using h

theorem preimage_operations_independent (left right : Vector (WitgenIR F 1) 24)
    (start : RegionIndex) :
    operations ((WitnessCircuit.preimageCircuit left).operations start) =
      operations ((WitnessCircuit.preimageCircuit right).operations start) :=
  operations_eq_of_circuit_eq (WitnessCircuit.preimageCircuit left)
    (WitnessCircuit.preimageCircuit right) (preimage_independent left right) start

/-- The keygen schedule of `Synthesis` already uses the erased advice program everywhere. -/
theorem source_schedule_fixedpoint (steps : Array Chips.Synthesis.Step) :
    operations (Chips.Synthesis.scheduleToOperations steps SHA256.activation) =
      Chips.Synthesis.scheduleToOperations steps SHA256.activation := by
  simp only [operations, Chips.Synthesis.scheduleToOperations, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro step _
  cases step with
  | publicInput cell row => rfl
  | region name instructions =>
    simp only [operation, List.map_flatMap]
    congr 1
    congr 1
    funext instruction
    cases instruction <;> simp only [List.map_cons, List.map_nil, regionOperation, activation]

theorem source_operations_fixedpoint :
    operations (Synthesis.operations SHA256.activation) = Synthesis.operations SHA256.activation := by
  simp only [Synthesis.operations, Synthesis.toOperations, operations, List.map_append]
  change operations (Chips.Synthesis.scheduleToOperations Synthesis.schedule SHA256.activation) ++
    Synthesis.tableOperations.map operation = _
  rw [source_schedule_fixedpoint]
  rfl

namespace Code
theorem decode_encode_region (op : RegionOperation F) :
    decodeRegion (encodeRegion op) = regionOperation op := by
  cases op <;> rfl

theorem decode_encode (op : Operation F) : decode (encode op) = operation op := by
  cases op <;> simp only [encode, decode, List.map_map, Function.comp_def,
    decode_encode_region, operation]

theorem decode_encode_operations (ops : Operations F) :
    (ops.map encode).map decode = operations ops := by
  simp only [List.map_map, Function.comp_def, decode_encode, operations]

end Code

end Midnight.SHA256.WitnessErasure
