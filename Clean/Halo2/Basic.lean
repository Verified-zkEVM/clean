import Clean.Halo2.Operations

/-!
# Halo2 circuit monads — DESIGN SKETCH

Port of `Clean/Circuit/Basic.lean` to halo2: the monads circuit authors write in, at the
two levels of `Operations.lean`.

- `RegionCircuit F α` — inside one region. A reader in the region's own index (needed so
  `assignAdvice` can return an `AssignedCell` pointing into this region) plus an
  operations writer. Local rows are **explicit arguments**, mirroring the Rust `Region`
  API where every call takes `offset: usize` — unlike main Clean's `Circuit`, there is
  no threaded row counter, because cells within a region are laid out in a 2D grid, not
  consumed linearly.
- `Circuit F α` — the layouter level. Threads the next region index (the
  prefix-computable part, exactly like Clean's `offset`) and writes layouter operations.
  Region *placement* is not decided here: it is the `place` semantics parameter,
  computed by the floor planner at top level.

TODO (deferred to the formal-circuit port): FormalCircuit-style packages at both levels,
subcircuit calls, `ElaboratedCircuit` analogue, witgen-IR witness values, `circuit_norm`
lemma set for the monad operations.

Rust reference: `halo2_proofs/src/circuit.rs` (`Region`, `Layouter` APIs).
-/

namespace Halo2

variable {F : Type} {α β : Type}

/-! ## Region-level circuits -/

/-- A circuit fragment inside one region: knows its region's index, accumulates
region-level operations. -/
def RegionCircuit (F : Type) (α : Type) :=
  RegionIndex → α × List (RegionOperation F)

namespace RegionCircuit

instance : Monad (RegionCircuit F) where
  pure a := fun _ => (a, [])
  bind x f := fun self =>
    let (a, ops) := x self
    let (b, ops') := f a self
    (b, ops ++ ops')

@[circuit_norm]
theorem bind_def (x : RegionCircuit F α) (f : α → RegionCircuit F β) :
    x >>= f = fun self =>
      let (a, ops) := x self
      let (b, ops') := f a self
      (b, ops ++ ops') := rfl

@[circuit_norm]
theorem pure_def (a : α) : (pure a : RegionCircuit F α) = fun _ => (a, []) := rfl

end RegionCircuit

/-- Witness a value into an advice cell. Rust: `region.assign_advice(col, offset, to)`
(`to` is a reserved token in Lean, hence `compute`). Returns the assigned cell; adds no
constraint. -/
@[circuit_norm]
def assignAdvice (col : Column .advice) (row : ℕ) (compute : Placed ProverEnvironment F → F) :
    RegionCircuit F (AssignedCell F) :=
  fun self => (⟨⟨self, row, col.toAny⟩⟩, [.assignAdvice col row compute])

/-- Rust: `region.assign_fixed(col, offset, value)`. -/
@[circuit_norm]
def assignFixed (col : Column .fixed) (row : ℕ) (value : F) :
    RegionCircuit F (AssignedCell F) :=
  fun self => (⟨⟨self, row, col.toAny⟩⟩, [.assignFixed col row value])

/-- Copy an existing cell into this region: assign + copy constraint.
Rust: `assigned_cell.copy_advice(region, col, offset)`. -/
@[circuit_norm]
def copyAdvice [Field F] (src : AssignedCell F) (col : Column .advice) (row : ℕ) :
    RegionCircuit F (AssignedCell F) :=
  fun self =>
    let cell : Cell := ⟨self, row, col.toAny⟩
    (⟨cell⟩, [
      .assignAdvice col row fun pe => src.eval pe.place pe.env.toEnvironment,
      .constrainEqual cell src.cell])

/-- Rust: `region.constrain_equal(a, b)`. -/
@[circuit_norm]
def constrainEqual (a b : AssignedCell F) : RegionCircuit F Unit :=
  fun _ => ((), [.constrainEqual a.cell b.cell])

/-- Rust: `region.constrain_constant(cell, value)`. -/
@[circuit_norm]
def constrainConstant (a : AssignedCell F) (value : F) : RegionCircuit F Unit :=
  fun _ => ((), [.constrainConstant a.cell value])

/-- Enable a gate at a local row (Rust: `selector.enable(region, offset)`): records the
selector activation and carries the gate's constraints. See `Operations.lean`. -/
@[circuit_norm]
def Gate.enable (gate : Gate F) (row : ℕ) : RegionCircuit F Unit :=
  fun _ => ((), [.enableGate gate row])

/-! ## Layouter-level circuits -/

/-- A layouter-level circuit: threads the next region index (like Clean's `offset`) and
accumulates layouter operations. -/
def Circuit (F : Type) (α : Type) :=
  RegionIndex → α × List (Operation F) × RegionIndex

namespace Circuit

instance : Monad (Circuit F) where
  pure a := fun i => (a, [], i)
  bind x f := fun i =>
    let (a, ops, i') := x i
    let (b, ops', i'') := f a i'
    (b, ops ++ ops', i'')

@[circuit_norm]
theorem bind_def (x : Circuit F α) (f : α → Circuit F β) :
    x >>= f = fun i =>
      let (a, ops, i') := x i
      let (b, ops', i'') := f a i'
      (b, ops ++ ops', i'') := rfl

@[circuit_norm]
theorem pure_def (a : α) : (pure a : Circuit F α) = fun i => (a, [], i) := rfl

/-- The operations of a circuit, from a given initial region index. -/
@[circuit_norm]
def operations (circuit : Circuit F α) (i : RegionIndex := 0) : List (Operation F) :=
  (circuit i).2.1

/-- The output of a circuit, from a given initial region index. -/
@[circuit_norm]
def output (circuit : Circuit F α) (i : RegionIndex := 0) : α :=
  (circuit i).1

end Circuit

/-- Create a region and run a region-level circuit inside it, allocating the next region
index. Rust: `layouter.assign_region(name, |region| …)`. -/
@[circuit_norm]
def assignRegion (name : String) (body : RegionCircuit F α) : Circuit F α :=
  fun i =>
    let (a, ops) := body i
    (a, [.region name ops], i + 1)

/-- Rust: `layouter.constrain_instance(cell, instance_col, row)`. -/
@[circuit_norm]
def constrainInstance (cell : AssignedCell F) (col : Column .instance) (row : ℕ) :
    Circuit F Unit :=
  fun i => ((), [.constrainInstance cell.cell col row], i)

/-- Top-level satisfaction of a circuit, for a given placement of its regions.
Gadget proofs are generic over `place` (and the initial region index); the final
statement instantiates `place` with the floor planner's output. -/
@[circuit_norm]
def Circuit.ConstraintsHold [Field F] (place : RegionIndex → ℕ) (env : Environment F)
    (circuit : Circuit F α) : Prop :=
  Halo2.ConstraintsHold place env (circuit.operations) 0

end Halo2
