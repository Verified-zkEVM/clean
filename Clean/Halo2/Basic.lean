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

TODO (deferred to the formal-circuit port): FormalCircuit-style packages at both levels
and their `toSubcircuit` conversions (the `.subcircuit` operations and their semantics
already exist in `Operations.lean`), `ElaboratedCircuit` analogue, witgen-IR witness
values, `circuit_norm` lemma set for the monad operations.

**Simp philosophy** (deliberate normal forms, unlike main Clean's tag-everything
approach): monadic composition, `Circuit.output`/`operations`/`nextRegionIndex`, and DSL
atoms like `assignAdvice` ARE the normal forms — none of them carry `@[circuit_norm]`
and they never unfold in proofs. The simp set lives in `Lemmas.lean` and consists of
*composition lemmas* describing how those atoms interact (`operations` of a bind,
`Constraints` of an append, …), keeping goals at the abstraction level of the circuit
source.

Rust reference: `halo2_proofs/src/circuit.rs` (`Region`, `Layouter` APIs).
-/

namespace Halo2

variable {F : Type} [FiniteField F] {α β : Type}

/-! ## Region-level circuits -/

/-- A circuit fragment inside one region: knows its region's index, accumulates
region-level operations. -/
def RegionCircuit (F : Type) [FiniteField F] (α : Type) :=
  RegionIndex → α × RegionOperations F

namespace RegionCircuit

instance : Monad (RegionCircuit F) where
  pure a := fun _ => (a, [])
  bind x f := fun self =>
    let (a, ops) := x self
    let (b, ops') := f a self
    (b, ops ++ ops')

/-- The operations of a region circuit, given its region's index. -/
def operations (body : RegionCircuit F α) (self : RegionIndex) : RegionOperations F :=
  (body self).2

/-- The output of a region circuit, given its region's index. -/
def output (body : RegionCircuit F α) (self : RegionIndex) : α :=
  (body self).1

end RegionCircuit

/-- Witness a value into an advice cell. Rust: `region.assign_advice(col, offset, to)`
(`to` is a reserved token in Lean, hence `compute`). Returns the assigned cell; adds no
constraint.

Deliberately single-cell, unlike main Clean's vector-valued `witness`: halo2's Region
API has no vector primitive, and the sharing that vector programs provide on the tape is
served here by later programs reading earlier cells (`.expr cellRef`). Multi-cell
assignment, if ever wanted, is DSL sugar over this op, not a new primitive. -/
def assignAdvice (col : Column .advice) (row : ℕ) (compute : WitgenIR F 1) :
    RegionCircuit F (AssignedCell F) :=
  fun self => (⟨⟨self, row, col⟩⟩, [.assignAdvice col row compute])

/-- Rust: `region.assign_fixed(col, offset, value)`. -/
def assignFixed (col : Column .fixed) (row : ℕ) (value : F) :
    RegionCircuit F (AssignedCell F) :=
  fun self => (⟨⟨self, row, col⟩⟩, [.assignFixed col row value])

/-- Copy an existing cell into this region: assign + copy constraint.
Rust: `assigned_cell.copy_advice(region, col, offset)`. -/
def copyAdvice (src : AssignedCell F) (col : Column .advice) (row : ℕ) :
    RegionCircuit F (AssignedCell F) :=
  fun self =>
    let cell : Cell := ⟨self, row, col⟩
    (⟨cell⟩, [
      .assignAdvice col row (.ofFExpr (.expr src)),
      .constrainEqual cell src.cell])

/-- Rust: `region.constrain_equal(a, b)`. -/
def constrainEqual (a b : AssignedCell F) : RegionCircuit F Unit :=
  fun _ => ((), [.constrainEqual a.cell b.cell])

/-- Rust: `region.constrain_constant(cell, value)`. -/
def constrainConstant (a : AssignedCell F) (value : F) : RegionCircuit F Unit :=
  fun _ => ((), [.constrainConstant a.cell value])

/-- Enable a gate at a local row (Rust: `selector.enable(region, offset)`): records the
selector activation and carries the gate's constraints. See `Operations.lean`. -/
def Gate.enable (gate : Gate F) (row : ℕ) : RegionCircuit F Unit :=
  fun _ => ((), [.enableGate gate row])

/-! ## Layouter-level circuits -/

/-- A layouter-level circuit: threads the next region index (like Clean's `offset`) and
accumulates layouter operations. -/
def Circuit (F : Type) [FiniteField F] (α : Type) :=
  RegionIndex → α × Operations F × RegionIndex

namespace Circuit

instance : Monad (Circuit F) where
  pure a := fun i => (a, [], i)
  bind x f := fun i =>
    let (a, ops, i') := x i
    let (b, ops', i'') := f a i'
    (b, ops ++ ops', i'')

/-- The operations of a circuit, from a given initial region index. -/
def operations (circuit : Circuit F α) (i : RegionIndex := 0) : Operations F :=
  (circuit i).2.1

/-- The output of a circuit, from a given initial region index. -/
def output (circuit : Circuit F α) (i : RegionIndex := 0) : α :=
  (circuit i).1

/-- The next free region index after running a circuit (the analogue of main Clean's
`offset + localLength`). -/
def nextRegionIndex (circuit : Circuit F α) (i : RegionIndex := 0) : RegionIndex :=
  (circuit i).2.2

end Circuit

/-- Create a region and run a region-level circuit inside it, allocating the next region
index. Rust: `layouter.assign_region(name, |region| …)`. -/
def assignRegion (name : String) (body : RegionCircuit F α) : Circuit F α :=
  fun i =>
    let (a, ops) := body i
    (a, [.region name ops], i + 1)

/-- Rust: `layouter.constrain_instance(cell, instance_col, row)`. -/
def constrainInstance (cell : AssignedCell F) (col : Column .instance) (row : ℕ) :
    Circuit F Unit :=
  fun i => ((), [.constrainInstance cell.cell col row], i)

/-- Satisfaction of a circuit, for a given placement of its regions
(including all subcircuit constraints, via flattening). Gadget proofs are generic
over `place` (and the initial region index); the final statement instantiates `place`
with the floor planner's output. -/
def Circuit.Constraints (place : RegionIndex → ℕ) (env : Environment F)
    (circuit : Circuit F α) : Prop :=
  Halo2.Constraints place env circuit.operations 0

end Halo2
