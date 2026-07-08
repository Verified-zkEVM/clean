import Clean.Halo2.Configure
import Clean.Halo2.Provable

/-!
# Halo2 synthesize-layer operations — DESIGN SKETCH

Port of the operation layer of `Clean/Circuit/Operations.lean` to halo2. Two levels of
operations, mirroring Rust's two synthesize APIs:

- Region level (Rust `Region<F>` methods): assignments, copies, gate enables — all at
  region-local rows. Region-level gadget composition (e.g.
  `add_incomplete.assign_region(…, offset, region)` called inside variable-base mul's
  big region) is row-offset-shifted, exactly Clean's offset-generic subcircuit pattern
  at row granularity.
- Layouter level (Rust `Layouter<F>`): creating regions, instance-column copies.
  Regions get indices from a threaded counter (prefix-computable, like Clean's offset);
  their *placement* `place : RegionIndex → ℕ` is a semantics parameter, computed at top
  level by the floor planner.

**The subcircuit mechanism** is ported from main Clean at *both* levels — it is what
makes parent proofs scale by isolating them from child circuit internals:

- `Flat*Operation` are the raw operations; `*Operation` additionally have a
  `subcircuit` constructor carrying a proof package (`RegionSubcircuit` / `Subcircuit`)
  whose `ops` are *flattened* child operations (as in main Clean, this is what avoids
  recursion between the op type and the package).
- The ground-truth predicate `Constraints` recurses through subcircuits (via
  flattening); the `Constraints.Soundness` variant replaces a subcircuit by
  `Assumptions → Spec`, and `Constraints.Completeness` by `ProverAssumptions` — parents
  never see child internals.
- Layouter-level subcircuits advance the region counter by their `regionCount` (the
  `localLength` analogue); region-level subcircuits live in the ambient region.
  TODO: the `SubcircuitsConsistent` discipline (stored index = ambient index, by
  construction of the monad) ports with the formal-circuit layer.

Other key design points:

- **`enableGate` is itself subcircuit-like**: one operation that records the selector
  activation (for layout/VK compilation) *and* carries the gate's constraints (for
  semantics), so the semantics never needs the global `ConstraintSystem` threaded
  through. The bridge to the compiled CS's `∀ rows, guard·poly = 0` view is a
  once-per-circuit lemma at the VK boundary.
- **Assignments are witness-only**: `assignAdvice` creates a cell and its witness
  program; it adds no constraint. Copies and gate enables are the constraints.
- Lookups add no per-region operation: lookup arguments are CS-global and hold at every
  row. TODO: their satisfaction enters the top-level semantics with the lookup port.
- TODO: witness programs via the shared witgen IR (plain functions for now);
  `assignAdviceFromInstance` (needed by the cross-address checks);
  `Requirements`-style well-formedness (row bounds, no double assignment).

Rust reference: `halo2_proofs/src/circuit.rs` (`Region`, `Layouter`, `Cell`).
-/

namespace Halo2

variable {F : Type}

/-! ## Flat operations (no subcircuit nesting) -/

/-- A raw operation inside a region, at region-local rows.

Witness computations take a `Placed ProverEnvironment` (they may read other cells, which
requires the placement). SKETCH: plain functions until the witgen IR hookup. -/
inductive FlatRegionOperation (F : Type) where
  /-- Witness a value into an advice cell at a local row. Rust: `region.assign_advice`.
  Adds no constraint. -/
  | assignAdvice : Column .advice → ℕ → (Placed ProverEnvironment F → F) → FlatRegionOperation F
  /-- Assign a fixed cell. Rust: `region.assign_fixed`. Pins the fixed column's value
  (fixed values are circuit data; the assignment is checked by the semantics and feeds
  the VK's fixed columns). -/
  | assignFixed : Column .fixed → ℕ → F → FlatRegionOperation F
  /-- Enable a gate at a local row. Rust: `selector.enable(region, offset)`. Records the
  activation of `gate.selector` and carries `gate.constraints` for semantics. -/
  | enableGate : Gate F → ℕ → FlatRegionOperation F
  /-- Copy constraint between two (possibly cross-region) cells.
  Rust: `region.constrain_equal`. -/
  | constrainEqual : Cell → Cell → FlatRegionOperation F
  /-- Copy constraint against the constants column. Rust: `region.constrain_constant`. -/
  | constrainConstant : Cell → F → FlatRegionOperation F

/-- A raw layouter-level operation. -/
inductive FlatOperation (F : Type) where
  /-- A named region containing raw region-level operations. The region's index is not
  stored: like Clean's offsets, indices are recomputed by the semantics while folding. -/
  | region : String → List (FlatRegionOperation F) → FlatOperation F
  /-- Copy constraint between a cell and an instance-column row.
  Rust: `layouter.constrain_instance`. -/
  | constrainInstance : Cell → Column .instance → ℕ → FlatOperation F

/-! ## Ground-truth semantics of flat operations -/

section FlatSemantics
variable [Field F]

/-- Read a (possibly foreign) cell. -/
def Cell.eval (place : RegionIndex → ℕ) (env : Environment F) (c : Cell) : F :=
  env.get c.column ((place c.regionIndex + c.rowOffset : ℕ) : ℤ)

/-- Semantics of one raw region operation, for a region with index `self`. -/
def FlatRegionOperation.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : FlatRegionOperation F → Prop
  | .assignAdvice _ _ _ => True
  | .assignFixed c row v => env.get c.toAny ((place self + row : ℕ) : ℤ) = v
  | .enableGate gate row => ∀ c ∈ gate.constraints,
      -- compiled polys vanish under `own selector ↦ 1`; sound because genuine selectors
      -- never occur in a foreign gate's polynomials (see halo2-selector-survey.md)
      c.poly.eval (Query.eval env (fun i => if i = gate.selector.index then 1 else 0)
        ((place self + row : ℕ) : ℤ)) = 0
  | .constrainEqual a b => a.eval place env = b.eval place env
  | .constrainConstant a v => a.eval place env = v

/-- Ground-truth semantics of raw layouter operations: `place` is the region placement
(the analogue of main Clean's `offset`, instantiated at top level with the floor
planner's output), `i` the index of the next region (threaded like Clean's offset). -/
def ConstraintsFlat (place : RegionIndex → ℕ) (env : Environment F) :
    List (FlatOperation F) → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops :: rest, i =>
      (∀ op ∈ ops, op.Constraints place i env) ∧ ConstraintsFlat place env rest (i + 1)
  | .constrainInstance c col row :: rest, i =>
      c.eval place env = env.get col.toAny row ∧ ConstraintsFlat place env rest i

/-- The witness condition for completeness: the environment assigns each advice cell
the value computed by its witness program (main Clean: `ExtendsVector`). -/
def FlatRegionOperation.ExtendsWitness (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : FlatRegionOperation F → Prop
  | .assignAdvice c row compute =>
      env.get c.toAny ((place self + row : ℕ) : ℤ) = compute ⟨place, env⟩
  | _ => True

/-- All-regions witness condition for raw layouter operations. -/
def ExtendsWitnessesFlat (place : RegionIndex → ℕ) (env : ProverEnvironment F) :
    List (FlatOperation F) → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops :: rest, i =>
      (∀ op ∈ ops, op.ExtendsWitness place i env) ∧ ExtendsWitnessesFlat place env rest (i + 1)
  | .constrainInstance _ _ _ :: rest, i => ExtendsWitnessesFlat place env rest i

end FlatSemantics

/-! ## Subcircuits: the proof boundary -/

section Subcircuits
variable [Field F]

/--
A region-level subcircuit: a fragment used *inside* a region (e.g. `add_incomplete`'s
`assign_region` method called at an offset inside variable-base mul's big region),
packaged with its contract. Port of main Clean's `Subcircuit` at row granularity.

Like main Clean, `ops` are the flattened child operations, and the statements are
env-level `Prop`s (the input/output-typed view is layered on by the formal-circuit
package, which instantiates them at concrete cells).

`self` is the region this fragment lives in (the analogue of main Clean's `offset`
index): the fragment shares its caller's region.
-/
structure RegionSubcircuit (F : Type) [Field F] (self : RegionIndex) where
  ops : List (FlatRegionOperation F)

  Assumptions : (RegionIndex → ℕ) → Environment F → Prop
  Spec : (RegionIndex → ℕ) → Environment F → Prop
  ProverAssumptions : (RegionIndex → ℕ) → ProverEnvironment F → Prop
  ProverSpec : (RegionIndex → ℕ) → ProverEnvironment F → Prop

  /-- Rows this fragment uses within the region, from its base offset (part of the
  region's shape for the floor planner). TODO consistency field, like `localLength_eq`. -/
  usedRows : ℕ

  soundness : ∀ place env,
    Assumptions place env →
    (∀ op ∈ ops, op.Constraints place self env) →
    Spec place env

  completeness : ∀ place (env : ProverEnvironment F),
    (∀ op ∈ ops, op.ExtendsWitness place self env) →
    (ProverAssumptions place env →
      ∀ op ∈ ops, op.Constraints place self env.toEnvironment) ∧
    ProverSpec place env

/--
A layouter-level subcircuit: a whole multi-region gadget (e.g. ECC mul), packaged with
its contract. Port of main Clean's `Subcircuit`; `i₀` is the region index it is
instantiated at, and `regionCount` (the `localLength` analogue) is how many region
indices it consumes.
-/
structure Subcircuit (F : Type) [Field F] (i₀ : RegionIndex) where
  ops : List (FlatOperation F)

  Assumptions : (RegionIndex → ℕ) → Environment F → Prop
  Spec : (RegionIndex → ℕ) → Environment F → Prop
  ProverAssumptions : (RegionIndex → ℕ) → ProverEnvironment F → Prop
  ProverSpec : (RegionIndex → ℕ) → ProverEnvironment F → Prop

  /-- Number of regions created by `ops` — recorded separately for fast simplification,
  like main Clean's `localLength`. -/
  regionCount : ℕ

  soundness : ∀ place env,
    Assumptions place env →
    ConstraintsFlat place env ops i₀ →
    Spec place env

  completeness : ∀ place (env : ProverEnvironment F),
    ExtendsWitnessesFlat place env ops i₀ →
    (ProverAssumptions place env →
      ConstraintsFlat place env.toEnvironment ops i₀) ∧
    ProverSpec place env

  /-- `regionCount` must be consistent with the operations. -/
  regionCount_eq : regionCount = (ops.filter fun op => match op with
    | .region _ _ => true | _ => false).length

end Subcircuits

/-! ## Structured operations -/

/-- An operation inside a region: the raw operations plus region-level subcircuit
calls. The subcircuit's region index is its type index; consistency with the ambient
region (`SubcircuitsConsistent` in main Clean) is maintained by the circuit monad and
ported with the formal-circuit layer. -/
inductive RegionOperation (F : Type) [Field F] where
  | assignAdvice : Column .advice → ℕ → (Placed ProverEnvironment F → F) → RegionOperation F
  | assignFixed : Column .fixed → ℕ → F → RegionOperation F
  | enableGate : Gate F → ℕ → RegionOperation F
  | constrainEqual : Cell → Cell → RegionOperation F
  | constrainConstant : Cell → F → RegionOperation F
  | subcircuit : {self : RegionIndex} → RegionSubcircuit F self → RegionOperation F

/-- A layouter-level operation: regions (with structured bodies), instance copies, and
layouter-level subcircuit calls. -/
inductive Operation (F : Type) [Field F] where
  | region : String → List (RegionOperation F) → Operation F
  | constrainInstance : Cell → Column .instance → ℕ → Operation F
  | subcircuit : {i₀ : RegionIndex} → Subcircuit F i₀ → Operation F

section StructuredSemantics
variable [Field F]

/-- Flatten a region operation (subcircuits contribute their flattened ops). -/
def RegionOperation.toFlat : RegionOperation F → List (FlatRegionOperation F)
  | .assignAdvice c r w => [.assignAdvice c r w]
  | .assignFixed c r v => [.assignFixed c r v]
  | .enableGate g r => [.enableGate g r]
  | .constrainEqual a b => [.constrainEqual a b]
  | .constrainConstant a v => [.constrainConstant a v]
  -- explicit projection: dot notation misresolves on the dependent pattern here
  | .subcircuit s => RegionSubcircuit.ops s

/-- Flatten a layouter operation. -/
def Operation.toFlat : Operation F → List (FlatOperation F)
  | .region name ops => [.region name (ops.flatMap RegionOperation.toFlat)]
  | .constrainInstance c col row => [.constrainInstance c col row]
  | .subcircuit s => s.ops

/--
Ground truth: what it means that "constraints hold" on a sequence of operations,
*including* all constraints inside subcircuits (via flattening). Region-index
bookkeeping is preserved by flattening because a subcircuit's `regionCount` matches the
regions its ops create.
-/
def Constraints (place : RegionIndex → ℕ) (env : Environment F)
    (ops : List (Operation F)) (i : RegionIndex := 0) : Prop :=
  ConstraintsFlat place env (ops.flatMap Operation.toFlat) i

/-- Soundness view of one region operation: subcircuits contribute `Assumptions → Spec`
instead of their constraints — this is the isolation that keeps parent proofs
independent of child internals. -/
def RegionOperation.Soundness (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperation F → Prop
  | .subcircuit s => RegionSubcircuit.Assumptions s place env → RegionSubcircuit.Spec s place env
  | op => ∀ flat ∈ op.toFlat, flat.Constraints place self env

/-- Soundness view of layouter operations (main Clean: `ConstraintsHold.Soundness`). -/
def Constraints.Soundness (place : RegionIndex → ℕ) (env : Environment F) :
    List (Operation F) → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops :: rest, i =>
      (∀ op ∈ ops, op.Soundness place i env) ∧ Constraints.Soundness place env rest (i + 1)
  | .constrainInstance c col row :: rest, i =>
      c.eval place env = env.get col.toAny row ∧ Constraints.Soundness place env rest i
  | .subcircuit s :: rest, i =>
      (s.Assumptions place env → s.Spec place env) ∧
        Constraints.Soundness place env rest (i + s.regionCount)

/-- Completeness view of one region operation: subcircuits contribute their
`ProverAssumptions` (which the parent must establish; the child's completeness proof
turns them into satisfied constraints). -/
def RegionOperation.Completeness (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : RegionOperation F → Prop
  | .subcircuit s => RegionSubcircuit.ProverAssumptions s place env
  | op => ∀ flat ∈ op.toFlat, flat.Constraints place self env.toEnvironment

/-- Completeness view of layouter operations (main Clean: `ConstraintsHold.Completeness`). -/
def Constraints.Completeness (place : RegionIndex → ℕ) (env : ProverEnvironment F) :
    List (Operation F) → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops :: rest, i =>
      (∀ op ∈ ops, op.Completeness place i env) ∧ Constraints.Completeness place env rest (i + 1)
  | .constrainInstance c col row :: rest, i =>
      c.eval place env.toEnvironment = env.toEnvironment.get col.toAny row ∧
        Constraints.Completeness place env rest i
  | .subcircuit s :: rest, i =>
      s.ProverAssumptions place env ∧ Constraints.Completeness place env rest (i + s.regionCount)

end StructuredSemantics

end Halo2
