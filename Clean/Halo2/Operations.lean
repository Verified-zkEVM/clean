import Clean.Halo2.Configure
import Clean.Halo2.Provable
import Clean.Halo2.WitnessIR

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

**The subcircuit mechanism** exists at *both* levels — it is what makes parent proofs
scale by isolating them from child circuit internals. Unlike main Clean's `Subcircuit`
(and per issue Verified-zkEVM/clean#358), the packages are **thin data**: flattened
child ops plus size metadata, with no `Spec`/`Assumptions` fields and no stored proofs:

- `Flat*Operation` are the raw operations; `*Operation` additionally have a
  `subcircuit` constructor carrying `RegionSubcircuit` / `Subcircuit` (flattened child
  ops — as in main Clean, flatness avoids recursion between op type and package).
- There is a single ground-truth `Constraints` predicate. A subcircuit's constraints
  appear in parent hypotheses as one *opaque chunk* over the child's named `ops`
  (`∀ op ∈ C.subcircuit(…).ops, …`), never spilled into the parent's conjunction.
- The contracts (`Spec`/`Assumptions`/prover variants) live on the formal-circuit
  packages, which provide per-circuit *forward lemmas*
  (`Constraints chunk → (Assumptions → Spec)` for soundness; the reverse direction for
  completeness). A custom tactic applies them — rewriting hypotheses to the weaker but
  higher-level spec form, which simp fundamentally cannot do. This replaces main
  Clean's `ConstraintsHold.Soundness`/`.Completeness` predicate variants.
- Layouter-level subcircuits advance the region counter by their `regionCount` (the
  `localLength` analogue); region-level subcircuits live in the ambient region.
  TODO: the `SubcircuitsConsistent` discipline (cells in child ops reference the
  ambient region, by construction of the monad) ports with the formal-circuit layer.

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

Witness values are witgen-IR programs over cell atoms (`Halo2.WitgenIR F 1`), the same
exportable mechanism as main Clean; `.native` remains the non-serializable escape
hatch. -/
inductive FlatRegionOperation (F : Type) where
  /-- Witness a value into an advice cell at a local row. Rust: `region.assign_advice`.
  Adds no constraint. -/
  | assignAdvice : Column .advice → ℕ → WitgenIR F 1 → FlatRegionOperation F
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
variable [FiniteField F]

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
      env.get c.toAny ((place self + row : ℕ) : ℤ) = (compute.eval ⟨place, env⟩)[0]
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
variable [FiniteField F]

/--
A region-level subcircuit: a fragment used *inside* a region (e.g. `add_incomplete`'s
`assign_region` method called at an offset inside variable-base mul's big region).

Thin data (issue #358): flattened child operations plus shape metadata — the contract
and its proofs live on the formal-circuit package, connected by per-circuit forward
lemmas. The fragment shares its caller's region; cells in `ops` referencing the ambient
region is a wellformedness condition maintained by the circuit monad.
-/
structure RegionSubcircuit (F : Type) where
  ops : List (FlatRegionOperation F)
  /-- Rows this fragment uses within the region, from its base offset (part of the
  region's shape for the floor planner). TODO consistency field, like `localLength_eq`. -/
  usedRows : ℕ

/--
A layouter-level subcircuit: a whole multi-region gadget (e.g. ECC mul). Thin data
(issue #358); `regionCount` (the `localLength` analogue) is how many region indices the
ops consume, recorded separately for fast simplification.
-/
structure Subcircuit (F : Type) where
  ops : List (FlatOperation F)
  regionCount : ℕ
  /-- `regionCount` must be consistent with the operations. -/
  regionCount_eq : regionCount = (ops.filter fun op => match op with
    | .region _ _ => true | _ => false).length

end Subcircuits

/-! ## Structured operations -/

/-- An operation inside a region: the raw operations plus region-level subcircuit
calls. Consistency of subcircuit cells with the ambient region (`SubcircuitsConsistent`
in main Clean) is maintained by the circuit monad and ported with the formal-circuit
layer. -/
inductive RegionOperation (F : Type) where
  | assignAdvice : Column .advice → ℕ → WitgenIR F 1 → RegionOperation F
  | assignFixed : Column .fixed → ℕ → F → RegionOperation F
  | enableGate : Gate F → ℕ → RegionOperation F
  | constrainEqual : Cell → Cell → RegionOperation F
  | constrainConstant : Cell → F → RegionOperation F
  | subcircuit : RegionSubcircuit F → RegionOperation F

/-- A layouter-level operation: regions (with structured bodies), instance copies, and
layouter-level subcircuit calls. -/
inductive Operation (F : Type) where
  | region : String → List (RegionOperation F) → Operation F
  | constrainInstance : Cell → Column .instance → ℕ → Operation F
  | subcircuit : Subcircuit F → Operation F

section StructuredSemantics
variable [FiniteField F]

/-- Flatten a region operation (subcircuits contribute their flattened ops). -/
def RegionOperation.toFlat : RegionOperation F → List (FlatRegionOperation F)
  | .assignAdvice c r w => [.assignAdvice c r w]
  | .assignFixed c r v => [.assignFixed c r v]
  | .enableGate g r => [.enableGate g r]
  | .constrainEqual a b => [.constrainEqual a b]
  | .constrainConstant a v => [.constrainConstant a v]
  | .subcircuit s => s.ops

/-- Flatten a layouter operation. -/
def Operation.toFlat : Operation F → List (FlatOperation F)
  | .region name ops => [.region name (ops.flatMap RegionOperation.toFlat)]
  | .constrainInstance c col row => [.constrainInstance c col row]
  | .subcircuit s => s.ops

/-- Constraints of one region operation. For a subcircuit call this is the *opaque
chunk* `∀ f ∈ s.ops, …` over the child's named op list — the proof boundary: parent
hypotheses keep the chunk folded, and the per-circuit forward lemmas (formal-circuit
layer) rewrite it to the child's `Assumptions → Spec`. -/
def RegionOperation.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) (op : RegionOperation F) : Prop :=
  ∀ flat ∈ op.toFlat, flat.Constraints place self env

/--
Ground truth: what it means that "constraints hold" on a sequence of operations,
*including* all constraints inside subcircuits. The single satisfaction predicate
(issue #358 — no separate `Soundness`/`Completeness` views): layouter-level subcircuits
contribute their constraints as one opaque `ConstraintsFlat … s.ops` chunk, advancing
the region counter by `regionCount`.

TODO (formal-circuit layer): the flattening equivalence
`Constraints place env ops i ↔ ConstraintsFlat place env (ops.flatMap Operation.toFlat) i`.
-/
def Constraints (place : RegionIndex → ℕ) (env : Environment F) :
    List (Operation F) → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops :: rest, i =>
      (∀ op ∈ ops, op.Constraints place i env) ∧ Constraints place env rest (i + 1)
  | .constrainInstance c col row :: rest, i =>
      c.eval place env = env.get col.toAny row ∧ Constraints place env rest i
  | .subcircuit s :: rest, i =>
      ConstraintsFlat place env s.ops i ∧ Constraints place env rest (i + s.regionCount)

end StructuredSemantics

end Halo2
