import Clean.Halo2.Configure
import Clean.Halo2.Provable

/-!
# Halo2 synthesize-layer operations — DESIGN SKETCH

Port of the operation layer of `Clean/Circuit/Operations.lean` to halo2. Two levels of
operations, mirroring Rust's two synthesize APIs:

- `RegionOperation`: what happens *inside* one region (Rust `Region<F>` methods):
  assignments, copies, gate enables — all at region-local rows. Region-level gadget
  composition (e.g. `add_incomplete.assign_region(…, offset, region)` called inside
  variable-base mul's big region) is row-offset-shifted, exactly Clean's offset-generic
  subcircuit pattern at row granularity.
- `Operation`: the layouter level (Rust `Layouter<F>`): creating regions and
  instance-column copies. Regions get indices from a threaded counter
  (prefix-computable, like Clean's offset); their *placement* `place : RegionIndex → ℕ`
  is a semantics parameter, computed at top level by the floor planner.

Key design points:

- **`enableGate` is a subcircuit-style call**: one operation that records the selector
  activation (for layout/VK compilation) *and* carries the gate's constraints (for
  semantics), so `ConstraintsHold` never needs the global `ConstraintSystem` threaded
  through. The bridge to the compiled CS's `∀ rows, guard·poly = 0` view is a
  once-per-circuit lemma at the VK boundary.
- **Assignments are witness-only**: `assignAdvice` creates a cell and its witness
  program; it adds no constraint. Copies (`constrainEqual`, `constrainConstant`,
  `constrainInstance`) and gate enables are the constraints.
- Lookups add no per-region operation: lookup arguments are CS-global and hold at every
  row. TODO: their satisfaction enters the top-level semantics with the lookup port.

TODO (deferred to the formal-circuit port):
- subcircuit/proof-boundary operation with soundness/completeness packaging,
- witness programs via the shared witgen IR (plain functions for now),
- `Requirements`-style well-formedness (row bounds, no double assignment, simple
  selector rules).

Rust reference: `halo2_proofs/src/circuit.rs` (`Region`, `Layouter`, `Cell`).
-/

namespace Halo2

variable {F : Type}

/-- An operation inside a region, at region-local rows.

Witness computations take a `Placed ProverEnvironment` (they may read other cells, which
requires the placement). SKETCH: plain functions until the witgen IR is generalized. -/
inductive RegionOperation (F : Type) where
  /-- Witness a value into an advice cell at a local row. Rust: `region.assign_advice`.
  Adds no constraint. -/
  | assignAdvice : Column .advice → ℕ → (Placed ProverEnvironment F → F) → RegionOperation F
  /-- Assign a fixed cell. Rust: `region.assign_fixed`. Pins the fixed column's value
  (fixed values are circuit data; the assignment is checked by the semantics and feeds
  the VK's fixed columns). -/
  | assignFixed : Column .fixed → ℕ → F → RegionOperation F
  /-- Enable a gate at a local row. Rust: `selector.enable(region, offset)`. Records the
  activation of `gate.guard`'s selector and carries `gate.constraints` for semantics. -/
  | enableGate : Gate F → ℕ → RegionOperation F
  /-- Copy constraint between two (possibly cross-region) cells.
  Rust: `region.constrain_equal`. -/
  | constrainEqual : Cell → Cell → RegionOperation F
  /-- Copy constraint against the constants column. Rust: `region.constrain_constant`. -/
  | constrainConstant : Cell → F → RegionOperation F

/-- A layouter-level operation. -/
inductive Operation (F : Type) where
  /-- A named region containing region-level operations. The region's index is not
  stored: like Clean's offsets, indices are recomputed by the semantics while folding
  (see `ConstraintsHold`). -/
  | region : String → List (RegionOperation F) → Operation F
  /-- Copy constraint between a cell and an instance-column row.
  Rust: `layouter.constrain_instance`. -/
  | constrainInstance : Cell → Column .instance → ℕ → Operation F

section Semantics
variable [Field F]

/-- Read a (possibly foreign) cell. -/
@[circuit_norm]
def Cell.eval (place : RegionIndex → ℕ) (env : Environment F) (c : Cell) : F :=
  env.get c.column ((place c.regionIndex + c.rowOffset : ℕ) : ℤ)

/--
Semantics of one region operation, for a region with index `self`, given the placement.
-/
@[circuit_norm]
def RegionOperation.Holds (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperation F → Prop
  | .assignAdvice _ _ _ => True
  | .assignFixed c row v => env.get c.toAny ((place self + row : ℕ) : ℤ) = v
  | .enableGate gate row => ∀ c ∈ gate.constraints,
      c.poly.eval (Query.eval env (fun _ => 1) ((place self + row : ℕ) : ℤ)) = 0
  | .constrainEqual a b => a.eval place env = b.eval place env
  | .constrainConstant a v => a.eval place env = v

/--
Semantics of a layouter-level operation list: `place` is the region placement (the
analogue of main Clean's `offset`, instantiated at top level with the floor planner's
output), `i` the index of the next region (threaded like Clean's offset).

SKETCH: main Clean distinguishes soundness/completeness variants of `ConstraintsHold`
and factors per-op semantics through subcircuit interfaces; that structure arrives with
the formal-circuit port.
-/
@[circuit_norm]
def ConstraintsHold (place : RegionIndex → ℕ) (env : Environment F) :
    List (Operation F) → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops :: rest, i =>
      (∀ op ∈ ops, op.Holds place i env) ∧ ConstraintsHold place env rest (i + 1)
  | .constrainInstance c col row :: rest, i =>
      c.eval place env = env.get col.toAny row ∧ ConstraintsHold place env rest i

end Semantics

end Halo2
