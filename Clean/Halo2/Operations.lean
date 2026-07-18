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
scale by isolating them from child circuit internals. Unlike main Clean (and per issue
Verified-zkEVM/clean#358), there is no `Subcircuit` type at all: a subcircuit call is
the `subcircuit` constructor carrying the child's operations, and the operation types
are **recursive** — which #358 unlocked, since main Clean's flat/structured split
exists only to let the `Subcircuit` package carry proofs about its ops without a
recursion knot. Consequences:

- There is a single ground-truth `Constraints` predicate. A subcircuit's constraints
  appear in parent hypotheses as one *opaque chunk* — `Constraints … <named child ops>`
  with the child ops folded behind the formal-circuit constant — never spilled into the
  parent's conjunction.
- The contracts (`Spec`/`Assumptions`/prover variants) live on the formal-circuit
  packages, which provide per-circuit *forward lemmas*
  (`Constraints chunk → (Assumptions → Spec)` for soundness; the reverse direction for
  completeness). A custom tactic applies them — rewriting hypotheses to the weaker but
  higher-level spec form, which simp fundamentally cannot do. This replaces main
  Clean's `ConstraintsHold.Soundness`/`.Completeness` predicate variants.
- Layouter-level subcircuits advance the region counter by their (computed, recursive)
  `regionCount`; region-level subcircuits live in the ambient region.
  TODO: the `SubcircuitsConsistent` discipline (cells in child ops reference the
  ambient region, by construction of the monad) ports with the formal-circuit layer.
  TODO: a `name` argument on `subcircuit` (like `region`'s) when serialization lands —
  subcircuit names are load-bearing for VK recovery.

Other key design points:

- **`enableGate` is itself subcircuit-like**: one operation that records the selector
  activation (for layout/VK compilation) *and* carries the gate's constraints (for
  semantics), so the semantics never needs the global `ConstraintSystem` threaded
  through. The bridge to the compiled CS's `∀ rows, guard·poly = 0` view is a
  once-per-circuit lemma at the VK boundary.
- **Assignments are witness-only**: `assignAdvice` creates a cell and its witness
  program (witgen IR over cell atoms; `.native` is the escape hatch); it adds no
  constraint. Copies and gate enables are the constraints.
- Lookups add no per-region operation: lookup arguments are CS-global and hold at every
  row. TODO: their satisfaction enters the top-level semantics with the lookup port.
- TODO: `assignAdviceFromInstance` (needed by the cross-address checks);
  `Requirements`-style well-formedness (row bounds, no double assignment).

Rust reference: `halo2_proofs/src/circuit.rs` (`Region`, `Layouter`, `Cell`).
-/

namespace Halo2

variable {F : Type}

/-- An operation inside a region, at region-local rows. Recursive: a `subcircuit` call
carries the child fragment's operations (sharing the caller's region). Consistency of
subcircuit cells with the ambient region (`SubcircuitsConsistent` in main Clean) is
maintained by the circuit monad and ported with the formal-circuit layer. -/
inductive RegionOperation (F : Type) where
  /-- Witness a value into an advice cell at a local row. Rust: `region.assign_advice`.
  Adds no constraint. -/
  | assignAdvice : Column .advice → ℕ → WitgenIR F 1 → RegionOperation F
  /-- Assign a fixed cell. Rust: `region.assign_fixed`. Pins the fixed column's value
  (fixed values are circuit data; the assignment is checked by the semantics and feeds
  the VK's fixed columns). -/
  | assignFixed : Column .fixed → ℕ → F → RegionOperation F
  /-- Enable a gate at a local row. Rust: `selector.enable(region, offset)`. Records the
  activation of `gate.selector` and carries `gate.constraints` for semantics. -/
  | enableGate : Gate F → ℕ → RegionOperation F
  /-- Enable a lookup argument at a local row (the dual of `enableGate`). There is no
  single Rust method: a gadget "enables a lookup at a row" by enabling the complex
  selector(s) its input expressions are gated on; in the port
  `enableLookup arg enabled row` is the sugar the gadget's `synthesize` emits alongside
  those `enable`s. Carries the registered `LookupArgument` (its input/table tuples) for
  semantics plus `enabled`, the selectors turned on at *this* row. Unlike a gate — whose
  polynomials only ever contain its own single selector — a lookup input's gating
  selectors genuinely vary per enabled row (range-check: `q_lookup = 1` at every
  participating row, but `q_running` is 1 only at running-sum rows and 0 at short rows,
  selecting *which* word is looked up — `lookup-design.md` §1.4). So the activation
  valuation is the per-row `enabled ↦ 1, rest ↦ 0`, not a fixed own-selector device. -/
  | enableLookup : LookupArgument F → List Selector → ℕ → RegionOperation F
  /-- Copy constraint between two (possibly cross-region) cells.
  Rust: `region.constrain_equal`. -/
  | constrainEqual : Cell → Cell → RegionOperation F
  /-- Copy constraint against the constants column. Rust: `region.constrain_constant`. -/
  | constrainConstant : Cell → F → RegionOperation F
  /-- Assign an advice cell from an instance-column value (absolute `row`) and constrain
  them equal. Rust: `region.assign_advice_from_instance` — an advice assignment plus the
  instance-left copy. -/
  | assignAdviceFromInstance : Column .instance → ℕ → Cell → RegionOperation F
  /-- A region-level subcircuit call: a packaged fragment's operations, in the ambient
  region. The proof boundary at row granularity. -/
  | subcircuit : List (RegionOperation F) → RegionOperation F

abbrev RegionOperations (F : Type) := List (RegionOperation F)

/-- A layouter-level operation: regions, instance copies, and layouter-level subcircuit
calls (recursive: the child gadget's operations). -/
inductive Operation (F : Type) where
  /-- A named region containing region-level operations. The region's index is not
  stored: like Clean's offsets, indices are recomputed by the semantics while folding. -/
  | region : String → RegionOperations F → Operation F
  /-- Copy constraint between a cell and an instance-column row.
  Rust: `layouter.constrain_instance`. -/
  | constrainInstance : Cell → Column .instance → ℕ → Operation F
  /-- Load a lookup table: fill a `TableColumn` (a fixed column) with `values` at absolute
  rows `[0, values.length)`, then default-fill every remaining usable row with the row-0
  value. Rust: `layouter.assign_table` (`table_layouter.rs`) + the floor planner's
  `fill_from_row` default-fill (`single_pass.rs:176-182`). Addresses absolute rows, so it
  is a layouter-level op, not a region op. See `lookup-design.md` §2.4. -/
  | loadTable : TableColumn → List F → Operation F
  /-- A layouter-level subcircuit call: a whole multi-region gadget's operations.
  The proof boundary at gadget granularity. -/
  | subcircuit : List (Operation F) → Operation F

abbrev Operations (F : Type) := List (Operation F)

/-- Number of region indices a list of operations consumes (the `localLength`
analogue) — computed, not cached; per-circuit lemmas evaluate it to a literal.
Counts through nested subcircuits. -/
def Operations.regionCount : Operations F → ℕ
  | [] => 0
  | .region _ _ :: ops => 1 + Operations.regionCount ops
  | .subcircuit ops' :: ops => Operations.regionCount ops' + Operations.regionCount ops
  | .constrainInstance _ _ _ :: ops => Operations.regionCount ops
  | .loadTable _ _ :: ops => Operations.regionCount ops

section Semantics
variable [FiniteField F]

/-- Read a (possibly foreign) cell. `@[circuit_norm]` (mirroring `AssignedCell.eval`): copy
constraints carry `Cell.eval`, so this reduces them to the shared `env.get` row form and
they line up with the query/assigned-cell paths without a manual unfold. -/
@[circuit_norm]
def Cell.eval (place : RegionIndex → ℕ) (env : Environment F) (c : Cell) : F :=
  env.get c.column ((place c.regionIndex + c.rowOffset : ℕ) : ℤ)

mutual

/-- Constraints of one region operation, for a region with index `self`. For a
subcircuit call this is the *opaque chunk* over the child's named op list — the proof
boundary: parent hypotheses keep the chunk folded, and the per-circuit forward lemmas
(formal-circuit layer) rewrite it to the child's `Assumptions → Spec`. -/
def RegionOperation.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperation F → Prop
  | .assignAdvice _ _ _ => True
  | .assignFixed col row v => env.get col (place self + row : ℕ) = v
  | .enableGate gate row =>
      -- compiled polys vanish under `own selector ↦ 1`; sound because genuine selectors
      -- never occur in a foreign gate's polynomials (see halo2-selector-survey.md).
      -- `List.Forall` (not `∀ c ∈ …`) so `circuit_norm` reduces it to a clean conjunction.
      gate.constraints.Forall fun c =>
        c.poly.eval (Query.eval env (fun i => if i = gate.selector.index then 1 else 0)
          (place self + row : ℕ)) = 0
  | .enableLookup arg enabled row =>
      -- membership (not permutation): the input tuple at this row equals the table tuple
      -- at *some* usable table row (`lookup-design.md` §2.2). The witness is bounded by
      -- `env.usableRows` for faithfulness: the prover truncates the input expression and
      -- builds the table multiset over `usable_rows = n − (blinding + 1)` only
      -- (`lookup/prover.rs:573-585`), so blinding rows never participate on either side.
      -- ℕ-with-cast spelling: table rows share the `(↑(n : ℕ) : ℤ)` row normal form of
      -- all other reads. Inputs are evaluated under the local activation valuation
      -- `enabled ↦ 1, rest ↦ 0` — which selectors are on at this row decides *which* word
      -- the gated input expression reduces to (running-sum vs short row, §1.4); the table
      -- side is a rotation-0 fixed query, unaffected by the valuation.
      ∃ tableRow : ℕ, tableRow < env.usableRows ∧
        arg.inputs.map (Expression.eval (Query.eval env
          (fun i => if i ∈ enabled.map Selector.index then 1 else 0) (place self + row : ℕ)))
        = arg.tables.map (Expression.eval (Query.eval env
          (fun i => if i ∈ enabled.map Selector.index then 1 else 0) (tableRow : ℤ)))
  | .constrainEqual a b => a.eval place env = b.eval place env
  | .constrainConstant a v => a.eval place env = v
  | .assignAdviceFromInstance instCol instRow cell =>
      cell.eval place env = env.get instCol (instRow : ℤ)
  | .subcircuit ops => RegionOperations.Constraints place self env ops

/-- Constraints of a list of region operations. -/
def RegionOperations.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperations F → Prop
  | [] => True
  | op :: ops =>
      op.Constraints place self env ∧ RegionOperations.Constraints place self env ops

end

/--
Ground truth: what it means that "constraints hold" on a sequence of operations,
*including* all constraints inside subcircuits. The single satisfaction predicate
(issue #358 — no separate `Soundness`/`Completeness` views): `place` is the region
placement (the analogue of main Clean's `offset`, instantiated at top level with the
floor planner's output), `i` the index of the next region (threaded like Clean's
offset); subcircuits contribute their constraints as one opaque chunk, advancing the
region counter by their `regionCount`.
-/
def Constraints (place : RegionIndex → ℕ) (env : Environment F) :
    Operations F → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops' :: ops, i =>
      ops'.Constraints place i env ∧ Constraints place env ops (i + 1)
  | .constrainInstance cell col row :: ops, i =>
      cell.eval place env = env.get col row ∧ Constraints place env ops i
  | .loadTable tbl values :: ops, i =>
      -- explicit block: rows `[0, values.length)` hold the loaded values
      (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
      -- default-fill (`lookup-design.md` §1.3.1): unused usable rows carry the row-0 value.
      -- Conditional on `values ≠ []` so an empty load imposes no bogus default.
      (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
        env.fixed tbl.inner (r : ℤ) = values[0]!) ∧
      Constraints place env ops i
  | .subcircuit ops' :: ops, i =>
      Constraints place env ops' i ∧ Constraints place env ops (i + Operations.regionCount ops')

mutual

/-- The witness condition for completeness: the environment assigns each advice cell
the value computed by its witness program (main Clean: `ExtendsVector`), and each fixed
cell the value the circuit assigns. The `assignFixed` clause mirrors its `Constraints`
equation — like `loadTable`'s witness clause (`ExtendsWitnesses` below): fixed-column
contents are circuit data the honest environment carries, so a completeness proof can
discharge the corresponding constraint (they are keygen-time assignments, not prover
witness choices). -/
def RegionOperation.ExtendsWitness (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : RegionOperation F → Prop
  | .assignAdvice col row compute =>
      env.get col (place self + row : ℕ) = (compute.eval ⟨place, env⟩)[0]
  | .assignFixed col row v => env.get col (place self + row : ℕ) = v
  | .assignAdviceFromInstance instCol instRow cell =>
      cell.eval place env.toEnvironment = env.get instCol (instRow : ℤ)
  | .subcircuit ops => RegionOperations.ExtendsWitnesses place self env ops
  | _ => True

/-- Witness condition for a list of region operations. -/
def RegionOperations.ExtendsWitnesses (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : RegionOperations F → Prop
  | [] => True
  | op :: ops =>
      op.ExtendsWitness place self env ∧ RegionOperations.ExtendsWitnesses place self env ops

end

/-- All-regions witness condition, threading the region counter like `Constraints`. -/
def ExtendsWitnesses (place : RegionIndex → ℕ) (env : ProverEnvironment F) :
    Operations F → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops' :: ops, i =>
      ops'.ExtendsWitnesses place i env ∧ ExtendsWitnesses place env ops (i + 1)
  | .constrainInstance _ _ _ :: ops, i => ExtendsWitnesses place env ops i
  | .loadTable tbl values :: ops, i =>
      -- The honest prover's environment holds exactly that column content: the explicit
      -- block plus the row-0 default-fill over the usable rows. Discharges the `loadTable`
      -- `Constraints` in the completeness proof of a table loader. See `lookup-design.md` §2.4.
      (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
      (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
        env.fixed tbl.inner (r : ℤ) = values[0]!) ∧
      ExtendsWitnesses place env ops i
  | .subcircuit ops' :: ops, i =>
      ExtendsWitnesses place env ops' i ∧ ExtendsWitnesses place env ops (i + Operations.regionCount ops')
end Semantics

end Halo2
