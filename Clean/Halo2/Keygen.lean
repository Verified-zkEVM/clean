module

public import Clean.Halo2.Keygen.RichExpression
public import Clean.Halo2.Keygen.CompressSelectors
public import Clean.Halo2.Keygen.FloorPlanner.ConstantAllocation
public import Clean.Halo2.Keygen.FloorPlanner.Simple
public import Clean.Halo2.Keygen.FloorPlanner.V1SortCorrectness
public import Clean.Halo2.Keygen.PdqsortCorrectness
public import Clean.Halo2.Keygen.PlannerTrace
public import Clean.Halo2.Keygen.Projection
public import Clean.Halo2.Keygen.PinnedCs
public import Clean.Halo2.Keygen.Domain
public import Clean.Halo2.Keygen.Semantics
public import Clean.Halo2.Keygen.Layout
public import Clean.Halo2.Keygen.GateProjection

@[expose] public section

/-!
# Halo2 keygen — the circuit-side half of `keygen_vk`

Aggregator for the pinned-constraint-system derivation: the pure Clean-data processing that
turns a circuit's configure/synthesize output into halo2's `PinnedConstraintSystem` — floor
plan → activations → minimal fitting domain → `compress_selectors` → pinned record.

* `RichExpression` — the pinned/verifier gate AST (query-index space).
* `CompressSelectors` — the `SelCompressMap` derivation and its root-finding algebra.
* `FloorPlanner` — the V1 floor planner (region placement from the operation stream).
* `PlannerTrace` — reusable compact-trace and repeated-shape reasoning.
* `Projection` — the query-index walk erasing `Expression F Query` into `RichExpression F`.
* `PinnedCs` — `PinnedConstraintSystem` and `.derive`.
* `Semantics` — the projection preserves evaluation (`derive_gates_eval`).
* `Layout` — the keygen layout semantics: floor-planner copy lists, the keygen
  `Assembly` (σ) replay, and fixed-column contents (tables, region assignments,
  packed selectors).
* `GateProjection` — selector-compressed gate algebra: the verifier-side gate
  polynomial as a packed-selector scale of Clean's enabled-gate evaluation.
-/
