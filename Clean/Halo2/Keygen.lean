import Clean.Halo2.Keygen.RichExpression
import Clean.Halo2.Keygen.CompressSelectors
import Clean.Halo2.Keygen.FloorPlanner
import Clean.Halo2.Keygen.Projection
import Clean.Halo2.Keygen.PinnedCs
import Clean.Halo2.Keygen.Semantics

/-!
# Halo2 keygen — the circuit-side half of `keygen_vk`

Aggregator for the pinned-constraint-system derivation: the pure Clean-data processing that
turns a circuit's configure/synthesize output into halo2's `PinnedConstraintSystem` — floor
plan → activations → minimal fitting domain → `compress_selectors` → pinned record.

* `RichExpression` — the pinned/verifier gate AST (query-index space).
* `CompressSelectors` — the `SelCompressMap` derivation and its root-finding algebra.
* `FloorPlanner` — the V1 floor planner (region placement from the operation stream).
* `Projection` — the query-index walk erasing `Expression F Query` into `RichExpression F`.
* `PinnedCs` — `PinnedConstraintSystem`, `.ofOperations`, `FormalCircuit.toPinnedCS`.
* `Semantics` — the projection preserves evaluation (`derive_gates_eval`).
-/
