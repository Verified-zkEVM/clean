import Clean.Halo2.Keygen.Projection
import Clean.Halo2.Keygen.FloorPlanner
import Clean.Halo2.Formal

/-!
# `PinnedConstraintSystem` — the pinned constraint system, derived from a circuit

halo2's `PinnedConstraintSystem` is the canonical view of the constraint system a
verifying key pins (and hashes into `transcript_repr`): counts, flattened gate
polynomials, query lists, permutation columns, lookups, constants. The Lean record
mirrors every field of the Rust pinned record (`circuit.rs:966-979`).

`PinnedConstraintSystem.derive` computes it from a Clean `ConstraintSystem` and the
`compress_selectors` packing `map`. The query-registration order needs no input: Clean's
configure-time query registration records it in `cs.{advice,fixed,instance}Queries`, and the
packed columns' fixed queries are appended by the projection (`queryWalkInit`).

`PinnedConstraintSystem.ofOperations` and `FormalCircuit.toPinnedCS` close the loop — the
circuit-side half of halo2's `keygen_vk`: floor plan → activations → minimal fitting
domain → compress_selectors → pinned record.
-/

namespace Halo2

variable {F : Type}

/-! ## Constraint-system derived scalars

halo2 quantities that are pure functions of the `ConstraintSystem` — computable since
the configure-time query registration records `adviceQueries`. -/

/-- halo2 `ConstraintSystem::blinding_factors` (`circuit.rs:1652-1675`):
`max(3, max per-column advice-query count) + 1 + 1`. The per-column counts are Rust's
`num_advice_queries`, recovered by counting the recorded `adviceQueries`. -/
def ConstraintSystem.blindingFactors (cs : ConstraintSystem F) : ℕ :=
  let factors := (List.range cs.numAdviceColumns).foldl
    (fun m c => max m (cs.adviceQueries.countP (fun q => q.1.index = c))) 1
  max 3 factors + 1 + 1

/-- halo2 `ConstraintSystem::minimum_rows` (`circuit.rs:1678-1689`):
blinding factors + l_last + l_0 breathing room + one row. -/
def ConstraintSystem.minimumRows (cs : ConstraintSystem F) : ℕ :=
  cs.blindingFactors + 3

/-- The permutation argument's chunk length, `cs.degree() - 2`
(`permutation/verifier.rs:43`). -/
def ConstraintSystem.chunkLen (cs : ConstraintSystem F) : ℕ :=
  csDegree cs - 2

/-- The Lean mirror of halo2's `PinnedConstraintSystem` (`circuit.rs:966-979`): column
counts, gate polynomials, query layouts, the permutation argument's columns, lookup
argument expressions, constants columns, and the minimum-degree override — every field
of the Rust pinned record. -/
structure PinnedConstraintSystem (F : Type) where
  numFixedColumns : ℕ
  numAdviceColumns : ℕ
  numInstanceColumns : ℕ
  numSelectors : ℕ
  gates : List (RichExpression F)
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  instanceQueryLayout : List (ℕ × ℤ)
  /-- The permutation argument's columns (`permutation::Argument`), in `enable_equality`
  call order — recorded in `cs.permutationColumns`. -/
  permutationColumns : List AnyColumn
  lookupInputExprs : List (List (RichExpression F))
  lookupTableExprs : List (List (RichExpression F))
  constants : List ℕ
  minimumDegree : Option ℕ
deriving DecidableEq, Repr

/-- Derive the pinned CS data from a Clean constraint system and the (circuit-derived)
selector-compression map; the query layouts come from the CS's configure-recorded
queries (see the module docstring). -/
def PinnedConstraintSystem.derive [Field F] [DecidableEq F] (cs : ConstraintSystem F)
    (map : SelCompressMap) : PinnedConstraintSystem F :=
  -- single let: the projection (selector substitution + query walk) runs once per
  -- `derive` evaluation, not once per field
  let proj := projectCS map cs
  { numFixedColumns := proj.numFixedColumns
    numAdviceColumns := proj.numAdviceColumns
    numInstanceColumns := proj.numInstanceColumns
    numSelectors := proj.numSelectors
    gates := proj.gates
    adviceQueryLayout := proj.adviceQueryLayout
    fixedQueryLayout := proj.fixedQueryLayout
    instanceQueryLayout := proj.instanceQueryLayout
    permutationColumns := cs.permutationColumns
    lookupInputExprs := proj.lookups.map (·.inputs)
    lookupTableExprs := proj.lookups.map (·.tables)
    -- Clean's constraint system does not model `set_minimum_degree`; Orchard never calls it.
    constants := cs.constants.map (·.index)
    minimumDegree := none }

/-! ## The domain exponent `k`, derived

Rust does not compute `k` — orchard pins `const K: u32 = 11` and keygen *asserts* the
circuit fits: every assignment row must lie in `usable_rows = 0..n − (blinding_factors + 1)`
and `n ≥ cs.minimum_rows()` (`keygen.rs:200`). The minimal `k` satisfying those asserts is
the faithful derived value. -/

/-- The rows the keygen-view synthesize occupies: floor-planned region extents and
loaded table lengths (both must fit in the usable rows). -/
def usedRows (ops : Operations F) : ℕ :=
  let shapes := FloorPlanner.measureRegions ops
  -- `(planFull shapes).1 = V1.starts ops`, reusing the measured shapes rather than
  -- re-measuring inside `V1.starts`
  let starts := (FloorPlanner.V1.planFull shapes).1
  let regionEnd := ((starts.zip shapes).map fun (s, sh) => s + sh.rowCount).foldl max 0
  let tableLen := (ops.filterMap fun op => match op with
    | .loadTable _ vals => some vals.length
    | _ => none).foldl max 0
  max regionEnd tableLen

/-- The minimal domain exponent for which the circuit fits keygen's asserts. -/
def minimalK (cs : ConstraintSystem F) (ops : Operations F) : ℕ :=
  let blinding := cs.blindingFactors
  -- `blinding + 3 = cs.minimumRows`, without recomputing the blinding count
  let need := max (usedRows ops + blinding + 1) (blinding + 3)
  ((List.range 33).find? (fun k => need ≤ 2 ^ k)).getD 33

/-- The pinned constraint system of a circuit given its keygen-view operation stream:
derived floor plan → activations → minimal fitting domain → compress_selectors → pinned
record. The circuit-side half of halo2 keygen_vk. -/
def PinnedConstraintSystem.ofOperations [Field F] [DecidableEq F] (cs : ConstraintSystem F)
    (ops : Operations F) : PinnedConstraintSystem F :=
  let acts := activations (FloorPlanner.V1.starts ops) (indexedRegions ops 0).1
  let map := deriveSelCompressMap cs (2 ^ minimalK cs ops) acts
  .derive cs map

section FormalCircuit
variable [FiniteField F] {ConfigInput Config : Type} {Input Output : TypeMap}
  [CircuitType Input] [CircuitType Output]

/-- The pinned constraint system of a `FormalCircuit`: run its `configure` (producing the
config and constraint system), then derive the pinned record from the `synthesize`
operation stream. -/
def FormalCircuit.toPinnedCS (c : FormalCircuit F ConfigInput Config Input Output)
    (ci : ConfigInput) (input : Var Input F) : PinnedConstraintSystem F :=
  let (config, cs) := c.configure ci {}
  .ofOperations cs ((c.synthesize config input).operations)

end FormalCircuit

end Halo2
