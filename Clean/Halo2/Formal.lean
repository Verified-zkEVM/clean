import Clean.Halo2.Basic

/-!
# Halo2 formal circuits — DESIGN SKETCH

Port of `Clean/Circuit/Formal.lean`, the proof-boundary packages that turn a circuit
into a subcircuit with a semantic contract. Deliberately simplified from main Clean per
design discussion:

- **One structure, `FormalCircuit`** — the hint-aware `GeneralFormalCircuit.WithHint`
  under the shorter name. No separate `FormalCircuit`/`FormalAssertion`/
  `GeneralFormalCircuit` variants (they were a UX nicety; `WithHint` was already
  pervasive in the phase-one Orchard port). Input/Output are general `CircuitType`s;
  the cost is that identities like `Value M F = M F` hold only up to defeq (not
  reducibly), making inputs slightly less ergonomic — tolerated.
- **No channels / `ProverData`**: halo2 has no interaction argument, and lookup tables
  are fixed columns (`Environment` carries no `data`). The `FormalCircuitBase` channel
  machinery is gone; the base collapses into `FormalCircuit` directly.
- **`Witness` slot + constructive extractor** for knowledge soundness (see the
  requirements doc): `Spec` receives a high-level witness computed by `extract` from the
  low-level witness (placement + environment). Extractors compose through the subcircuit
  tree. `Witness` defaults to `unit` (ordinary input/output soundness).
- **Region-relative**: soundness/completeness quantify over the starting region index
  `i₀` and the placement `place` (the analogues of main Clean's `offset`).

- **`configure` + `synthesize` bundled**: both halo2 phases live in the same structure
  (with `ConfigInput`/`Config` as type parameters, since parents interact with both —
  they are part of the gadget's visible signature), so bundles are parameterless defs.
  Soundness/completeness quantify over an *arbitrary* config; consistency between the
  phases holds because gates are standalone defs of the config's columns/selectors,
  referenced by both.

This file has the **layouter-level** `FormalCircuit` (over `Circuit`) and the
region-level `FormalRegionCircuit` (over `RegionCircuit`, for `assign_region` fragments
composed inside a parent region like `add_incomplete` inside variable-base mul), which
additionally takes the row `offset` at which the gadget is placed.

The forward lemmas and the hypothesis-rewriting tactic (`circuit_proof_start` analogue)
live in a companion tactic file; here we provide the data + statements they consume.
-/

namespace Halo2

variable {F : Type} [FiniteField F] {Input Output Witness : TypeMap}

/-- Bundles the circuit metadata exposed in reduced form (main Clean's
`ElaboratedCircuit`): the output cells and the number of region indices consumed, as
functions of the input variable and starting region index, so parent circuits simplify
without unfolding `main`. -/
class ElaboratedCircuit (F : Type) [FiniteField F] (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output] (main : Var Input F → Circuit F (Var Output F)) where
  output : Var Input F → RegionIndex → Var Output F := fun input i => (main input).output i
  regionCount : Var Input F → ℕ := fun input => ((main input).operations 0).regionCount
  output_eq : ∀ input i, output input i = (main input).output i := by intro _ _; rfl
  regionCount_eq : ∀ input i,
    regionCount input = ((main input).operations i).regionCount := by intro _ _; rfl

section Statements
variable [CircuitType Input] [CircuitType Output]

/-- Soundness (verifier view — hints erased). If the constraints of `main` hold at
placement `place` from region index `i₀`, then `Spec` holds on the input, the extracted
high-level witness, and the output. -/
def FormalCircuit.Soundness
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) : Prop :=
  ∀ (i₀ : RegionIndex) (env : Placed Environment F)
    (input : Var Input F),
  Assumptions (eval env input) →
  Constraints env.place env.env ((main input).operations i₀) i₀ →
  Spec (eval env input) (eval env (ElaboratedCircuit.output main input i₀)) (extract input i₀ env)

/-- Completeness (prover view — hints visible). Under the honest prover's witness
generators, `ProverAssumptions` imply the constraints and the `ProverSpec`. -/
def FormalCircuit.Completeness
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (ProverAssumptions : ProverValue Input F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop) : Prop :=
  ∀ (i₀ : RegionIndex) (env : Placed ProverEnvironment F)
    (input : Var Input F),
  ExtendsWitnesses env.place env.env ((main input).operations i₀) i₀ →
  ProverAssumptions (eval env input) env.env.hint →
  Constraints env.place env.env ((main input).operations i₀) i₀ ∧
  ProverSpec (eval env input) (eval env (ElaboratedCircuit.output main input i₀)) env.env.hint

end Statements

/--
A formal circuit: a layouter-level circuit packaged with its contract. Single
structure (the hint-aware variant), general `CircuitType` I/O, constructive high-level
`Witness` extractor. The proof boundary — parents consume `Spec` opaquely.

Bundles both halo2 phases: `configure` (register selectors/gates into the constraint
system, given `ConfigInput` — what the parent hands down) and `synthesize` (the
layouter-level circuit, given the resulting `Config`). Bundles are *parameterless*
defs; soundness/completeness quantify over an **arbitrary** config — see
`FormalRegionCircuit` for the rationale. Unlike the region level there is no `offset`:
layouter circuits create their own regions and are placed via the region index `i₀`.

Circuits with a trivial witness leave `Witness := unit` (default) and set
`extract := fun _ _ _ _ => ()`.
-/
structure FormalCircuit (F : Type) [FiniteField F] (ConfigInput Config : Type)
    (Input Output : TypeMap) [CircuitType Input] [CircuitType Output] where
  name : String := "anonymous"

  /-- Configuration phase: allocate selectors and register gates into the constraint
  system, from what the parent hands down (`ConfigInput`) to the configuration consumed
  by `synthesize` (`Config`). Rust: `Config::configure(meta, …)`. -/
  configure : ConfigInput → Configure F Config
  /-- Synthesis phase: the layouter-level circuit. Rust: the chip method body. -/
  synthesize : Config → Var Input F → Circuit F (Var Output F)
  elaborated : ∀ config, ElaboratedCircuit F Input Output (synthesize config) := by
    intro config; first | infer_instance | exact {}

  /-- The high-level witness type (default `unit`: ordinary I/O soundness). -/
  Witness : TypeMap := unit
  inhabitedWitness [Inhabited F] : Inhabited (Witness F) := by infer_instance

  /-- Constructive extractor: the high-level witness from the low-level one
  (placement + environment), given the config, input variable and starting region index. -/
  extract : Config → Var Input F → RegionIndex → Placed Environment F → Witness F :=
    fun _ _ _ _ => inhabitedWitness.default

  /-- Verifier-view precondition (hints erased). -/
  Assumptions : Value Input F → Prop := fun _ => True
  /-- Verifier-view postcondition: relates input, extracted witness, and output. -/
  Spec : Value Input F → Value Output F → Witness F → Prop

  /-- Prover-view precondition (hints visible). -/
  ProverAssumptions : ProverValue Input F → ProverHint F → Prop := fun _ _ => True
  /-- Prover-view postcondition, proved alongside the constraints. -/
  ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop := fun _ _ _ => True

  soundness : ∀ (config : Config),
    FormalCircuit.Soundness (synthesize config) (extract config) Assumptions Spec
  completeness : ∀ (config : Config),
    FormalCircuit.Completeness (synthesize config) ProverAssumptions ProverSpec

namespace FormalCircuit
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

/-- The output variable of the circuit (via the elaborated metadata). -/
def output (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) (i₀ : RegionIndex) : Var Output F :=
  (self.elaborated config).output input i₀

/-- Number of region indices the circuit consumes. -/
def regionCount (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) : ℕ :=
  (self.elaborated config).regionCount input

/-- Call this circuit as a subcircuit from a parent layouter circuit: emit a single
`.subcircuit` operation carrying the child's operations, return the child's output,
advance the region counter by `regionCount`. Rust: calling a chip method. -/
def call (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) : Circuit F (Var Output F) :=
  fun i =>
    (self.output config input i, [.subcircuit ((self.synthesize config input).operations i)],
      i + self.regionCount config input)

/-!
TODO (with the first slice consumer — `witness_point` → `add_incomplete`):

- **Forward lemmas**, the #358 mechanism. From `self.soundness`, derive
  `Constraints place env [.subcircuit ((main input).operations i₀)] i₀ →
    (Assumptions (evalCells ⟨place,env⟩ input) →
      Spec (evalCells ⟨place,env⟩ input) (extract …) (evalCells ⟨place,env⟩ (output input i₀)))`,
  i.e. the single-subcircuit constraint chunk unfolds (a `Constraints` computation lemma)
  and `soundness` applies. The completeness direction is dual. A per-circuit `@[grind]`/
  simp-lemma-shaped statement the tactic can fire.
- **`circuit_proof_start` analogue**: sets up the soundness/completeness goal, runs the
  deliberate `circuit_norm` simp set (`Lemmas.lean`) to expose the operation list, then
  applies each child's forward lemma to rewrite subcircuit chunks to their `Spec` — the
  forward reasoning simp cannot do.
- **Extractor composition**: a parent whose `Witness` includes a child's builds `extract`
  by calling the child's `extract` on the child's region range — knowledge soundness
  composes through the subcircuit tree by construction.
- **`SubcircuitsConsistent`**: the wellformedness that subcircuit cells reference the
  ambient region range `[i₀, i₀ + regionCount)`, discharged by the monad's structure.
-/

end FormalCircuit

/-! ## Region-level formal circuits

The region-level analogue of `FormalCircuit`, for `assign_region` fragments composed
*inside* a parent region at region-local rows (e.g. `add_incomplete.assign_region`
called inside variable-base mul's big region). It lives in the ambient region `self` and
creates no new regions — so, unlike `FormalCircuit`, there is no `i₀`/`regionCount`; the
constraints are `RegionOperations.Constraints` at the ambient `self`.
-/

/-- Region-level metadata exposed in reduced form: the output cells as a function of the
input variable and the ambient region index. -/
class ElaboratedRegionCircuit (F : Type) [FiniteField F] (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output]
    (main : Var Input F → RegionCircuit F (Var Output F)) where
  output : Var Input F → RegionIndex → Var Output F := fun input self => (main input).output self
  output_eq : ∀ input self, output input self = (main input).output self := by intro _ _; rfl

section RegionStatements
variable [CircuitType Input] [CircuitType Output]

/-- Soundness of a region-level circuit (verifier view). If the constraints of `main`
hold in the ambient region `self`, then `Spec` holds on the input, extracted witness,
and output. -/
def FormalRegionCircuit.Soundness
    (main : Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) : Prop :=
  ∀ (self : RegionIndex) (env : Placed Environment F) (input : Var Input F),
  Assumptions (eval env input) →
  RegionOperations.Constraints env.place self env.env ((main input).operations self) →
  Spec (eval env input) (eval env (ElaboratedRegionCircuit.output main input self))
    (extract input self env)

/-- Completeness of a region-level circuit (prover view). -/
def FormalRegionCircuit.Completeness
    (main : Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F Input Output main]
    (ProverAssumptions : ProverValue Input F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop) : Prop :=
  ∀ (self : RegionIndex) (env : Placed ProverEnvironment F) (input : Var Input F),
  RegionOperations.ExtendsWitnesses env.place self env.env ((main input).operations self) →
  ProverAssumptions (eval env input) env.env.hint →
  RegionOperations.Constraints env.place self env.env ((main input).operations self) ∧
  ProverSpec (eval env input)
    (eval env (ElaboratedRegionCircuit.output main input self)) env.env.hint

/-- Equivalence rewriting `Soundness` into a form with the input/output *values* intro'd
as variables (with their defining equations). A proof tactic `rw`s this at the very start,
so the user works with `input`/`output` (finite-field values) instead of `eval env …`. -/
theorem FormalRegionCircuit.soundness_iff
    (main : Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) :
    FormalRegionCircuit.Soundness main extract Assumptions Spec ↔
    ∀ (self : RegionIndex) (env : Placed Environment F) (input_var : Var Input F)
      (input : Value Input F) (output : Value Output F),
    eval env input_var = input →
    eval env (ElaboratedRegionCircuit.output main input_var self) = output →
    Assumptions input →
    RegionOperations.Constraints env.place self env.env ((main input_var).operations self) →
    Spec input output (extract input_var self env) := by
  constructor
  · intro h self env iv input output h_in h_out hA hC
    subst h_in h_out; exact h self env iv hA hC
  · intro h self env iv hA hC
    exact h self env iv _ _ rfl rfl hA hC

/-- Completeness counterpart of `soundness_iff`. -/
theorem FormalRegionCircuit.completeness_iff
    (main : Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F Input Output main]
    (ProverAssumptions : ProverValue Input F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop) :
    FormalRegionCircuit.Completeness main ProverAssumptions ProverSpec ↔
    ∀ (self : RegionIndex) (env : Placed ProverEnvironment F) (input_var : Var Input F)
      (input : ProverValue Input F) (output : ProverValue Output F),
    eval env input_var = input →
    eval env (ElaboratedRegionCircuit.output main input_var self) = output →
    RegionOperations.ExtendsWitnesses env.place self env.env ((main input_var).operations self) →
    ProverAssumptions input env.env.hint →
    RegionOperations.Constraints env.place self env.env ((main input_var).operations self) ∧
    ProverSpec input output env.env.hint := by
  constructor
  · intro h self env iv input output h_in h_out hW hA
    subst h_in h_out; exact h self env iv hW hA
  · intro h self env iv hW hA
    exact h self env iv _ _ rfl rfl hW hA

end RegionStatements

/--
A region-level formal circuit: an `assign_region`-fragment packaged with its contract.
Same shape as `FormalCircuit` (single hint-aware structure, `Witness` extractor), but
inside the ambient region rather than creating regions.

Bundles both halo2 phases: `configure` (register selectors/gates into the constraint
system, given the columns handed down by the parent — `ConfigInput`) and `synthesize`
(the region-level circuit, given the resulting `Config` and the row `offset` at which
the gadget is placed inside the ambient region). Bundles are therefore *parameterless*
defs; soundness/completeness quantify over an **arbitrary** config and offset — proofs
stay decoupled from `configure`'s monadic allocation, and consistency between the two
phases holds because gates are standalone defs of the config's columns/selectors,
referenced by both. (If a gadget's soundness ever needs config well-formedness, add an
explicit `ConfigWF config` hypothesis discharged from `configure` at instantiation.)
-/
structure FormalRegionCircuit (F : Type) [FiniteField F] (ConfigInput Config : Type)
    (Input Output : TypeMap) [CircuitType Input] [CircuitType Output] where
  name : String := "anonymous"

  /-- Configuration phase: allocate selectors and register gates into the constraint
  system, from what the parent chip hands down (`ConfigInput`, typically columns) to
  the configuration consumed by `synthesize` (`Config`, halo2's meaning: selectors +
  columns, e.g. `witness_point::Config`). Rust: `Config::configure(meta, …)`. -/
  configure : ConfigInput → Configure F Config
  /-- Synthesis phase: the region-level circuit, at row `offset` inside the ambient
  region. Rust: the `assign_region`-helper body at `offset`. -/
  synthesize : Config → (offset : ℕ) → Var Input F → RegionCircuit F (Var Output F)
  elaborated : ∀ config offset,
    ElaboratedRegionCircuit F Input Output (synthesize config offset) := fun _ _ => {}

  Witness : TypeMap := unit
  inhabitedWitness [Inhabited F] : Inhabited (Witness F) := by infer_instance
  extract : Config → (offset : ℕ) → Var Input F → RegionIndex → Placed Environment F →
      Witness F :=
    fun _ _ _ _ _ => inhabitedWitness.default

  Assumptions : Value Input F → Prop := fun _ => True
  Spec : Value Input F → Value Output F → Witness F → Prop
  ProverAssumptions : ProverValue Input F → ProverHint F → Prop := fun _ _ => True
  ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop := fun _ _ _ => True

  soundness : ∀ (config : Config) (offset : ℕ),
    FormalRegionCircuit.Soundness (synthesize config offset) (extract config offset)
      Assumptions Spec
  completeness : ∀ (config : Config) (offset : ℕ),
    FormalRegionCircuit.Completeness (synthesize config offset) ProverAssumptions ProverSpec

namespace FormalRegionCircuit
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

/-- The output variable of the region circuit, in the ambient region. -/
def output (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) : Var Output F :=
  (self.elaborated config offset).output input region

/-- Call this region circuit as a subcircuit from a parent region circuit: emit a single
region-level `.subcircuit` operation carrying the child's operations (in the *same*
ambient region), returning the child's output. Rust: calling an `assign_region` helper
with the parent's `region`/`offset`. -/
def call (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) : RegionCircuit F (Var Output F) :=
  fun region =>
    (self.output config offset input region,
      [.subcircuit ((self.synthesize config offset input).operations region)])

end FormalRegionCircuit

end Halo2
