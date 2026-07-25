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
    regionCount input = ((main input).operations i).regionCount := by
    -- fallback: count symbolically (child call chunks via `call_regionCount` metadata —
    -- the opaque `callOps` barrier is not evaluable, by design)
    intro _ _
    first
    | rfl
    | simp only [circuit_norm, Circuit.operations_bind, Circuit.operations_pure,
        Operations.regionCount_append, Operations.regionCount,
        FormalCircuit.call_regionCount, FormalCircuit.call_regionCount',
        Nat.add_assoc, Nat.reduceAdd]

section Statements
variable [CircuitType Input] [CircuitType Output]

/-- Soundness (verifier view — hints erased). If the constraints of `main` hold at
placement `place` from region index `i₀`, then `Spec` holds on the input, the extracted
high-level witness, and the output. -/
def FormalCircuit.Soundness
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) : Prop :=
  ∀ (i₀ : RegionIndex) (env : Placed Environment F)
    (input : Var Input F),
  EnvAssumptions env →
  Assumptions (eval env input) →
  Constraints env.place env.env ((main input).operations i₀) i₀ →
  Spec (eval env input) (eval env (ElaboratedCircuit.output main input i₀)) (extract input i₀ env)

/-- Completeness (prover view — hints visible). Under the honest prover's witness
generators, the soundness `Assumptions` (on the input's verifier-visible value) together
with `ProverAssumptions` imply the constraints and the `ProverSpec`.

`Assumptions` is assumed here as well as in soundness, so gadgets never repeat it inside
`ProverAssumptions`: the prover side is strictly *additional*, for hint-side facts that
the verifier value erases. -/
def FormalCircuit.Completeness
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    Prop :=
  ∀ (i₀ : RegionIndex) (env : Placed ProverEnvironment F)
    (input : Var Input F),
  ExtendsWitnesses env.place env.env ((main input).operations i₀) i₀ →
  EnvAssumptions env.toEnvironment →
  Assumptions (eval env.toEnvironment input) →
  ProverAssumptions (eval env input) (extract input i₀ env.toEnvironment) env.env.hint →
  Constraints env.place env.env ((main input).operations i₀) i₀ ∧
  ProverSpec (eval env input) (eval env (ElaboratedCircuit.output main input i₀))
    (extract input i₀ env.toEnvironment) env.env.hint

/-- Equivalence rewriting the layouter-level `Soundness` into a form with the input/output
*values* intro'd as variables (with their defining equations), the layouter-level mirror of
`FormalRegionCircuit.soundness_iff`. A proof tactic `rw`s this at the very start, so the user
works with `input`/`output` (finite-field values) instead of `eval env …`. -/
theorem FormalCircuit.soundness_iff
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) :
    FormalCircuit.Soundness main extract EnvAssumptions Assumptions Spec ↔
    ∀ (i₀ : RegionIndex) (env : Placed Environment F) (input_var : Var Input F)
      (input : Value Input F) (output : Value Output F),
    eval env input_var = input →
    eval env (ElaboratedCircuit.output main input_var i₀) = output →
    EnvAssumptions env →
    Assumptions input →
    Constraints env.place env.env ((main input_var).operations i₀) i₀ →
    Spec input output (extract input_var i₀ env) := by
  constructor
  · intro h i₀ env iv input output h_in h_out hE hA hC
    subst h_in h_out; exact h i₀ env iv hE hA hC
  · intro h i₀ env iv hE hA hC
    exact h i₀ env iv _ _ rfl rfl hE hA hC

/-- Completeness counterpart of the layouter-level `soundness_iff`, the mirror of
`FormalRegionCircuit.completeness_iff`. Only the *prover-side* input value is intro'd (with
its defining equation): the `Assumptions` and `EnvAssumptions` hypotheses stay raw (see the
region-level docstring for the rationale). -/
theorem FormalCircuit.completeness_iff
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    FormalCircuit.Completeness main extract EnvAssumptions Assumptions ProverAssumptions
      ProverSpec ↔
    ∀ (i₀ : RegionIndex) (env : Placed ProverEnvironment F) (input_var : Var Input F)
      (input : ProverValue Input F) (output : ProverValue Output F),
    eval env input_var = input →
    eval env (ElaboratedCircuit.output main input_var i₀) = output →
    ExtendsWitnesses env.place env.env ((main input_var).operations i₀) i₀ →
    EnvAssumptions env.toEnvironment →
    Assumptions (eval env.toEnvironment input_var) →
    ProverAssumptions input (extract input_var i₀ env.toEnvironment) env.env.hint →
    Constraints env.place env.env ((main input_var).operations i₀) i₀ ∧
    ProverSpec input output (extract input_var i₀ env.toEnvironment) env.env.hint := by
  constructor
  · intro h i₀ env iv input output h_in h_out hW hE hA hPA
    subst h_in h_out; exact h i₀ env iv hW hE hA hPA
  · intro h i₀ env iv hW hE hA hPA
    exact h i₀ env iv _ _ rfl rfl hW hE hA hPA

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

  /-- Env-level preconditions: facts about the ambient `Environment` (placement + cell
  assignment), *not* the gadget's own input. The canonical example is "the range table is
  loaded" — a table-contents fact about `env.fixed table_col r` that lives at the
  environment level and cannot be carried by `Assumptions` (which sees only the input
  value). Discharged by callers (an in-scope `loadTable` subcircuit, or an ambient VK
  guarantee). Defaults to `fun _ _ => True`.

  Takes the `Config` (mirroring the region level): the env-fact usually names a *config*
  column — e.g. "`env.fixed cfg.tableIdx r < 2^K`" for the range table — which the
  arbitrary-config soundness quantifier binds. `Soundness`/`Completeness` still take a
  plain `Placed Environment F → Prop`; the `soundness`/`completeness` fields feed
  `EnvAssumptions config`. See `lookup-design.md` §2.4/§D4. -/
  EnvAssumptions : Config → Placed Environment F → Prop := fun _ _ => True
  /-- Verifier-view precondition (hints erased). -/
  Assumptions : Value Input F → Prop := fun _ => True
  /-- Verifier-view postcondition: relates input, extracted witness, and output. -/
  Spec : Value Input F → Value Output F → Witness F → Prop

  /-- Prover-view precondition (hints visible), strictly *additional* to `Assumptions`
  (completeness assumes both) — hint-side facts that the verifier value erases, or (for
  positional gadgets) honesty conditions on the extracted `Witness` readings. -/
  ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop :=
    fun _ _ _ => True
  /-- Prover-view postcondition, proved alongside the constraints. -/
  ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop :=
    fun _ _ _ _ => True

  soundness : ∀ (config : Config),
    FormalCircuit.Soundness (synthesize config) (extract config) (EnvAssumptions config)
      Assumptions Spec
  completeness : ∀ (config : Config),
    FormalCircuit.Completeness (synthesize config) (extract config) (EnvAssumptions config)
      Assumptions ProverAssumptions ProverSpec

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

/-- The whole `call` runtime triple, packaged with its defining equation behind an
`opaque` reduction barrier. One mechanism, two jobs:

* **Runtime (the perf fix).** The implementation applies the child monad `synthesize`
  **exactly once** (`let r := self.synthesize config input i`) and reads all three
  components off that single application. `opaque` initializers still *run* at runtime, so
  this sharing — not the opacity — is what stops a call node from re-materializing its
  child: no bundle's metadata shape (e.g. a spine bundle's recompute-shaped `output`
  field, which re-runs the whole child monad) can ever cause re-evaluation, because the
  runtime never reads the metadata fields at all (they are proof-side only). This kills the
  ~2^depth blow-up where each nesting level materialized its child 2–3×.
* **Proofs (the reduction barrier).** `@[irreducible]` would not suffice: the kernel
  ignores reducibility attributes, so defeq-replayed simp steps in big parent proofs would
  evaluate straight through `synthesize` into the whole child op tree (the job the retired
  `.subcircuit` constructor head used to do). `opaque` is neutral for the kernel *and* the
  elaborator across all three components; the packaged `property` re-exposes the defining
  equation as a *recorded* rewrite (`call_eq`/`call_operations` below). -/
private opaque callPacked (F : Type) [FiniteField F] (CI Cfg : Type)
    (Input Output : TypeMap) [CircuitType Input] [CircuitType Output] :
    { f : FormalCircuit F CI Cfg Input Output → Cfg → Var Input F → RegionIndex →
        Var Output F × Operations F × RegionIndex //
      ∀ self config input i, f self config input i
        = (self.output config input i, (self.synthesize config input).operations i,
           i + self.regionCount config input) } :=
  ⟨fun self config input i =>
      let r := self.synthesize config input i
      (r.1, r.2.1, i + self.regionCount config input),
   fun self config input i => by
      -- componentwise: `output` component is exactly the elaborated `output_eq`, the
      -- other two are the `Circuit.operations`/`Circuit.nextRegionIndex` projections
      have h : (self.synthesize config input i).1 = self.output config input i :=
        ((self.elaborated config).output_eq input i).symm
      show ((self.synthesize config input i).1, (self.synthesize config input i).2.1,
          i + self.regionCount config input)
        = (self.output config input i, (self.synthesize config input).operations i,
           i + self.regionCount config input)
      rw [h, Circuit.operations]⟩

/-- Call this circuit as a subcircuit from a parent layouter circuit: append the child's
operations, return the child's output, advance the region counter by `regionCount`. The
runtime is the `callPacked` shared-application implementation (one child monad application
per call node); the child list stays a folded chunk in parent proofs (the proof boundary,
isolated by `constraints_append`), with `callPacked` the reduction barrier for all three
components. Rust: calling a chip method. -/
def call (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) : Circuit F (Var Output F) :=
  fun i => (callPacked F ConfigInput Config Input Output).val self config input i

/-- The operation list a `call` contributes: the child's own operations, read off the
`callPacked` shared application (so no metadata re-materialization) behind its reduction
barrier. Consumers never unfold this; they rewrite with `call_operations`. NO attribute —
the opaque underneath is the barrier. -/
def callOps (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) (i : RegionIndex) : Operations F :=
  ((callPacked F ConfigInput Config Input Output).val self config input i).2.1

/-- The full `call` triple, re-exposed from the packed `property`: output, operations, and
next region index of a single `call` node. The public handle downstream proofs use to open
any component of the (otherwise opaque) `call`. -/
theorem call_eq (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    self.call config input i
      = (self.output config input i, (self.synthesize config input).operations i,
         i + self.regionCount config input) :=
  (callPacked F ConfigInput Config Input Output).property self config input i

/-- The chunk-opening equation, `callOps`-spelled (for sites that unfolded
`call`/`operations` first). NOT `@[circuit_norm]`. -/
theorem callOps_eq (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    self.callOps config input i = (self.synthesize config input).operations i :=
  congrArg (fun t => t.2.1)
    ((callPacked F ConfigInput Config Input Output).property self config input i)

/-- The chunk-opening equation: a `call`'s operations are the child's `synthesize`
operations. Deliberately NOT `@[circuit_norm]` — chunks stay folded in parent proofs;
this is the bridge the framework leaves (`Subcircuit.lean`, `subcircuit_rw`) rewrite
with. -/
theorem call_operations (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.call config input).operations i
      = (self.synthesize config input).operations i :=
  self.callOps_eq config input i

/-!
The consumption mechanism for `call` chunks lives in `Subcircuit.lean` (framework leaf
lemmas over the folded `(call …).operations` term) and `Tactics/SubcircuitRw.lean` (the
polarity-aware rewriter applying them). Extractor composition: a parent whose `Witness`
includes a child's builds `extract` by calling the child's `extract` on the child's
region range — knowledge soundness composes through the call tree by construction.
TODO: `SubcircuitsConsistent` wellformedness (child cells reference the ambient region
range `[i₀, i₀ + regionCount)`), discharged by the monad's structure.
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
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) : Prop :=
  ∀ (self : RegionIndex) (env : Placed Environment F) (input : Var Input F),
  EnvAssumptions env →
  Assumptions (eval env input) →
  RegionOperations.Constraints env.place self env.env ((main input).operations self) →
  Spec (eval env input) (eval env (ElaboratedRegionCircuit.output main input self))
    (extract input self env)

/-- Completeness of a region-level circuit (prover view). As at the layouter level, the
soundness `Assumptions` (on the input's verifier-visible value) are assumed alongside
`ProverAssumptions`, so the prover side is strictly additional (hint-side facts only).

The prover-side predicates see the extracted `Witness` (the same designated env readings
`Spec` sees): positional gadgets state "my neighborhood holds honest values" as a
`ProverAssumptions` on the witness. -/
def FormalRegionCircuit.Completeness
    (main : Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    Prop :=
  ∀ (self : RegionIndex) (env : Placed ProverEnvironment F) (input : Var Input F),
  RegionOperations.ExtendsWitnesses env.place self env.env ((main input).operations self) →
  EnvAssumptions env.toEnvironment →
  Assumptions (eval env.toEnvironment input) →
  ProverAssumptions (eval env input) (extract input self env.toEnvironment) env.env.hint →
  RegionOperations.Constraints env.place self env.env ((main input).operations self) ∧
  ProverSpec (eval env input)
    (eval env (ElaboratedRegionCircuit.output main input self))
    (extract input self env.toEnvironment) env.env.hint

/-- Equivalence rewriting `Soundness` into a form with the input/output *values* intro'd
as variables (with their defining equations). A proof tactic `rw`s this at the very start,
so the user works with `input`/`output` (finite-field values) instead of `eval env …`. -/
theorem FormalRegionCircuit.soundness_iff
    (main : Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) :
    FormalRegionCircuit.Soundness main extract EnvAssumptions Assumptions Spec ↔
    ∀ (self : RegionIndex) (env : Placed Environment F) (input_var : Var Input F)
      (input : Value Input F) (output : Value Output F),
    eval env input_var = input →
    eval env (ElaboratedRegionCircuit.output main input_var self) = output →
    EnvAssumptions env →
    Assumptions input →
    RegionOperations.Constraints env.place self env.env ((main input_var).operations self) →
    Spec input output (extract input_var self env) := by
  constructor
  · intro h self env iv input output h_in h_out hE hA hC
    subst h_in h_out; exact h self env iv hE hA hC
  · intro h self env iv hE hA hC
    exact h self env iv _ _ rfl rfl hE hA hC

/-- Completeness counterpart of `soundness_iff`. Only the *prover-side* input value is
intro'd (with its defining equation): the verifier value carries strictly less
information (hint components erase to unit; cell components read the same environment as
the prover eval), so the `Assumptions` hypothesis keeps the raw verifier eval — the eval
machinery decomposes it in gadget proofs, and `h_input`'s component equations rewrite it
to value-level facts. -/
theorem FormalRegionCircuit.completeness_iff
    (main : Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F Input Output main]
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    FormalRegionCircuit.Completeness main extract EnvAssumptions Assumptions ProverAssumptions
      ProverSpec ↔
    ∀ (self : RegionIndex) (env : Placed ProverEnvironment F) (input_var : Var Input F)
      (input : ProverValue Input F) (output : ProverValue Output F),
    eval env input_var = input →
    eval env (ElaboratedRegionCircuit.output main input_var self) = output →
    RegionOperations.ExtendsWitnesses env.place self env.env ((main input_var).operations self) →
    EnvAssumptions env.toEnvironment →
    Assumptions (eval env.toEnvironment input_var) →
    ProverAssumptions input (extract input_var self env.toEnvironment) env.env.hint →
    RegionOperations.Constraints env.place self env.env ((main input_var).operations self) ∧
    ProverSpec input output (extract input_var self env.toEnvironment) env.env.hint := by
  constructor
  · intro h self env iv input output h_in h_out hW hE hA hPA
    subst h_in h_out; exact h self env iv hW hE hA hPA
  · intro h self env iv hW hE hA hPA
    exact h self env iv _ _ rfl rfl hW hE hA hPA

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

  /-- Designated env readings the contract may reference: `Spec` and the prover-side
  predicates all receive `extract`'s value. Two uses: knowledge-soundness extraction
  (opaque to parents), and *positional neighborhoods* — a gadget whose gate reads
  adjacent cells it doesn't own (rows determined by its own offset) publishes them as a
  `reads` def and sets `extract := fun cfg offset _ _ env => eval env (reads cfg offset)`;
  parents connect the witness to cells they know by `rfl`. -/
  Witness : TypeMap := unit
  inhabitedWitness [Inhabited F] : Inhabited (Witness F) := by infer_instance
  extract : Config → (offset : ℕ) → Var Input F → RegionIndex → Placed Environment F →
      Witness F :=
    fun _ _ _ _ _ => inhabitedWitness.default

  /-- Env-level preconditions: facts about the ambient `Environment` (placement + cell
  assignment), *not* the gadget's own input. The canonical example is "the range table is
  loaded" — a table-contents fact about `env.fixed table_col r` that lives at the
  environment level and cannot be carried by `Assumptions` (which sees only the input
  value). Discharged by callers (an in-scope `loadTable` subcircuit, or an ambient VK
  guarantee). Defaults to `fun _ => True`.

  Takes the `Config` (unlike `Assumptions`): the env-fact usually names a *config* column
  — e.g. "`env.fixed cfg.tableIdx r < 2^K`" for the range table — which the arbitrary-config
  soundness quantifier binds. `Soundness`/`Completeness` still take a plain
  `Placed Environment F → Prop`; the `soundness`/`completeness` fields feed
  `EnvAssumptions config`. See `lookup-design.md` §2.4/§D4. -/
  EnvAssumptions : Config → Placed Environment F → Prop := fun _ _ => True
  Assumptions : Value Input F → Prop := fun _ => True
  Spec : Value Input F → Value Output F → Witness F → Prop
  ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop :=
    fun _ _ _ => True
  ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop :=
    fun _ _ _ _ => True

  soundness : ∀ (config : Config) (offset : ℕ),
    FormalRegionCircuit.Soundness (synthesize config offset) (extract config offset)
      (EnvAssumptions config) Assumptions Spec
  completeness : ∀ (config : Config) (offset : ℕ),
    FormalRegionCircuit.Completeness (synthesize config offset) (extract config offset)
      (EnvAssumptions config) Assumptions ProverAssumptions ProverSpec

namespace FormalRegionCircuit
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

/-- The output variable of the region circuit, in the ambient region. -/
def output (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) : Var Output F :=
  (self.elaborated config offset).output input region

/-- The whole region-level `call` runtime pair, packaged with its defining equation behind
an `opaque` reduction barrier; see `FormalCircuit.callPacked` for the two-jobs design. The
implementation applies the child monad `synthesize` **exactly once** and reads both the
output and the operations off that single application (runtime: no metadata
re-materialization); the `opaque` is the kernel + elaborator reduction barrier, and the
packaged `property` re-exposes the equation (`call_eq`/`call_operations`). -/
private opaque callPacked (F : Type) [FiniteField F] (CI Cfg : Type)
    (Input Output : TypeMap) [CircuitType Input] [CircuitType Output] :
    { f : FormalRegionCircuit F CI Cfg Input Output → Cfg → ℕ → Var Input F →
        RegionIndex → Var Output F × RegionOperations F //
      ∀ self config offset input region, f self config offset input region
        = (self.output config offset input region,
           (self.synthesize config offset input).operations region) } :=
  ⟨fun self config offset input region =>
      let r := self.synthesize config offset input region
      (r.1, r.2),
   fun self config offset input region => by
      have h : (self.synthesize config offset input region).1
          = self.output config offset input region :=
        ((self.elaborated config offset).output_eq input region).symm
      show ((self.synthesize config offset input region).1,
          (self.synthesize config offset input region).2)
        = (self.output config offset input region,
           (self.synthesize config offset input).operations region)
      rw [h, RegionCircuit.operations]⟩

/-- Call this region circuit as a subcircuit from a parent region circuit: append the
child's operations (in the *same* ambient region), returning the child's output. The
runtime is the `callPacked` shared-application implementation (one child monad application
per call node); the child list stays a folded chunk in parent proofs (the proof boundary),
with `callPacked` the reduction barrier. Rust: calling an `assign_region` helper with the
parent's `region`/`offset`. -/
def call (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) : RegionCircuit F (Var Output F) :=
  fun region => (callPacked F ConfigInput Config Input Output).val self config offset input region

/-- The operation list a region-level `call` contributes — read off the `callPacked`
shared application behind its reduction barrier; see `FormalCircuit.callOps`. NO attribute. -/
def callOps (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) : RegionOperations F :=
  ((callPacked F ConfigInput Config Input Output).val self config offset input region).2

/-- The full region-level `call` pair, re-exposed from the packed `property`: the output
and operations of a single `call` node; see `FormalCircuit.call_eq`. -/
theorem call_eq (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    self.call config offset input region
      = (self.output config offset input region,
         (self.synthesize config offset input).operations region) :=
  (callPacked F ConfigInput Config Input Output).property self config offset input region

/-- The chunk-opening equation, `callOps`-spelled. NOT `@[circuit_norm]`. -/
theorem callOps_eq (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    self.callOps config offset input region
      = (self.synthesize config offset input).operations region :=
  congrArg (fun t => t.2)
    ((callPacked F ConfigInput Config Input Output).property self config offset input region)

/-- The chunk-opening equation for region-level calls; see
`FormalCircuit.call_operations`. NOT `@[circuit_norm]`. -/
theorem call_operations (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    (self.call config offset input).operations region
      = (self.synthesize config offset input).operations region :=
  self.callOps_eq config offset input region

end FormalRegionCircuit

/-! ## The region-boundary bridge: `FormalRegionCircuit.toFormal`

Lifts a region-level gadget to a layouter-level `FormalCircuit` by wrapping its body in a
fresh `assignRegion` (halo2 helpers wrapped in their own region start at row offset 0). This
is the *single* mechanism that makes every region-level gadget consumable at layouter level;
the layouter absorption iffs then cover it with zero extra machinery.

**Contract transfer.** All contracts move over verbatim (the two levels' contract fields
mirror each other, including the config-aware `EnvAssumptions`), with one adapter forced by
the level difference: the region `extract` takes an `offset`, the layouter one does not (the
wrapping region fixes offset `0`), so the layouter `extract` is `child.extract config 0 …`. -/

namespace FormalRegionCircuit
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

/-- Lift a region-level formal circuit to the layouter level by wrapping its body in a fresh
region. See the section docstring for the contract-transfer details. -/
def toFormal (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String := child.name) :
    FormalCircuit F ConfigInput Config Input Output where
  name := name
  configure := child.configure
  synthesize config input := assignRegion name (child.synthesize config 0 input)
  elaborated config :=
    { output := fun input i => (child.synthesize config 0 input).output i
      regionCount := fun _ => 1
      output_eq := by intro _ _; rfl
      regionCount_eq := by
        intro _ _
        simp only [assignRegion, Circuit.operations, Operations.regionCount] }
  Witness := child.Witness
  inhabitedWitness := child.inhabitedWitness
  extract config input i₀ env := child.extract config 0 input i₀ env
  EnvAssumptions := child.EnvAssumptions
  Assumptions := child.Assumptions
  Spec := child.Spec
  ProverAssumptions := child.ProverAssumptions
  ProverSpec := child.ProverSpec

  soundness := by
    intro config
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_in h_out hE hA hC
    -- the wrapping region's layouter `Constraints` peels to the child's region `Constraints`
    -- at the freshly-allocated region index `i₀` (offset 0)
    simp only [Circuit.operations, assignRegion, Halo2.Constraints] at hC
    subst h_in h_out
    -- instantiate the child's region-level soundness at `self := i₀`
    have hsound := child.soundness config 0 i₀ env input_var hE hA hC.1
    have hout := (child.elaborated config 0).output_eq input_var i₀
    rw [hout] at hsound
    show child.Spec (eval env input_var)
      (eval env ((child.synthesize config 0 input_var).output i₀))
      (child.extract config 0 input_var i₀ env)
    exact hsound

  completeness := by
    intro config
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_in h_out hW hE hA hpa
    simp only [Circuit.operations, assignRegion,
      Halo2.ExtendsWitnesses, Halo2.Constraints] at hW ⊢
    subst h_in h_out
    -- instantiate the child's region-level completeness at `self := i₀`
    have hcompl := child.completeness config 0 i₀ env input_var hW.1 hE hA hpa
    -- the two `output` spellings (layouter vs region elaborated metadata) are defeq;
    -- pin both to the raw `.output` via the region instance's `output_eq`
    refine ⟨⟨hcompl.1, trivial⟩, ?_⟩
    have hout := (child.elaborated config 0).output_eq input_var i₀
    show child.ProverSpec (eval env input_var)
      (eval env ((child.synthesize config 0 input_var).output i₀))
      (child.extract config 0 input_var i₀ env.toEnvironment) env.env.hint
    rw [hout] at hcompl
    exact hcompl.2

end FormalRegionCircuit

end Halo2
