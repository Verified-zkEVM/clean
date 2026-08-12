import Clean.Halo2.Tactics.Keygen

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

/-- The keygen arguments available at a circuit boundary. -/
structure KeygenContext (F : Type) where
  gates : List (Gate F)
  lookups : List (LookupArgument F)
  permutationColumns : List AnyColumn

/--
A configure result together with proof that every argument it provides or borrows is
available in an ambient keygen context.

This is the configure-side capability consumed by an opaque subcircuit call. Aggregate
configurers may package several such values; monadic composition transports them by
`mono` without reopening the configured child.
-/
structure ConfigurationCertificate
    {ConfigInput Config InputVar : Type}
    (requirements : KeygenRequirements F ConfigInput InputVar)
    (configure : ConfigInput → Configure F Config)
    (config : Config) (context : KeygenContext F) where
  configInput : ConfigInput
  counts : ConfigureCounts
  configLawful : requirements.configLawful configInput
  output_eq : (configure configInput).output counts = config
  gates : ∀ gate,
    gate ∈ requirements.gates configInput configLawful ++
      ((configure configInput).delta counts).gates →
    gate ∈ context.gates
  lookups : ∀ argument,
    argument ∈ requirements.lookups configInput configLawful ++
      ((configure configInput).delta counts).lookups →
    argument ∈ context.lookups
  permutationColumns : ∀ column,
    column ∈ requirements.permutationColumns configInput configLawful ++
      ((configure configInput).delta counts).permutationRequests →
    column ∈ context.permutationColumns

namespace ConfigurationCertificate

/-- The canonical certificate in the configure program's exact resulting context. -/
def ofOutput
    {ConfigInput Config InputVar : Type}
    (requirements : KeygenRequirements F ConfigInput InputVar)
    (configure : ConfigInput → Configure F Config)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (configLawful : requirements.configLawful configInput) :
    ConfigurationCertificate requirements configure
      ((configure configInput).output counts)
      { gates := requirements.gates configInput configLawful ++
          ((configure configInput).delta counts).gates
        lookups := requirements.lookups configInput configLawful ++
          ((configure configInput).delta counts).lookups
        permutationColumns := requirements.permutationColumns configInput configLawful ++
          ((configure configInput).delta counts).permutationRequests } :=
  ⟨configInput, counts, configLawful, rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩

/-- Transport a configured capability into a larger ambient context. -/
def mono
    {ConfigInput Config InputVar : Type}
    {requirements : KeygenRequirements F ConfigInput InputVar}
    {configure : ConfigInput → Configure F Config}
    {config : Config} {source target : KeygenContext F}
    (certificate : ConfigurationCertificate requirements configure config source)
    (gates : ∀ gate, gate ∈ source.gates → gate ∈ target.gates)
    (lookups : ∀ argument, argument ∈ source.lookups → argument ∈ target.lookups)
    (permutationColumns : ∀ column,
      column ∈ source.permutationColumns → column ∈ target.permutationColumns) :
    ConfigurationCertificate requirements configure config target where
  configInput := certificate.configInput
  counts := certificate.counts
  configLawful := certificate.configLawful
  output_eq := certificate.output_eq
  gates gate hgate := gates gate (certificate.gates gate hgate)
  lookups argument hargument :=
    lookups argument (certificate.lookups argument hargument)
  permutationColumns column hcolumn :=
    permutationColumns column (certificate.permutationColumns column hcolumn)

end ConfigurationCertificate

/--
The complete reduced metadata of a layouter circuit's configure/synthesize pair.

Configure elaboration stays compositional through `infer_instance`; synthesis metadata
is flattened here because circuit authors frequently provide reduced output and region
count functions manually. This is the single elaboration object exposed by
`FormalCircuit` to its parents.
-/
class ElaboratedCircuit (F : Type) [FiniteField F]
    (ConfigInput Config : Type) (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output]
    (configure : ConfigInput → Configure F Config)
    (synthesize : Config → Var Input F → Circuit F (Var Output F)) where
  configureInfo : ∀ input, ElaboratedConfigure (configure input) := by
    intro input
    try dsimp only [configure]
    infer_instance
  /-- Keygen capabilities supplied by the caller rather than local configure. -/
  keygenRequirements : KeygenRequirements F ConfigInput (Var Input F) := {}
  /-- Configure/synthesis registration certificate. -/
  registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := configure configInput
    ((synthesize (program.output counts) input).operations i).KeygenRegistered
      (keygenRequirements.gates configInput hconfig ++ (program.delta counts).gates)
      (keygenRequirements.lookups configInput hconfig ++ (program.delta counts).lookups)
      (keygenRequirements.permutationColumns configInput hconfig ++
        (program.delta counts).permutationRequests ++
        keygenRequirements.inputPermutationColumns configInput hconfig input) := by
    keygen_registration
  /-- Every copy endpoint is either a declared caller input or assigned by synthesis. -/
  copyCellsAssigned :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := configure configInput
    ((synthesize (program.output counts) input).operations i).CopyCellsAssigned i
      (keygenRequirements.inputCells configInput hconfig input) := by
    keygen_registration
  /-- Every lookup activation enables its master and only its declared selectors. -/
  lookupActivationsWellFormed :
    ∀ (config : Config) (input : Var Input F) (i : RegionIndex),
    ((synthesize config input).operations i).LookupActivationsWellFormed := by
    keygen_registration
  output : Config → Var Input F → RegionIndex → Var Output F :=
    fun config input i => (synthesize config input).output i
  regionCount : Var Input F → ℕ := fun _ => 0
  /-- Exact compositional footprint of synthesis.  Parents use this reduced value
  without unfolding the child's operation stream. -/
  synthesisSummary : Config → Var Input F → RegionIndex →
      FloorPlanner.SynthesisSummary
  output_eq : ∀ config input i,
    output config input i = (synthesize config input).output i := by
    intro _ _ _
    rfl
  regionCount_eq : ∀ config input i,
    regionCount input =
      ((synthesize config input).operations i).regionCount := by
    -- fallback: count symbolically (child call chunks via `call_regionCount` metadata —
    -- the opaque `callOps` barrier is not evaluable, by design)
    intro _ _ _
    first
    | rfl
    | simp only [circuit_norm, Circuit.operations_bind, Circuit.operations_pure,
        Operations.regionCount_append, Operations.regionCount,
        FormalCircuit.call_regionCount, FormalCircuit.call_regionCount',
        Nat.add_assoc, Nat.reduceAdd]
  synthesisSummary_eq : ∀ config input i,
    synthesisSummary config input i =
      FloorPlanner.synthesisSummary
        ((synthesize config input).operations i) := by
    intro _ _ _
    first
    | rfl
    | simp only [circuit_norm, Circuit.operations_bind,
        Circuit.operations_pure, FloorPlanner.synthesisSummary_append,
        FormalCircuit.call_synthesisSummary,
        FormalCircuit.call_synthesisSummary']

section SynthesisSummary
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}
    {configure : ConfigInput → Configure F Config}
    {synthesize : Config → Var Input F → Circuit F (Var Output F)}

/-- Project exact synthesis columns without exposing unrelated elaborated metadata. -/
@[circuit_norm ↓]
theorem ElaboratedCircuit.synthesisSummary_columns_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.synthesisSummary config input i).columns =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).columns :=
  congrArg FloorPlanner.SynthesisSummary.columns
    (self.synthesisSummary_eq config input i)

/-- Project one exact column occupancy without exposing unrelated metadata. -/
@[circuit_norm ↓]
theorem ElaboratedCircuit.synthesisSummary_columnOccupancy_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex)
    (column : FloorPlanner.RegionColumn) :
    (self.synthesisSummary config input i).columnOccupancy column =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).columnOccupancy column :=
  congrArg (fun summary => summary.columnOccupancy column)
    (self.synthesisSummary_eq config input i)

/-- Project the exact deferred-constant request count without exposing unrelated metadata. -/
@[circuit_norm ↓]
theorem ElaboratedCircuit.synthesisSummary_constantSiteCount_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.synthesisSummary config input i).constantSiteCount =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).constantSiteCount :=
  congrArg FloorPlanner.SynthesisSummary.constantSiteCount
    (self.synthesisSummary_eq config input i)

/-- Project the ordered reduced V1 measurement input without exposing the child's
operation stream. -/
@[circuit_norm ↓]
theorem ElaboratedCircuit.synthesisSummary_regionShapes_eq
    (self : ElaboratedCircuit F ConfigInput Config Input Output configure synthesize)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    (self.synthesisSummary config input i).regionShapes =
      (FloorPlanner.synthesisSummary
        ((synthesize config input).operations i)).regionShapes :=
  congrArg FloorPlanner.SynthesisSummary.regionShapes
    (self.synthesisSummary_eq config input i)

end SynthesisSummary

section Statements
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}

/-- Soundness (verifier view — hints erased). If the constraints of `main` hold at
placement `place` from region index `i₀`, then `Spec` holds on the input, the extracted
high-level witness, and the output. -/
def FormalCircuit.Soundness
    (configure : ConfigInput → Configure F Config)
    (synthesize : Config → Var Input F → Circuit F (Var Output F))
    [elaborated :
      ElaboratedCircuit F ConfigInput Config Input Output configure synthesize]
    (config : Config)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) : Prop :=
  ∀ (i₀ : RegionIndex) (env : Placed Environment F)
    (input : Var Input F),
  EnvAssumptions env →
  Assumptions (eval env input) →
  Constraints env.place env.env ((synthesize config input).operations i₀) i₀ →
  Spec (eval env input)
    (eval env (ElaboratedCircuit.output configure synthesize config input i₀))
    (extract input i₀ env)

/-- Completeness (prover view — hints visible). Under the honest prover's witness
generators, the soundness `Assumptions` (on the input's verifier-visible value) together
with `ProverAssumptions` imply the constraints and the `ProverSpec`.

`Assumptions` is assumed here as well as in soundness, so gadgets never repeat it inside
`ProverAssumptions`: the prover side is strictly *additional*, for hint-side facts that
the verifier value erases. -/
def FormalCircuit.Completeness
    (configure : ConfigInput → Configure F Config)
    (synthesize : Config → Var Input F → Circuit F (Var Output F))
    [elaborated :
      ElaboratedCircuit F ConfigInput Config Input Output configure synthesize]
    (config : Config)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    Prop :=
  ∀ (i₀ : RegionIndex) (env : Placed ProverEnvironment F)
    (input : Var Input F),
  ExtendsWitnesses env.place env.env ((synthesize config input).operations i₀) i₀ →
  EnvAssumptions env.toEnvironment →
  Assumptions (eval env.toEnvironment input) →
  ProverAssumptions (eval env input) (extract input i₀ env.toEnvironment) env.env.hint →
  Constraints env.place env.env ((synthesize config input).operations i₀) i₀ ∧
  ProverSpec (eval env input)
    (eval env (ElaboratedCircuit.output configure synthesize config input i₀))
    (extract input i₀ env.toEnvironment) env.env.hint

/-- Equivalence rewriting the layouter-level `Soundness` into a form with the input/output
*values* intro'd as variables (with their defining equations), the layouter-level mirror of
`FormalRegionCircuit.soundness_iff`. A proof tactic `rw`s this at the very start, so the user
works with `input`/`output` (finite-field values) instead of `eval env …`. -/
theorem FormalCircuit.soundness_iff
    (configure : ConfigInput → Configure F Config)
    (synthesize : Config → Var Input F → Circuit F (Var Output F))
    [ElaboratedCircuit F ConfigInput Config Input Output configure synthesize]
    (config : Config)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) :
    FormalCircuit.Soundness configure synthesize config
      extract EnvAssumptions Assumptions Spec ↔
    ∀ (i₀ : RegionIndex) (env : Placed Environment F) (input_var : Var Input F)
      (input : Value Input F) (output : Value Output F),
    eval env input_var = input →
    eval env (ElaboratedCircuit.output
      configure synthesize config input_var i₀) = output →
    EnvAssumptions env →
    Assumptions input →
    Constraints env.place env.env
      ((synthesize config input_var).operations i₀) i₀ →
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
    (configure : ConfigInput → Configure F Config)
    (synthesize : Config → Var Input F → Circuit F (Var Output F))
    [ElaboratedCircuit F ConfigInput Config Input Output configure synthesize]
    (config : Config)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    FormalCircuit.Completeness configure synthesize config
      extract EnvAssumptions Assumptions ProverAssumptions ProverSpec ↔
    ∀ (i₀ : RegionIndex) (env : Placed ProverEnvironment F) (input_var : Var Input F)
      (input : ProverValue Input F) (output : ProverValue Output F),
    eval env input_var = input →
    eval env (ElaboratedCircuit.output
      configure synthesize config input_var i₀) = output →
    ExtendsWitnesses env.place env.env
      ((synthesize config input_var).operations i₀) i₀ →
    EnvAssumptions env.toEnvironment →
    Assumptions (eval env.toEnvironment input_var) →
    ProverAssumptions input (extract input_var i₀ env.toEnvironment) env.env.hint →
    Constraints env.place env.env
      ((synthesize config input_var).operations i₀) i₀ ∧
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
  /-- The single reduced interface for both phases. Configure metadata is inferred
  compositionally by default; synthesis metadata may be overridden explicitly. -/
  elaborated :
    ElaboratedCircuit F ConfigInput Config Input Output configure synthesize := by
    first
    | infer_instance
    | exact {}

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
    FormalCircuit.Soundness (elaborated := elaborated) configure synthesize config
      (extract config) (EnvAssumptions config) Assumptions Spec
  completeness : ∀ (config : Config),
    FormalCircuit.Completeness (elaborated := elaborated) configure synthesize config
      (extract config) (EnvAssumptions config)
      Assumptions ProverAssumptions ProverSpec

/--
The configure and synthesis phases of a layouter circuit agree on their keygen-facing
data.

The law is stated over arbitrary initial allocation counts so child circuits compose
inside a parent's configure program. Append-only configure metadata records the exact
local contributions; synthesis may enable those arguments plus explicit arguments
required from its caller. Selector allocation is carried compositionally by the
mandatory `ElaboratedConfigure`, independently of this cross-phase registration law.
-/
structure FormalCircuit.KeygenLawful
    {ConfigInput Config : Type}
    [CircuitType Input] [CircuitType Output]
    (self : FormalCircuit F ConfigInput Config Input Output)
    (requirements : KeygenRequirements F ConfigInput (Var Input F) := {}) : Prop where
  registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : requirements.configLawful configInput)
      (input : Var Input F) (i : RegionIndex),
    let program := self.configure configInput
    ((self.synthesize (program.output counts) input).operations i).KeygenRegistered
      (requirements.gates configInput hconfig ++ (program.delta counts).gates)
      (requirements.lookups configInput hconfig ++ (program.delta counts).lookups)
      (requirements.permutationColumns configInput hconfig ++
        (program.delta counts).permutationRequests ++
        requirements.inputPermutationColumns configInput hconfig input)

namespace FormalCircuit
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

instance (self : FormalCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) :
    ElaboratedConfigure (self.configure input) :=
  self.elaborated.configureInfo input

/-- The folded keygen interface exposed by a layouter circuit. -/
abbrev keygenRequirements
    (self : FormalCircuit F ConfigInput Config Input Output) :
    KeygenRequirements F ConfigInput (Var Input F) :=
  self.elaborated.keygenRequirements

/-- A configured circuit handle whose full keygen interface is available in `context`. -/
abbrev ConfigurationCertificate
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (context : KeygenContext F) :=
  Halo2.ConfigurationCertificate self.keygenRequirements self.configure config context

/-- The certificate produced by this circuit's own configure program. -/
def configureCertificate
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    self.ConfigurationCertificate
      ((self.configure configInput).output counts)
      { gates := self.keygenRequirements.gates configInput hconfig ++
          ((self.configure configInput).delta counts).gates
        lookups := self.keygenRequirements.lookups configInput hconfig ++
          ((self.configure configInput).delta counts).lookups
        permutationColumns := self.keygenRequirements.permutationColumns configInput hconfig ++
          ((self.configure configInput).delta counts).permutationRequests } :=
  Halo2.ConfigurationCertificate.ofOutput
    self.keygenRequirements self.configure configInput counts hconfig

/--
Proof that a configuration value is the output of this circuit's own configure
program, from a caller input satisfying its folded provenance requirement.
-/
structure Configured
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) where
  configInput : ConfigInput
  counts : ConfigureCounts
  configLawful :
    self.keygenRequirements.configLawful configInput
  output_eq :
    (self.configure configInput).output counts = config

/-- Forget ambient availability while retaining configure provenance. -/
def ConfigurationCertificate.configured
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    self.Configured config :=
  ⟨certificate.configInput, certificate.counts,
    certificate.configLawful, certificate.output_eq⟩

/-- A configure output is configured whenever its caller provenance holds. -/
abbrev Configured.ofOutput
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    self.Configured ((self.configure configInput).output counts) :=
  ⟨configInput, counts, hconfig, rfl⟩

/-- A pure configure wrapper preserves a caller-supplied config at any allocation state. -/
def Configured.ofPure
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    self.Configured config :=
  ⟨config, {}, hconfig, by simp [hconfigure]⟩

/-- Gate arguments available from a configured circuit handle. -/
def Configured.gates
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) : List (Gate F) :=
  self.keygenRequirements.gates
      (FormalCircuit.Configured.configInput configured)
      (FormalCircuit.Configured.configLawful configured) ++
    ((self.configure (FormalCircuit.Configured.configInput configured)).delta
      (FormalCircuit.Configured.counts configured)).gates

/-- Lookup arguments available from a configured circuit handle. -/
def Configured.lookups
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) :
    List (LookupArgument F) :=
  self.keygenRequirements.lookups
      (FormalCircuit.Configured.configInput configured)
      (FormalCircuit.Configured.configLawful configured) ++
    ((self.configure (FormalCircuit.Configured.configInput configured)).delta
      (FormalCircuit.Configured.counts configured)).lookups

/-- Equality-enabled columns available from a configured circuit handle. -/
def Configured.permutationColumns
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) : List AnyColumn :=
  self.keygenRequirements.permutationColumns
      (FormalCircuit.Configured.configInput configured)
      (FormalCircuit.Configured.configLawful configured) ++
    ((self.configure (FormalCircuit.Configured.configInput configured)).delta
      (FormalCircuit.Configured.counts configured)).permutationRequests

/-- Equality-enabled columns required by the concrete input of this call. -/
def Configured.inputPermutationColumns
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config)
    (input : Var Input F) : List AnyColumn :=
  self.keygenRequirements.inputPermutationColumns
    (FormalCircuit.Configured.configInput configured)
    (FormalCircuit.Configured.configLawful configured) input

/-- Use a layouter certificate through the familiar `Configured.gates` interface. -/
theorem ConfigurationCertificate.gates_of_configured
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ gate, gate ∈ certificate.configured.gates → gate ∈ context.gates := by
  intro gate hgate
  simpa [Configured.gates, ConfigurationCertificate.configured] using
    certificate.gates gate hgate

/-- Use a layouter certificate through the familiar `Configured.lookups` interface. -/
theorem ConfigurationCertificate.lookups_of_configured
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ argument,
      argument ∈ certificate.configured.lookups → argument ∈ context.lookups := by
  intro argument hargument
  simpa [Configured.lookups, ConfigurationCertificate.configured] using
    certificate.lookups argument hargument

/-- Use a layouter certificate through `Configured.permutationColumns`. -/
theorem ConfigurationCertificate.permutationColumns_of_configured
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ column,
      column ∈ certificate.configured.permutationColumns →
        column ∈ context.permutationColumns := by
  intro column hcolumn
  simpa [Configured.permutationColumns, ConfigurationCertificate.configured] using
    certificate.permutationColumns column hcolumn

@[simp, keygen_norm] theorem Configured.ofPure_gates
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.gates (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.gates config hconfig := by
  simp [Configured.gates, Configured.ofPure, hconfigure]

@[simp, keygen_norm] theorem Configured.ofPure_lookups
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.lookups (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.lookups config hconfig := by
  simp [Configured.lookups, Configured.ofPure, hconfigure]

@[keygen_norm] theorem Configured.ofPure_permutationColumns
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.permutationColumns (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.permutationColumns config hconfig := by
  simp [Configured.permutationColumns, Configured.ofPure, hconfigure]

@[keygen_norm] theorem Configured.ofPure_inputPermutationColumns
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config)
    (input : Var Input F) :
    Configured.inputPermutationColumns
        (Configured.ofPure self config hconfig hconfigure) input =
      self.keygenRequirements.inputPermutationColumns config hconfig input := by
  simp [Configured.inputPermutationColumns, Configured.ofPure]

@[simp, keygen_norm] theorem Configured.ofOutput_gates
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    Configured.gates (Configured.ofOutput self configInput counts hconfig) =
      self.keygenRequirements.gates configInput hconfig ++
        ((self.configure configInput).delta counts).gates :=
  rfl

@[simp, keygen_norm] theorem Configured.ofOutput_lookups
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    Configured.lookups (Configured.ofOutput self configInput counts hconfig) =
      self.keygenRequirements.lookups configInput hconfig ++
        ((self.configure configInput).delta counts).lookups :=
  rfl

@[simp, keygen_norm] theorem Configured.ofOutput_configInput
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    FormalCircuit.Configured.configInput
      (Configured.ofOutput self configInput counts hconfig) = configInput :=
  rfl

@[simp, keygen_norm] theorem Configured.ofOutput_counts
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    FormalCircuit.Configured.counts
      (Configured.ofOutput self configInput counts hconfig) = counts :=
  rfl

/--
Selector allocation borrowed from the incoming configure state. Complete configure
programs normally reduce this to `True`; reusable gadgets may require selectors carried
by `ConfigInput` to have been allocated by their caller.
-/
def selectorRequirements
    (self : FormalCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts) : Prop :=
  (self.elaborated.configureInfo input).selectorRequirements counts

/-- Local keygen capabilities are allocated whenever the caller requirements hold. -/
theorem selectorsAllocated
    (self : FormalCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts)
    (hrequirements : self.selectorRequirements input counts) :
    ((self.configure input).delta counts).SelectorsAllocated
      ((self.configure input).finalCounts counts).numSelectors :=
  (self.elaborated.configureInfo input).selectorsAllocated counts hrequirements

/-- Configure composition keeps gate and lookup selectors mutually compatible. -/
theorem lookupSelectorsCompatible
    (self : FormalCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts)
    (hrequirements : self.selectorRequirements input counts) :
    ((self.configure input).delta counts).LookupSelectorsCompatible :=
  (self.elaborated.configureInfo input).lookupSelectorsCompatible
    counts hrequirements

/-- Column allocation and query-shape requirements borrowed from the incoming
configure state. Closed circuits normally reduce this to `True`. -/
def queryRequirements
    (self : FormalCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts) : Prop :=
  (self.elaborated.configureInfo input).queryRequirements counts

/-- Every locally registered query is valid and names an allocated column whenever
the caller requirements hold. -/
theorem queriesLawful
    (self : FormalCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts)
    (hrequirements : self.queryRequirements input counts) :
    ((self.configure input).delta counts).QueriesLawful
      ((self.configure input).finalCounts counts) :=
  (self.elaborated.configureInfo input).queriesLawful counts hrequirements

/-- The output variable of the circuit (via the elaborated metadata). -/
def output (self : FormalCircuit F ConfigInput Config Input Output) (config : Config)
    (input : Var Input F) (i₀ : RegionIndex) : Var Output F :=
  self.elaborated.output config input i₀

/-- Number of region indices the circuit consumes. -/
def regionCount (self : FormalCircuit F ConfigInput Config Input Output)
    (input : Var Input F) : ℕ :=
  self.elaborated.regionCount input

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
@[keygen_call_expression]
private opaque callPacked (F : Type) [FiniteField F] (CI Cfg : Type)
    (Input Output : TypeMap) [CircuitType Input] [CircuitType Output] :
    { f : FormalCircuit F CI Cfg Input Output → Cfg → Var Input F → RegionIndex →
        Var Output F × Operations F × RegionIndex //
      ∀ self config input i, f self config input i
        = (self.output config input i, (self.synthesize config input).operations i,
           i + self.regionCount input) } :=
  ⟨fun self config input i =>
      let r := self.synthesize config input i
      (r.1, r.2.1, i + self.regionCount input),
   fun self config input i => by
      -- componentwise: `output` component is exactly the elaborated `output_eq`, the
      -- other two are the `Circuit.operations`/`Circuit.nextRegionIndex` projections
      have h : (self.synthesize config input i).1 = self.output config input i :=
        (self.elaborated.output_eq config input i).symm
      show ((self.synthesize config input i).1, (self.synthesize config input i).2.1,
          i + self.regionCount input)
        = (self.output config input i, (self.synthesize config input).operations i,
           i + self.regionCount input)
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
         i + self.regionCount input) :=
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

/-- A call exposes the child's exact reduced synthesis footprint. -/
@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    FloorPlanner.synthesisSummary ((self.call config input).operations i) =
      self.elaborated.synthesisSummary config input i := by
  rw [self.call_operations]
  exact (self.elaborated.synthesisSummary_eq config input i).symm

@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary' {Output : TypeMap} [ProvableType Output]
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (input : Var Input F) (i : RegionIndex) :
    FloorPlanner.synthesisSummary
        (@Circuit.operations F _ (Output (AssignedCell F))
          (self.call config input) i) =
      self.elaborated.synthesisSummary config input i :=
  self.call_synthesisSummary config input i

/--
Consume a configure certificate directly. Unlike `call_keygenRegistered`, this exposes
no gate-by-gate routing obligations to the parent.
-/
@[keygen_norm]
theorem call_keygenRegistered_ofCertificate
    (self : FormalCircuit F ConfigInput Config Input Output)
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context)
    (input : Var Input F) (i : RegionIndex)
    (hinputPermutationColumns : ∀ column,
      column ∈ certificate.configured.inputPermutationColumns input →
      column ∈ context.permutationColumns) :
    ((self.call config input).operations i).KeygenRegistered
      context.gates context.lookups context.permutationColumns := by
  rcases certificate with
    ⟨configInput, counts, hconfig, output_eq, gates, lookups, permutationColumns⟩
  subst config
  rw [self.call_operations]
  exact (self.elaborated.registered
    configInput counts hconfig input i).mono gates lookups (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact permutationColumns column (by
          simpa only [List.mem_append] using hcolumn)
      · exact hinputPermutationColumns column (by
          simpa [Configured.inputPermutationColumns,
            ConfigurationCertificate.configured] using hcolumn))

/--
An embedded registration certificate closes a child call against any larger ambient
gate, lookup, and equality-column sets. This is the compositional leaf used by
`keygen_registration`.
-/
@[keygen_norm]
theorem call_keygenRegistered
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ Configured.gates hconfigured →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ Configured.lookups hconfigured →
        argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ Configured.permutationColumns hconfigured →
        column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈ Configured.inputPermutationColumns hconfigured input →
        column ∈ targetPermutationColumns) :
    ((self.call config input).operations i).KeygenRegistered
      targetGates targetLookups targetPermutationColumns := by
  rcases hconfigured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact (self.elaborated.registered
    configInput counts hconfig input i).mono
      (by simpa [Configured.gates] using hgates)
      (by simpa [Configured.lookups] using hlookups)
      (by
        intro column hcolumn
        simp only [List.mem_append] at hcolumn
        rcases hcolumn with hcolumn | hcolumn
        · exact hpermutationColumns column (by
            simpa [Configured.permutationColumns] using hcolumn)
        · exact hinputPermutationColumns column (by
            simpa [Configured.inputPermutationColumns] using hcolumn))

/-- Registration certificate specialized to a configure output. Its premises expose
the caller requirements and local configure delta directly. -/
theorem call_keygenRegistered_ofOutput
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (input : Var Input F) (i : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates : ∀ gate,
      gate ∈ self.keygenRequirements.gates configInput hconfig ++
        ((self.configure configInput).delta counts).gates →
      gate ∈ targetGates)
    (hlookups : ∀ argument,
      argument ∈ self.keygenRequirements.lookups configInput hconfig ++
        ((self.configure configInput).delta counts).lookups →
      argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ self.keygenRequirements.permutationColumns configInput hconfig ++
        ((self.configure configInput).delta counts).permutationRequests →
      column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈
        self.keygenRequirements.inputPermutationColumns configInput hconfig input →
      column ∈ targetPermutationColumns) :
    ((self.call
      ((self.configure configInput).output counts) input).operations i).KeygenRegistered
        targetGates targetLookups targetPermutationColumns := by
  apply self.call_keygenRegistered _
      (Configured.ofOutput self configInput counts hconfig)
  · simpa [Configured.gates, Configured.ofOutput] using hgates
  · simpa [Configured.lookups, Configured.ofOutput] using hlookups
  · simpa [Configured.permutationColumns, Configured.ofOutput] using
      hpermutationColumns
  · simpa [Configured.inputPermutationColumns, Configured.ofOutput] using
      hinputPermutationColumns

/-- A folded call is registered in exactly the arguments carried by its configured
handle. This conclusion shape exposes every input needed by `grind`. -/
theorem call_keygenRegistered_exact
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex) :
    ((self.call config input).operations i).KeygenRegistered
      hconfigured.gates hconfigured.lookups
        (hconfigured.permutationColumns ++
          hconfigured.inputPermutationColumns input) :=
  self.call_keygenRegistered config hconfigured input i
    (fun _ h => h) (fun _ h => h)
    (fun _ h => List.mem_append_left _ h)
    (fun _ h => List.mem_append_right _ h)

/-- Lookup activations in a child call obey the lookup's local selector declaration. -/
theorem call_lookupActivationsWellFormed
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config)
    (input : Var Input F) (i : RegionIndex) :
    ((self.call config input).operations i).LookupActivationsWellFormed := by
  rw [self.call_operations]
  exact self.elaborated.lookupActivationsWellFormed config input i

/-- Lookup-activation certificate in the opaque call spelling. -/
theorem callPacked_lookupActivationsWellFormed
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config)
    (input : Var Input F) (i : RegionIndex) :
    (((callPacked F ConfigInput Config Input Output).val self
      config input i).2.1)
        |>.LookupActivationsWellFormed :=
  self.call_lookupActivationsWellFormed config input i

/-- Registration certificate in the exact opaque spelling exposed after operation-spine
normalization. -/
theorem callPacked_keygenRegistered
    (self : FormalCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (input : Var Input F) (i : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ Configured.gates hconfigured →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ Configured.lookups hconfigured →
        argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ Configured.permutationColumns hconfigured →
        column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈ Configured.inputPermutationColumns hconfigured input →
        column ∈ targetPermutationColumns) :
    (((callPacked F ConfigInput Config Input Output).val
      self config input i).2.1).KeygenRegistered targetGates targetLookups
        targetPermutationColumns :=
  call_keygenRegistered self config hconfigured input i hgates hlookups
    hpermutationColumns hinputPermutationColumns

/--
A lawful layouter child remains registered when called inside a parent whose available
argument lists contain the child's requirements and configure contribution.
-/
theorem KeygenLawful.call_registered
    {self : FormalCircuit F ConfigInput Config Input Output}
    {requirements : KeygenRequirements F ConfigInput (Var Input F)}
    (hlawful : self.KeygenLawful requirements)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : requirements.configLawful configInput)
    (input : Var Input F) (i : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ requirements.gates configInput hconfig ++
          ((self.configure configInput).delta counts).gates →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ requirements.lookups configInput hconfig ++
          ((self.configure configInput).delta counts).lookups →
        argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ requirements.permutationColumns configInput hconfig ++
        ((self.configure configInput).delta counts).permutationRequests →
      column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈
        requirements.inputPermutationColumns configInput hconfig input →
      column ∈ targetPermutationColumns) :
    ((self.call
      ((self.configure configInput).output counts)
      input).operations i).KeygenRegistered targetGates targetLookups
        targetPermutationColumns := by
  rw [self.call_operations]
  exact (FormalCircuit.KeygenLawful.registered
    hlawful configInput counts hconfig input i).mono hgates hlookups
      (by
        intro column hcolumn
        simp only [List.mem_append] at hcolumn
        rcases hcolumn with hcolumn | hcolumn
        · exact hpermutationColumns column (by
            simpa only [List.mem_append] using hcolumn)
        · exact hinputPermutationColumns column hcolumn)

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

/-- Region-level counterpart of `ElaboratedCircuit`. -/
class ElaboratedRegionCircuit (F : Type) [FiniteField F]
    (ConfigInput Config : Type) (Input Output : TypeMap)
    [CircuitType Input] [CircuitType Output]
    (configure : ConfigInput → Configure F Config)
    (synthesize :
      Config → (offset : ℕ) → Var Input F → RegionCircuit F (Var Output F)) where
  configureInfo : ∀ input, ElaboratedConfigure (configure input) := by
    intro input
    try dsimp only [configure]
    infer_instance
  /-- Keygen capabilities supplied by the caller rather than local configure. -/
  keygenRequirements : KeygenRequirements F ConfigInput (Var Input F) := {}
  /-- Region-level configure/synthesis registration certificate. -/
  registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex),
    let program := configure configInput
    ((synthesize
      (program.output counts) offset input).operations region).Forall
        (RegionOperation.KeygenRegistered
          (keygenRequirements.gates configInput hconfig ++ (program.delta counts).gates)
          (keygenRequirements.lookups configInput hconfig ++ (program.delta counts).lookups)
          (keygenRequirements.permutationColumns configInput hconfig ++
            (program.delta counts).permutationRequests ++
            keygenRequirements.inputPermutationColumns configInput hconfig input)) := by
    keygen_registration
  /-- Region-level copy endpoints are either declared inputs or locally assigned. -/
  copyCellsAssigned :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : keygenRequirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex),
    let program := configure configInput
    ((synthesize
      (program.output counts) offset input).operations region).CopyCellsAssigned region
        (keygenRequirements.inputCells configInput hconfig input) := by
    keygen_registration
  /-- Every region lookup activation enables its master and only declared selectors. -/
  lookupActivationsWellFormed :
    ∀ (config : Config) (offset : ℕ)
      (input : Var Input F) (region : RegionIndex),
    ((synthesize config offset input).operations region)
      |>.LookupActivationsWellFormed := by
    keygen_registration
  output : Config → ℕ → Var Input F → RegionIndex → Var Output F :=
    fun config offset input self =>
      (synthesize config offset input).output self
  /-- Exact footprint contributed inside the ambient region. -/
  synthesisSummary : Config → ℕ → Var Input F → RegionIndex →
      FloorPlanner.RegionSynthesisSummary
  output_eq : ∀ config offset input self,
    output config offset input self =
      (synthesize config offset input).output self := by
    intro _ _ _ _
    rfl
  synthesisSummary_eq : ∀ config offset input self,
    synthesisSummary config offset input self =
      FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations self) := by
    intro _ _ _ _
    first
    | rfl
    | simp only [circuit_norm, RegionCircuit.operations_bind,
        RegionCircuit.operations_pure,
        FloorPlanner.regionSynthesisSummary_append,
        FormalRegionCircuit.call_synthesisSummary,
        FormalRegionCircuit.call_synthesisSummary']

section RegionSynthesisSummary
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}
    {configure : ConfigInput → Configure F Config}
    {synthesize :
      Config → ℕ → Var Input F → RegionCircuit F (Var Output F)}

@[circuit_norm ↓]
theorem ElaboratedRegionCircuit.synthesisSummary_columns_eq
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (self.synthesisSummary config offset input region).columns =
      (FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations region)).columns :=
  congrArg FloorPlanner.RegionSynthesisSummary.columns
    (self.synthesisSummary_eq config offset input region)

@[circuit_norm ↓]
theorem ElaboratedRegionCircuit.synthesisSummary_rowCount_eq
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (self.synthesisSummary config offset input region).rowCount =
      (FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations region)).rowCount :=
  congrArg FloorPlanner.RegionSynthesisSummary.rowCount
    (self.synthesisSummary_eq config offset input region)

@[circuit_norm ↓]
theorem ElaboratedRegionCircuit.synthesisSummary_constantSiteCount_eq
    (self : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    (self.synthesisSummary config offset input region).constantSiteCount =
      (FloorPlanner.regionSynthesisSummary
        ((synthesize config offset input).operations region)).constantSiteCount :=
  congrArg FloorPlanner.RegionSynthesisSummary.constantSiteCount
    (self.synthesisSummary_eq config offset input region)

end RegionSynthesisSummary

section RegionStatements
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}

/-- Soundness of a region-level circuit (verifier view). If the constraints of `main`
hold in the ambient region `self`, then `Spec` holds on the input, extracted witness,
and output. -/
def FormalRegionCircuit.Soundness
    (configure : ConfigInput → Configure F Config)
    (synthesize :
      Config → (offset : ℕ) → Var Input F → RegionCircuit F (Var Output F))
    [elaborated : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize]
    (config : Config) (offset : ℕ)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) : Prop :=
  ∀ (self : RegionIndex) (env : Placed Environment F) (input : Var Input F),
  EnvAssumptions env →
  Assumptions (eval env input) →
  RegionOperations.Constraints env.place self env.env
    ((synthesize config offset input).operations self) →
  Spec (eval env input)
    (eval env (ElaboratedRegionCircuit.output
      configure synthesize config offset input self))
    (extract input self env)

/-- Completeness of a region-level circuit (prover view). As at the layouter level, the
soundness `Assumptions` (on the input's verifier-visible value) are assumed alongside
`ProverAssumptions`, so the prover side is strictly additional (hint-side facts only).

The prover-side predicates see the extracted `Witness` (the same designated env readings
`Spec` sees): positional gadgets state "my neighborhood holds honest values" as a
`ProverAssumptions` on the witness. -/
def FormalRegionCircuit.Completeness
    (configure : ConfigInput → Configure F Config)
    (synthesize :
      Config → (offset : ℕ) → Var Input F → RegionCircuit F (Var Output F))
    [elaborated : ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize]
    (config : Config) (offset : ℕ)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    Prop :=
  ∀ (self : RegionIndex) (env : Placed ProverEnvironment F) (input : Var Input F),
  RegionOperations.ExtendsWitnesses env.place self env.env
    ((synthesize config offset input).operations self) →
  EnvAssumptions env.toEnvironment →
  Assumptions (eval env.toEnvironment input) →
  ProverAssumptions (eval env input) (extract input self env.toEnvironment) env.env.hint →
  RegionOperations.Constraints env.place self env.env
    ((synthesize config offset input).operations self) ∧
  ProverSpec (eval env input)
    (eval env (ElaboratedRegionCircuit.output
      configure synthesize config offset input self))
    (extract input self env.toEnvironment) env.env.hint

/-- Equivalence rewriting `Soundness` into a form with the input/output *values* intro'd
as variables (with their defining equations). A proof tactic `rw`s this at the very start,
so the user works with `input`/`output` (finite-field values) instead of `eval env …`. -/
theorem FormalRegionCircuit.soundness_iff
    (configure : ConfigInput → Configure F Config)
    (synthesize :
      Config → (offset : ℕ) → Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize]
    (config : Config) (offset : ℕ)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (Spec : Value Input F → Value Output F → Witness F → Prop) :
    FormalRegionCircuit.Soundness configure synthesize config offset
      extract EnvAssumptions Assumptions Spec ↔
    ∀ (self : RegionIndex) (env : Placed Environment F) (input_var : Var Input F)
      (input : Value Input F) (output : Value Output F),
    eval env input_var = input →
    eval env (ElaboratedRegionCircuit.output
      configure synthesize config offset input_var self) = output →
    EnvAssumptions env →
    Assumptions input →
    RegionOperations.Constraints env.place self env.env
      ((synthesize config offset input_var).operations self) →
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
    (configure : ConfigInput → Configure F Config)
    (synthesize :
      Config → (offset : ℕ) → Var Input F → RegionCircuit F (Var Output F))
    [ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize]
    (config : Config) (offset : ℕ)
    (extract : Var Input F → RegionIndex → Placed Environment F → Witness F)
    (EnvAssumptions : Placed Environment F → Prop)
    (Assumptions : Value Input F → Prop)
    (ProverAssumptions : ProverValue Input F → Witness F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → Witness F → ProverHint F → Prop) :
    FormalRegionCircuit.Completeness configure synthesize config offset
      extract EnvAssumptions Assumptions ProverAssumptions ProverSpec ↔
    ∀ (self : RegionIndex) (env : Placed ProverEnvironment F) (input_var : Var Input F)
      (input : ProverValue Input F) (output : ProverValue Output F),
    eval env input_var = input →
    eval env (ElaboratedRegionCircuit.output
      configure synthesize config offset input_var self) = output →
    RegionOperations.ExtendsWitnesses env.place self env.env
      ((synthesize config offset input_var).operations self) →
    EnvAssumptions env.toEnvironment →
    Assumptions (eval env.toEnvironment input_var) →
    ProverAssumptions input (extract input_var self env.toEnvironment) env.env.hint →
    RegionOperations.Constraints env.place self env.env
      ((synthesize config offset input_var).operations self) ∧
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
  /-- The single reduced interface for both phases. -/
  elaborated :
    ElaboratedRegionCircuit F ConfigInput Config Input Output
      configure synthesize := by
    first
    | infer_instance
    | exact {}

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
    FormalRegionCircuit.Soundness (elaborated := elaborated)
      configure synthesize config offset
      (extract config offset) (EnvAssumptions config) Assumptions Spec
  completeness : ∀ (config : Config) (offset : ℕ),
    FormalRegionCircuit.Completeness (elaborated := elaborated)
      configure synthesize config offset
      (extract config offset) (EnvAssumptions config)
      Assumptions ProverAssumptions ProverSpec

/--
Region-level counterpart of `FormalCircuit.KeygenLawful`.

The operation stream is quantified over both its row offset and ambient region index,
matching every context in which a parent may call the region circuit.
-/
structure FormalRegionCircuit.KeygenLawful
    {ConfigInput Config : Type}
    [CircuitType Input] [CircuitType Output]
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (requirements : KeygenRequirements F ConfigInput (Var Input F) := {}) : Prop where
  registered :
    ∀ (configInput : ConfigInput) (counts : ConfigureCounts)
      (hconfig : requirements.configLawful configInput)
      (offset : ℕ) (input : Var Input F) (region : RegionIndex),
    let program := self.configure configInput
    ((self.synthesize
      (program.output counts) offset input).operations region).Forall
        (RegionOperation.KeygenRegistered
          (requirements.gates configInput hconfig ++ (program.delta counts).gates)
          (requirements.lookups configInput hconfig ++ (program.delta counts).lookups)
          (requirements.permutationColumns configInput hconfig ++
            (program.delta counts).permutationRequests ++
            requirements.inputPermutationColumns configInput hconfig input))

namespace FormalRegionCircuit
variable [CircuitType Input] [CircuitType Output] {ConfigInput Config : Type}

instance (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) :
    ElaboratedConfigure (self.configure input) :=
  self.elaborated.configureInfo input

/-- The folded keygen interface exposed by a region circuit. -/
abbrev keygenRequirements
    (self : FormalRegionCircuit F ConfigInput Config Input Output) :
    KeygenRequirements F ConfigInput (Var Input F) :=
  self.elaborated.keygenRequirements

/-- Region-level configured capability in an ambient keygen context. -/
abbrev ConfigurationCertificate
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (context : KeygenContext F) :=
  Halo2.ConfigurationCertificate self.keygenRequirements self.configure config context

/-- The certificate produced by this region circuit's configure program. -/
def configureCertificate
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    self.ConfigurationCertificate
      ((self.configure configInput).output counts)
      { gates := self.keygenRequirements.gates configInput hconfig ++
          ((self.configure configInput).delta counts).gates
        lookups := self.keygenRequirements.lookups configInput hconfig ++
          ((self.configure configInput).delta counts).lookups
        permutationColumns := self.keygenRequirements.permutationColumns configInput hconfig ++
          ((self.configure configInput).delta counts).permutationRequests } :=
  Halo2.ConfigurationCertificate.ofOutput
    self.keygenRequirements self.configure configInput counts hconfig

/-- Region-level counterpart of `FormalCircuit.Configured`. -/
structure Configured
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) where
  configInput : ConfigInput
  counts : ConfigureCounts
  configLawful :
    self.keygenRequirements.configLawful configInput
  output_eq :
    (self.configure configInput).output counts = config

/-- Forget ambient availability while retaining region-configure provenance. -/
def ConfigurationCertificate.configured
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    self.Configured config :=
  ⟨certificate.configInput, certificate.counts,
    certificate.configLawful, certificate.output_eq⟩

/-- A region circuit's configure output carries folded configuration provenance. -/
abbrev Configured.ofOutput
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    self.Configured ((self.configure configInput).output counts) :=
  ⟨configInput, counts, hconfig, rfl⟩

/-- Region-level pure-configure provenance. -/
def Configured.ofPure
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    self.Configured config :=
  ⟨config, {}, hconfig, by simp [hconfigure]⟩

/-- Gate arguments available from a configured region-circuit handle. -/
def Configured.gates
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) : List (Gate F) :=
  self.keygenRequirements.gates
      (FormalRegionCircuit.Configured.configInput configured)
      (FormalRegionCircuit.Configured.configLawful configured) ++
    ((self.configure (FormalRegionCircuit.Configured.configInput configured)).delta
      (FormalRegionCircuit.Configured.counts configured)).gates

/-- Lookup arguments available from a configured region-circuit handle. -/
def Configured.lookups
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) :
    List (LookupArgument F) :=
  self.keygenRequirements.lookups
      (FormalRegionCircuit.Configured.configInput configured)
      (FormalRegionCircuit.Configured.configLawful configured) ++
    ((self.configure (FormalRegionCircuit.Configured.configInput configured)).delta
      (FormalRegionCircuit.Configured.counts configured)).lookups

/-- Equality-enabled columns available from a configured region-circuit handle. -/
def Configured.permutationColumns
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) : List AnyColumn :=
  self.keygenRequirements.permutationColumns
      (FormalRegionCircuit.Configured.configInput configured)
      (FormalRegionCircuit.Configured.configLawful configured) ++
    ((self.configure (FormalRegionCircuit.Configured.configInput configured)).delta
      (FormalRegionCircuit.Configured.counts configured)).permutationRequests

/-- Equality-enabled columns required by the concrete region-circuit input. -/
def Configured.inputPermutationColumns
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config)
    (input : Var Input F) : List AnyColumn :=
  self.keygenRequirements.inputPermutationColumns
    (FormalRegionCircuit.Configured.configInput configured)
    (FormalRegionCircuit.Configured.configLawful configured) input

/-- Region-level certificate elimination through `Configured.gates`. -/
theorem ConfigurationCertificate.gates_of_configured
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ gate, gate ∈ certificate.configured.gates → gate ∈ context.gates := by
  intro gate hgate
  simpa [Configured.gates, ConfigurationCertificate.configured] using
    certificate.gates gate hgate

/-- Region-level certificate elimination through `Configured.lookups`. -/
theorem ConfigurationCertificate.lookups_of_configured
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ argument,
      argument ∈ certificate.configured.lookups → argument ∈ context.lookups := by
  intro argument hargument
  simpa [Configured.lookups, ConfigurationCertificate.configured] using
    certificate.lookups argument hargument

/-- Region-level certificate elimination through `Configured.permutationColumns`. -/
theorem ConfigurationCertificate.permutationColumns_of_configured
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ column,
      column ∈ certificate.configured.permutationColumns →
        column ∈ context.permutationColumns := by
  intro column hcolumn
  simpa [Configured.permutationColumns, ConfigurationCertificate.configured] using
    certificate.permutationColumns column hcolumn

@[simp, keygen_norm] theorem Configured.ofPure_gates
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.gates (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.gates config hconfig := by
  simp [Configured.gates, Configured.ofPure, hconfigure]

@[simp, keygen_norm] theorem Configured.ofPure_lookups
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.lookups (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.lookups config hconfig := by
  simp [Configured.lookups, Configured.ofPure, hconfigure]

@[keygen_norm] theorem Configured.ofPure_permutationColumns
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.permutationColumns (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.permutationColumns config hconfig := by
  simp [Configured.permutationColumns, Configured.ofPure, hconfigure]

@[keygen_norm] theorem Configured.ofPure_inputPermutationColumns
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config)
    (input : Var Input F) :
    Configured.inputPermutationColumns
        (Configured.ofPure self config hconfig hconfigure) input =
      self.keygenRequirements.inputPermutationColumns config hconfig input := by
  simp [Configured.inputPermutationColumns, Configured.ofPure]

@[simp, keygen_norm] theorem Configured.ofOutput_gates
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    Configured.gates (Configured.ofOutput self configInput counts hconfig) =
      self.keygenRequirements.gates configInput hconfig ++
        ((self.configure configInput).delta counts).gates :=
  rfl

@[simp, keygen_norm] theorem Configured.ofOutput_lookups
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    Configured.lookups (Configured.ofOutput self configInput counts hconfig) =
      self.keygenRequirements.lookups configInput hconfig ++
        ((self.configure configInput).delta counts).lookups :=
  rfl

@[simp, keygen_norm] theorem Configured.ofOutput_configInput
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    FormalRegionCircuit.Configured.configInput
      (Configured.ofOutput self configInput counts hconfig) = configInput :=
  rfl

@[simp, keygen_norm] theorem Configured.ofOutput_counts
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    FormalRegionCircuit.Configured.counts
      (Configured.ofOutput self configInput counts hconfig) = counts :=
  rfl

/-- Region-level counterpart of `FormalCircuit.selectorRequirements`. -/
def selectorRequirements
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts) : Prop :=
  (self.elaborated.configureInfo input).selectorRequirements counts

/-- Region-level counterpart of `FormalCircuit.selectorsAllocated`. -/
theorem selectorsAllocated
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts)
    (hrequirements : self.selectorRequirements input counts) :
    ((self.configure input).delta counts).SelectorsAllocated
      ((self.configure input).finalCounts counts).numSelectors :=
  (self.elaborated.configureInfo input).selectorsAllocated counts hrequirements

/-- Region-level counterpart of `FormalCircuit.lookupSelectorsCompatible`. -/
theorem lookupSelectorsCompatible
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts)
    (hrequirements : self.selectorRequirements input counts) :
    ((self.configure input).delta counts).LookupSelectorsCompatible :=
  (self.elaborated.configureInfo input).lookupSelectorsCompatible
    counts hrequirements

/-- Region-level counterpart of `FormalCircuit.queryRequirements`. -/
def queryRequirements
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts) : Prop :=
  (self.elaborated.configureInfo input).queryRequirements counts

/-- Region-level counterpart of `FormalCircuit.queriesLawful`. -/
theorem queriesLawful
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (input : ConfigInput) (counts : ConfigureCounts)
    (hrequirements : self.queryRequirements input counts) :
    ((self.configure input).delta counts).QueriesLawful
      ((self.configure input).finalCounts counts) :=
  (self.elaborated.configureInfo input).queriesLawful counts hrequirements

/-- The output variable of the region circuit, in the ambient region. -/
def output (self : FormalRegionCircuit F ConfigInput Config Input Output) (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) : Var Output F :=
  self.elaborated.output config offset input region

/-- The whole region-level `call` runtime pair, packaged with its defining equation behind
an `opaque` reduction barrier; see `FormalCircuit.callPacked` for the two-jobs design. The
implementation applies the child monad `synthesize` **exactly once** and reads both the
output and the operations off that single application (runtime: no metadata
re-materialization); the `opaque` is the kernel + elaborator reduction barrier, and the
packaged `property` re-exposes the equation (`call_eq`/`call_operations`). -/
@[keygen_call_expression]
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
        (self.elaborated.output_eq config offset input region).symm
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

/-- A region call exposes the child's exact reduced synthesis footprint. -/
@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((self.call config offset input).operations region) =
      self.elaborated.synthesisSummary config offset input region := by
  rw [self.call_operations]
  exact (self.elaborated.synthesisSummary_eq config offset input region).symm

@[circuit_norm, synthesis_summary_norm]
theorem call_synthesisSummary' {Output : TypeMap} [ProvableType Output]
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset : ℕ) (input : Var Input F)
    (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        (@RegionCircuit.operations F _ (Output (AssignedCell F))
          (self.call config offset input) region) =
      self.elaborated.synthesisSummary config offset input region :=
  self.call_synthesisSummary config offset input region

/-- A fixed-stride loop of region-circuit calls reduces to the fold of the children'
already-reduced summaries. The result is the synthesis-summary normal form for
composite gadgets built from homogeneous child circuits. -/
@[synthesis_summary_norm]
theorem forRange'_call_synthesisSummary
    (circuits : ℕ → FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (offset stride count : ℕ)
    (inputs : ℕ → Var Input F) (region : RegionIndex) :
    FloorPlanner.regionSynthesisSummary
        ((RegionCircuit.forRange' offset stride count fun i row => do
          let _ ← (circuits i).call config row (inputs i)
          pure ()).operations region) =
      (List.ofFn fun i : Fin count =>
        (circuits i.val).elaborated.synthesisSummary config
          (offset + i.val * stride) (inputs i.val) region).foldr
            FloorPlanner.RegionSynthesisSummary.combine {} := by
  rw [RegionCircuit.forRange'_regionSynthesisSummary]
  apply congrArg (List.foldr FloorPlanner.RegionSynthesisSummary.combine {})
  apply congrArg List.ofFn
  funext i
  simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
    List.append_nil]
  exact (circuits i.val).call_synthesisSummary config
    (offset + i.val * stride) (inputs i.val) region

/-- Consume a region circuit's configure certificate without exposing routing premises. -/
@[keygen_norm]
theorem call_keygenRegistered_ofCertificate
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    (hinputPermutationColumns : ∀ column,
      column ∈ certificate.configured.inputPermutationColumns input →
      column ∈ context.permutationColumns) :
    ((self.call config offset input).operations region).Forall
      (RegionOperation.KeygenRegistered context.gates context.lookups
        context.permutationColumns) := by
  rcases certificate with
    ⟨configInput, counts, hconfig, output_eq, gates, lookups, permutationColumns⟩
  subst config
  rw [self.call_operations]
  exact RegionOperations.keygenRegistered_mono
    (self.elaborated.registered
      configInput counts hconfig offset input region)
    gates lookups (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact permutationColumns column (by
          simpa only [List.mem_append] using hcolumn)
      · exact hinputPermutationColumns column (by
          simpa [Configured.inputPermutationColumns,
            ConfigurationCertificate.configured] using hcolumn))

/--
Region-level counterpart of `FormalCircuit.call_keygenRegistered`.
-/
@[keygen_norm]
theorem call_keygenRegistered
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ Configured.gates hconfigured →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ Configured.lookups hconfigured →
        argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ Configured.permutationColumns hconfigured →
        column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈ Configured.inputPermutationColumns hconfigured input →
        column ∈ targetPermutationColumns) :
    ((self.call config offset input).operations region).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetPermutationColumns) := by
  rcases hconfigured with ⟨configInput, counts, hconfig, rfl⟩
  rw [self.call_operations]
  exact RegionOperations.keygenRegistered_mono
    (self.elaborated.registered
      configInput counts hconfig offset input region)
    (by simpa [Configured.gates] using hgates)
    (by simpa [Configured.lookups] using hlookups)
    (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact hpermutationColumns column (by
          simpa [Configured.permutationColumns] using hcolumn)
      · exact hinputPermutationColumns column (by
          simpa [Configured.inputPermutationColumns] using hcolumn))

/-- Region-level registration certificate specialized to a configure output. -/
theorem call_keygenRegistered_ofOutput
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates : ∀ gate,
      gate ∈ self.keygenRequirements.gates configInput hconfig ++
        ((self.configure configInput).delta counts).gates →
      gate ∈ targetGates)
    (hlookups : ∀ argument,
      argument ∈ self.keygenRequirements.lookups configInput hconfig ++
        ((self.configure configInput).delta counts).lookups →
      argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ self.keygenRequirements.permutationColumns configInput hconfig ++
        ((self.configure configInput).delta counts).permutationRequests →
      column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈
        self.keygenRequirements.inputPermutationColumns configInput hconfig input →
      column ∈ targetPermutationColumns) :
    ((self.call ((self.configure configInput).output counts) offset input).operations
      region).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetPermutationColumns) := by
  apply self.call_keygenRegistered _
      (Configured.ofOutput self configInput counts hconfig)
  · simpa [Configured.gates, Configured.ofOutput] using hgates
  · simpa [Configured.lookups, Configured.ofOutput] using hlookups
  · simpa [Configured.permutationColumns, Configured.ofOutput] using
      hpermutationColumns
  · simpa [Configured.inputPermutationColumns, Configured.ofOutput] using
      hinputPermutationColumns

/-- Region-level exact-arguments counterpart of
`FormalCircuit.call_keygenRegistered_exact`. -/
theorem call_keygenRegistered_exact
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    ((self.call config offset input).operations region).Forall
      (RegionOperation.KeygenRegistered
        hconfigured.gates hconfigured.lookups
          (hconfigured.permutationColumns ++
            hconfigured.inputPermutationColumns input)) :=
  self.call_keygenRegistered config hconfigured offset input region
    (fun _ h => h) (fun _ h => h)
    (fun _ h => List.mem_append_left _ h)
    (fun _ h => List.mem_append_right _ h)

/-- Lookup activations in a region child call obey the lookup's local selector declaration. -/
theorem call_lookupActivationsWellFormed
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    ((self.call config offset input).operations region)
      |>.LookupActivationsWellFormed := by
  rw [self.call_operations]
  exact self.elaborated.lookupActivationsWellFormed
    config offset input region

/-- Region lookup-activation certificate in the opaque call spelling. -/
theorem callPacked_lookupActivationsWellFormed
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex) :
    (((callPacked F ConfigInput Config Input Output).val self
      config offset input region).2)
        |>.LookupActivationsWellFormed :=
  self.call_lookupActivationsWellFormed
    config offset input region

/-- Region registration certificate in the opaque spelling exposed after spine
normalization. -/
theorem callPacked_keygenRegistered
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (config : Config) (hconfigured : self.Configured config)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ Configured.gates hconfigured →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ Configured.lookups hconfigured →
        argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ Configured.permutationColumns hconfigured →
        column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈ Configured.inputPermutationColumns hconfigured input →
        column ∈ targetPermutationColumns) :
    (((callPacked F ConfigInput Config Input Output).val
      self config offset input region).2).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetPermutationColumns) :=
  call_keygenRegistered self config hconfigured offset input region hgates hlookups
    hpermutationColumns hinputPermutationColumns

/--
A lawful region child remains registered when called inside a parent whose available
argument lists contain the child's requirements and configure contribution.
-/
theorem KeygenLawful.call_registered
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {requirements : KeygenRequirements F ConfigInput (Var Input F)}
    (hlawful : self.KeygenLawful requirements)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : requirements.configLawful configInput)
    (offset : ℕ) (input : Var Input F) (region : RegionIndex)
    {targetGates : List (Gate F)}
    {targetLookups : List (LookupArgument F)}
    {targetPermutationColumns : List AnyColumn}
    (hgates :
      ∀ gate,
        gate ∈ requirements.gates configInput hconfig ++
          ((self.configure configInput).delta counts).gates →
        gate ∈ targetGates)
    (hlookups :
      ∀ argument,
        argument ∈ requirements.lookups configInput hconfig ++
          ((self.configure configInput).delta counts).lookups →
        argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ requirements.permutationColumns configInput hconfig ++
        ((self.configure configInput).delta counts).permutationRequests →
      column ∈ targetPermutationColumns)
    (hinputPermutationColumns : ∀ column,
      column ∈
        requirements.inputPermutationColumns configInput hconfig input →
      column ∈ targetPermutationColumns) :
    ((self.call
      ((self.configure configInput).output counts)
      offset input).operations region).Forall
        (RegionOperation.KeygenRegistered targetGates targetLookups
          targetPermutationColumns) := by
  rw [self.call_operations]
  exact RegionOperations.keygenRegistered_mono
    (FormalRegionCircuit.KeygenLawful.registered
      hlawful configInput counts hconfig offset input region)
    hgates hlookups (by
      intro column hcolumn
      simp only [List.mem_append] at hcolumn
      rcases hcolumn with hcolumn | hcolumn
      · exact hpermutationColumns column (by
          simpa only [List.mem_append] using hcolumn)
      · exact hinputPermutationColumns column hcolumn)

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
  elaborated :=
    { configureInfo := child.elaborated.configureInfo
      keygenRequirements := child.elaborated.keygenRequirements
      registered := by
        intro configInput counts hconfig input region
        have hregistered := child.elaborated.registered
          configInput counts hconfig 0 input region
        simpa only [assignRegion, Circuit.operations,
          Operations.KeygenRegistered, Operation.KeygenRegistered,
          List.Forall, and_true] using hregistered
      copyCellsAssigned := by
        intro configInput counts hconfig input region
        have hassigned := child.elaborated.copyCellsAssigned
          configInput counts hconfig 0 input region
        simpa [assignRegion, Circuit.operations,
          Operations.CopyCellsAssigned, Operations.copiedCells,
          Operations.assignedCellsFrom, RegionOperations.CopyCellsAssigned] using hassigned
      lookupActivationsWellFormed := by
        intro config input region
        have hlawful := child.elaborated.lookupActivationsWellFormed
          config 0 input region
        simpa only [assignRegion, Circuit.operations,
          Operations.LookupActivationsWellFormed,
          Operation.LookupActivationsWellFormed, List.Forall, and_true] using hlawful
      output config input i :=
        child.output config 0 input i
      regionCount _ := 1
      synthesisSummary config input region :=
        FloorPlanner.SynthesisSummary.ofRegion
          (child.elaborated.synthesisSummary config 0 input region)
      output_eq := by
        intro config input i
        rw [output_assignRegion]
        exact child.elaborated.output_eq config 0 input i
      regionCount_eq := by
        intro _ _ _
        simp only [assignRegion, Circuit.operations, Operations.regionCount]
      synthesisSummary_eq := by
        intro config input region
        simp only [assignRegion, Circuit.operations,
          FloorPlanner.synthesisSummary]
        have hsummary :
            child.elaborated.synthesisSummary config 0 input region =
              FloorPlanner.regionSynthesisSummary
                (child.synthesize config 0 input region).2 := by
          simpa only [RegionCircuit.operations] using
            child.elaborated.synthesisSummary_eq config 0 input region
        rw [← hsummary]
        exact FloorPlanner.SynthesisSummary.combine_empty _ |>.symm }
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
    exact child.soundness config 0 i₀ env input_var hE hA hC.1

  completeness := by
    intro config
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_in h_out hW hE hA hpa
    simp only [Circuit.operations, assignRegion,
      Halo2.ExtendsWitnesses, Halo2.Constraints] at hW ⊢
    subst h_in h_out
    -- instantiate the child's region-level completeness at `self := i₀`
    have hcompl := child.completeness config 0 i₀ env input_var hW.1 hE hA hpa
    exact ⟨⟨hcompl.1, trivial⟩, hcompl.2⟩

@[simp, keygen_norm]
theorem toFormal_keygenRequirements
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String := child.name) :
    (child.toFormal name).keygenRequirements =
      child.keygenRequirements :=
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary_columns
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) :
    ((child.toFormal name).elaborated.synthesisSummary
      config input region).columns =
        (child.elaborated.synthesisSummary config 0 input region).columns := rfl

/-- Lifting a region circuit turns its reduced region footprint into the corresponding
single-region layouter footprint. -/
@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) :
    (child.toFormal name).elaborated.synthesisSummary config input region =
      FloorPlanner.SynthesisSummary.ofRegion
        (child.elaborated.synthesisSummary config 0 input region) := rfl

@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary_columnOccupancy
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) (column : FloorPlanner.RegionColumn) :
    ((child.toFormal name).elaborated.synthesisSummary
      config input region).columnOccupancy column =
        if column ∈ (child.elaborated.synthesisSummary
          config 0 input region).columns then
          (child.elaborated.synthesisSummary config 0 input region).rowCount
        else 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem toFormal_synthesisSummary_constantSiteCount
    (child : FormalRegionCircuit F ConfigInput Config Input Output)
    (name : String) (config : Config) (input : Var Input F)
    (region : RegionIndex) :
    ((child.toFormal name).elaborated.synthesisSummary
      config input region).constantSiteCount =
        (child.elaborated.synthesisSummary
          config 0 input region).constantSiteCount := rfl

/-- A region circuit's configured handle remains valid after lifting it to the
layouter level. -/
def Configured.toFormal
    {child : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} {name : String}
    (configured : child.Configured config) :
    (child.toFormal name).Configured config := by
  rcases configured with ⟨configInput, counts, hconfig, output_eq⟩
  exact ⟨configInput, counts, hconfig, output_eq⟩

/-- The region-to-layouter bridge preserves configure/synthesis keygen lawfulness. -/
theorem KeygenLawful.toFormal
    {child : FormalRegionCircuit F ConfigInput Config Input Output}
    {requirements : KeygenRequirements F ConfigInput (Var Input F)}
    (hlawful : child.KeygenLawful requirements) (name : String := child.name) :
    (child.toFormal name).KeygenLawful requirements where
  registered := by
    intro configInput counts hconfig input region
    have hregistered :=
      FormalRegionCircuit.KeygenLawful.registered
        hlawful configInput counts hconfig 0 input region
    simpa only [toFormal, assignRegion, Circuit.operations,
      Operations.KeygenRegistered, Operation.KeygenRegistered,
      List.Forall, and_true] using hregistered

end FormalRegionCircuit

attribute [keygen_call]
  FormalCircuit.callPacked_keygenRegistered
  FormalCircuit.call_keygenRegistered
  FormalCircuit.callPacked_lookupActivationsWellFormed
  FormalCircuit.call_lookupActivationsWellFormed
  FormalRegionCircuit.callPacked_keygenRegistered
  FormalRegionCircuit.call_keygenRegistered
  FormalRegionCircuit.callPacked_lookupActivationsWellFormed
  FormalRegionCircuit.call_lookupActivationsWellFormed

attribute [keygen_call_expression]
  FormalCircuit.call
  FormalRegionCircuit.call

attribute [keygen_call_bundle]
  FormalCircuit
  FormalRegionCircuit

attribute [keygen_configured]
  FormalCircuit.Configured.ofOutput
  FormalCircuit.Configured.ofPure
  FormalRegionCircuit.Configured.ofOutput
  FormalRegionCircuit.Configured.ofPure

attribute [keygen_configured_output FormalCircuit.configure]
  FormalCircuit.Configured.ofOutput

attribute [keygen_configured_pure FormalCircuit.configure]
  FormalCircuit.Configured.ofPure

attribute [keygen_configured_output FormalRegionCircuit.configure]
  FormalRegionCircuit.Configured.ofOutput

attribute [keygen_configured_pure FormalRegionCircuit.configure]
  FormalRegionCircuit.Configured.ofPure

attribute [keygen_bundle_projection]
  ElaboratedCircuit.keygenRequirements
  FormalCircuit.configure
  FormalCircuit.synthesize
  FormalCircuit.elaborated
  FormalCircuit.keygenRequirements
  ElaboratedRegionCircuit.keygenRequirements
  FormalRegionCircuit.configure
  FormalRegionCircuit.synthesize
  FormalRegionCircuit.elaborated
  FormalRegionCircuit.keygenRequirements

attribute [keygen_requirement_projection]
  ElaboratedCircuit.keygenRequirements
  FormalCircuit.keygenRequirements
  ElaboratedRegionCircuit.keygenRequirements
  FormalRegionCircuit.keygenRequirements

attribute [keygen_metadata_projection]
  FormalRegionCircuit.toFormal
  FormalCircuit.configure
  FormalCircuit.elaborated
  ElaboratedCircuit.keygenRequirements
  FormalCircuit.keygenRequirements
  FormalRegionCircuit.configure
  FormalRegionCircuit.elaborated
  ElaboratedRegionCircuit.keygenRequirements
  FormalRegionCircuit.keygenRequirements

attribute [keygen_configure_projection]
  FormalCircuit.configure
  FormalRegionCircuit.configure

open Lean Meta Simp in
/-- Reduce a concrete circuit's declared output metadata without adding a projection
lemma for every circuit bundle. Circuits with a reduced elaborated `output` field stop
at that field; opaque or still-symbolic bundles are left unchanged. -/
def foldDeclaredOutputProc : Simproc := fun expression => do
  let isRegion := expression.isAppOf ``FormalRegionCircuit.output
  unless expression.isAppOf ``FormalCircuit.output || isRegion do
    return .continue
  try
    let arguments := expression.getAppArgs
    let explicitArity := if isRegion then 5 else 4
    unless explicitArity ≤ arguments.size do
      return .continue
    let self := arguments[arguments.size - explicitArity]!
    let some unfoldedSelf ← withTransparency .default <| unfoldDefinition? self
      | return .continue
    let some unfoldedOutput ←
        withTransparency .default <| unfoldDefinition? expression
      | return .continue
    let withBundle := unfoldedOutput.replace fun candidate =>
      if candidate == self then some unfoldedSelf else none
    let withBundle ← withTransparency .reducible <| whnf withBundle
    let elaboratedOutput :=
      if isRegion then ``ElaboratedRegionCircuit.output else ``ElaboratedCircuit.output
    let some outputProjection := withBundle.find? fun candidate =>
        candidate.getAppFn.isConstOf elaboratedOutput
      | return .continue
    let some projectionInfo ← getProjectionFnInfo? elaboratedOutput
      | return .continue
    let projectionArguments := outputProjection.getAppArgs
    unless projectionInfo.numParams < projectionArguments.size do
      return .continue
    let elaborated := projectionArguments[projectionInfo.numParams]!
    let reducedElaborated ← withTransparency .default <| whnf elaborated
    let reducedElaborated ←
      if reducedElaborated != elaborated then
        pure reducedElaborated
      else
        match ← withTransparency .default <| unfoldDefinition? elaborated with
        | some unfoldedElaborated => pure unfoldedElaborated
        | none => pure elaborated
    let withElaborated := withBundle.replace fun candidate =>
      if candidate == elaborated then some reducedElaborated else none
    let reduced ← withTransparency .reducible <| whnf withElaborated
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldFormalCircuitDeclaredOutput
    (FormalCircuit.output _ _ _ _) := foldDeclaredOutputProc

simproc foldFormalRegionCircuitDeclaredOutput
    (FormalRegionCircuit.output _ _ _ _ _) := foldDeclaredOutputProc

attribute [keygen_output_norm]
  foldFormalCircuitDeclaredOutput
  foldFormalRegionCircuitDeclaredOutput

open Lean Meta Simp in
/-- Reduce a configured circuit's declared input-dependent equality requirements.
This is the keygen analogue of `foldDeclaredOutputProc`: it exposes only the small
`KeygenRequirements.inputPermutationColumns` field and never unfolds synthesis. -/
def foldDeclaredInputPermutationColumnsProc : Simproc := fun expression => do
  let isRegion :=
    expression.isAppOf ``FormalRegionCircuit.Configured.inputPermutationColumns
  unless expression.isAppOf ``FormalCircuit.Configured.inputPermutationColumns ||
      isRegion do
    return .continue
  try
    let arguments := expression.getAppArgs
    unless 4 ≤ arguments.size do
      return .continue
    let self := arguments[arguments.size - 4]!
    let some unfoldedSelf ← withTransparency .default <| unfoldDefinition? self
      | return .continue
    let some unfoldedProjection ←
        withTransparency .default <| unfoldDefinition? expression
      | return .continue
    let withBundle := unfoldedProjection.replace fun candidate =>
      if candidate == self then some unfoldedSelf else none
    let withBundle ← withTransparency .default <| whnf withBundle
    let some requirementProjection := withBundle.find? fun candidate =>
        candidate.getAppFn.isConstOf ``KeygenRequirements.inputPermutationColumns
      | if withBundle == expression then
          return .continue
        let proof ← mkExpectedTypeHint
          (← mkEqRefl expression) (← mkEq expression withBundle)
        return .visit { expr := withBundle, proof? := some proof }
    let requirementArguments := requirementProjection.getAppArgs
    unless 3 < requirementArguments.size do
      return .continue
    let requirements := requirementArguments[3]!
    let reducedRequirements ← withTransparency .default <| whnf requirements
    let reducedRequirements ←
      if reducedRequirements != requirements then
        pure reducedRequirements
      else
        match ← withTransparency .default <| unfoldDefinition? requirements with
        | some unfoldedRequirements => pure unfoldedRequirements
        | none => pure requirements
    let withRequirements := withBundle.replace fun candidate =>
      if candidate == requirements then some reducedRequirements else none
    let reduced ← withTransparency .reducible <| whnf withRequirements
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldFormalCircuitDeclaredInputPermutationColumns
    (FormalCircuit.Configured.inputPermutationColumns _ _) :=
  foldDeclaredInputPermutationColumnsProc

simproc foldFormalRegionCircuitDeclaredInputPermutationColumns
    (FormalRegionCircuit.Configured.inputPermutationColumns _ _) :=
  foldDeclaredInputPermutationColumnsProc

attribute [keygen_norm]
  foldFormalCircuitDeclaredInputPermutationColumns
  foldFormalRegionCircuitDeclaredInputPermutationColumns

attribute [grind norm]
  FormalCircuit.Configured.ofPure_gates
  FormalCircuit.Configured.ofPure_lookups
  FormalCircuit.Configured.ofOutput_gates
  FormalCircuit.Configured.ofOutput_lookups
  FormalCircuit.Configured.ofOutput_configInput
  FormalCircuit.Configured.ofOutput_counts
  FormalRegionCircuit.Configured.ofPure_gates
  FormalRegionCircuit.Configured.ofPure_lookups
  FormalRegionCircuit.Configured.ofOutput_gates
  FormalRegionCircuit.Configured.ofOutput_lookups
  FormalRegionCircuit.Configured.ofOutput_configInput
  FormalRegionCircuit.Configured.ofOutput_counts

end Halo2
