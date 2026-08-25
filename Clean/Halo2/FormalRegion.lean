import Clean.Halo2.Formal.Call

namespace Halo2

variable {F : Type} [FiniteField F] {Input Output Witness : TypeMap}

/-! ## Region-level formal circuits

The region-level analogue of `FormalCircuit`, for `assign_region` fragments composed
*inside* a parent region at region-local rows (e.g. `add_incomplete.assign_region`
called inside variable-base mul's big region). It lives in the ambient region `self` and
creates no new regions — so, unlike `FormalCircuit`, there is no `i₀`/`regionCount`; the
constraints are `RegionOperations.Constraints` at the ambient `self`.
-/

namespace FormalRegionCircuit

section RegionStatements
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}

/-- Soundness of a region-level circuit (verifier view). If the constraints of `main`
hold in the ambient region `self`, then `Spec` holds on the input, extracted witness,
and output. -/
def Soundness
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
def Completeness
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
theorem soundness_iff
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
theorem completeness_iff
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

end FormalRegionCircuit

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
@[keygen_call_bundle]
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

attribute [keygen_bundle_projection, keygen_metadata_projection,
    keygen_configure_projection]
  FormalRegionCircuit.configure

attribute [keygen_bundle_projection]
  FormalRegionCircuit.synthesize

attribute [keygen_bundle_projection, keygen_metadata_projection]
  FormalRegionCircuit.elaborated

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
          (requirements.fixedColumns configInput hconfig ++
            program.fixedColumns counts)
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
@[keygen_bundle_projection, keygen_requirement_projection,
  keygen_metadata_projection]
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
        fixedColumns := self.keygenRequirements.fixedColumns configInput hconfig ++
          (self.configure configInput).fixedColumns counts
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
@[keygen_configured, keygen_configured_output FormalRegionCircuit.configure]
abbrev Configured.ofOutput
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    self.Configured ((self.configure configInput).output counts) :=
  ⟨configInput, counts, hconfig, rfl⟩

/-- Region-level pure-configure provenance. -/
@[keygen_configured, keygen_configured_pure FormalRegionCircuit.configure]
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

/-- Fixed columns available from a configured region-circuit handle. -/
def Configured.fixedColumns
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) :
    List (Column .fixed) :=
  self.keygenRequirements.fixedColumns
      (FormalRegionCircuit.Configured.configInput configured)
      (FormalRegionCircuit.Configured.configLawful configured) ++
    (self.configure
      (FormalRegionCircuit.Configured.configInput configured)).fixedColumns
      (FormalRegionCircuit.Configured.counts configured)

/-- Constants columns available from a configured region-circuit handle. -/
def Configured.constantColumns
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) :
    List (Column .fixed) :=
  self.keygenRequirements.constantColumns
      (FormalRegionCircuit.Configured.configInput configured)
      (FormalRegionCircuit.Configured.configLawful configured) ++
    ((self.configure
      (FormalRegionCircuit.Configured.configInput configured)).delta
      (FormalRegionCircuit.Configured.counts configured)).constants

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

/-- Cells supplied by the concrete input of this region call. -/
def Configured.inputCells
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config)
    (input : Var Input F) : List Cell :=
  self.keygenRequirements.inputCells
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

/-- Region-level certificate elimination through `Configured.fixedColumns`. -/
theorem ConfigurationCertificate.fixedColumns_of_configured
    {self : FormalRegionCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ column,
      column ∈ certificate.configured.fixedColumns →
        column ∈ context.fixedColumns := by
  intro column hcolumn
  simpa [Configured.fixedColumns, ConfigurationCertificate.configured] using
    certificate.fixedColumns column hcolumn

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

@[simp, keygen_norm, grind =] theorem Configured.ofPure_gates
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.gates (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.gates config hconfig := by
  simp [Configured.gates, Configured.ofPure, hconfigure]

@[simp, keygen_norm, grind =] theorem Configured.ofPure_lookups
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.lookups (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.lookups config hconfig := by
  simp [Configured.lookups, Configured.ofPure, hconfigure]

@[simp, keygen_norm] theorem Configured.ofPure_fixedColumns
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.fixedColumns (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.fixedColumns config hconfig := by
  simp [Configured.fixedColumns, Configured.ofPure, hconfigure]

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

@[keygen_norm] theorem Configured.ofPure_inputCells
    (self : FormalRegionCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config)
    (input : Var Input F) :
    Configured.inputCells
        (Configured.ofPure self config hconfig hconfigure) input =
      self.keygenRequirements.inputCells config hconfig input := by
  simp [Configured.inputCells, Configured.ofPure]

@[simp, keygen_norm, grind =] theorem Configured.ofOutput_gates
    (self : FormalRegionCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    Configured.gates (Configured.ofOutput self configInput counts hconfig) =
      self.keygenRequirements.gates configInput hconfig ++
        ((self.configure configInput).delta counts).gates :=
  rfl

@[simp, keygen_norm, grind =] theorem Configured.ofOutput_lookups
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

attribute [grind norm]
  Configured.ofOutput_configInput
  Configured.ofOutput_counts

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


end FormalRegionCircuit

end Halo2
