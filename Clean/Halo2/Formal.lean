import Clean.Halo2.Elaborated

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

namespace FormalCircuit

section Statements
variable [CircuitType Input] [CircuitType Output]
    {ConfigInput Config : Type}

/-- Soundness (verifier view — hints erased). If the constraints of `main` hold at
placement `place` from region index `i₀`, then `Spec` holds on the input, the extracted
high-level witness, and the output. -/
def Soundness
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
def Completeness
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
theorem soundness_iff
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
theorem completeness_iff
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

end FormalCircuit

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
@[keygen_call_bundle]
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

attribute [keygen_bundle_projection, keygen_metadata_projection,
    keygen_configure_projection]
  FormalCircuit.configure

attribute [keygen_bundle_projection]
  FormalCircuit.synthesize

attribute [keygen_bundle_projection, keygen_metadata_projection]
  FormalCircuit.elaborated

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
      (requirements.fixedColumns configInput hconfig ++
        program.fixedColumns counts)
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
@[keygen_bundle_projection, keygen_requirement_projection,
  keygen_metadata_projection]
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
        fixedColumns := self.keygenRequirements.fixedColumns configInput hconfig ++
          (self.configure configInput).fixedColumns counts
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
@[keygen_configured, keygen_configured_output FormalCircuit.configure]
abbrev Configured.ofOutput
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    self.Configured ((self.configure configInput).output counts) :=
  ⟨configInput, counts, hconfig, rfl⟩

/-- A pure configure wrapper preserves a caller-supplied config at any allocation state. -/
@[keygen_configured, keygen_configured_pure FormalCircuit.configure]
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

/-- Fixed columns available from a configured circuit handle. -/
def Configured.fixedColumns
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) :
    List (Column .fixed) :=
  self.keygenRequirements.fixedColumns
      (FormalCircuit.Configured.configInput configured)
      (FormalCircuit.Configured.configLawful configured) ++
    (self.configure (FormalCircuit.Configured.configInput configured)).fixedColumns
      (FormalCircuit.Configured.counts configured)

/-- Constants columns available from a configured circuit handle. -/
def Configured.constantColumns
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config) :
    List (Column .fixed) :=
  self.keygenRequirements.constantColumns
      (FormalCircuit.Configured.configInput configured)
      (FormalCircuit.Configured.configLawful configured) ++
    ((self.configure
      (FormalCircuit.Configured.configInput configured)).delta
      (FormalCircuit.Configured.counts configured)).constants

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

/-- Cells supplied by the concrete input of this call. -/
def Configured.inputCells
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} (configured : self.Configured config)
    (input : Var Input F) : List Cell :=
  self.keygenRequirements.inputCells
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

/-- Use a layouter certificate through `Configured.fixedColumns`. -/
theorem ConfigurationCertificate.fixedColumns_of_configured
    {self : FormalCircuit F ConfigInput Config Input Output}
    {config : Config} {context : KeygenContext F}
    (certificate : self.ConfigurationCertificate config context) :
    ∀ column,
      column ∈ certificate.configured.fixedColumns →
        column ∈ context.fixedColumns := by
  intro column hcolumn
  simpa [Configured.fixedColumns, ConfigurationCertificate.configured] using
    certificate.fixedColumns column hcolumn

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

@[simp, keygen_norm, grind =] theorem Configured.ofPure_gates
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.gates (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.gates config hconfig := by
  simp [Configured.gates, Configured.ofPure, hconfigure]

@[simp, keygen_norm, grind =] theorem Configured.ofPure_lookups
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.lookups (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.lookups config hconfig := by
  simp [Configured.lookups, Configured.ofPure, hconfigure]

@[simp, keygen_norm] theorem Configured.ofPure_fixedColumns
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config) :
    Configured.fixedColumns (Configured.ofPure self config hconfig hconfigure) =
      self.keygenRequirements.fixedColumns config hconfig := by
  simp [Configured.fixedColumns, Configured.ofPure, hconfigure]

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

@[keygen_norm] theorem Configured.ofPure_inputCells
    (self : FormalCircuit F Config Config Input Output)
    (config : Config)
    (hconfig : self.keygenRequirements.configLawful config)
    (hconfigure : self.configure config = pure config)
    (input : Var Input F) :
    Configured.inputCells
        (Configured.ofPure self config hconfig hconfigure) input =
      self.keygenRequirements.inputCells config hconfig input := by
  simp [Configured.inputCells, Configured.ofPure]

@[simp, keygen_norm, grind =] theorem Configured.ofOutput_gates
    (self : FormalCircuit F ConfigInput Config Input Output)
    (configInput : ConfigInput) (counts : ConfigureCounts)
    (hconfig : self.keygenRequirements.configLawful configInput) :
    Configured.gates (Configured.ofOutput self configInput counts hconfig) =
      self.keygenRequirements.gates configInput hconfig ++
        ((self.configure configInput).delta counts).gates :=
  rfl

@[simp, keygen_norm, grind =] theorem Configured.ofOutput_lookups
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

attribute [grind norm]
  Configured.ofOutput_configInput
  Configured.ofOutput_counts

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

end FormalCircuit

end Halo2
