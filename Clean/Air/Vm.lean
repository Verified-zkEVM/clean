module

public import Clean.Air.FlatEnsemble
public import Clean.Air.OrderedChannel

@[expose] public section

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-
## VM ensembles

VM-like ensembles have a "main channel" that stores the VM state, which we'll call a _VM channel_.
One or more tables pull from, then push to, this channel in their row circuit; thereby performing
one VM transition.

The public input/output of such an ensemble is the initial push (initial state) and the final pull
(final state). The statement to prove is that there exists a sequence of valid VM transitions from
the initial state to the final state. Note that this does not, in general, require that every row in
the trace participates in a single transition path! In addition to the main (valid) transition path,
there can be additional closed cycles of VM steps.

What is more, the unused cycles can be "invalid": nothing forces their states to be reachable from
the initial state. Consequently, from the assumptions (constraints + balance), we _cannot_ prove a
property of all states on a VM channel, like we did above for the guarantees of `SoundChannels`.

Instead, a VM describes the states it reaches after `k` steps, `VmTables.Reached`, and the spec of
every VM table says that an enabled row takes a state reached after `k` steps to one reached after
`k + 1` steps. The verifier pushes the initial state, which is reached after `0` steps, and pulls
the final state. Balance lets us follow the transitions backwards from the final state to the
initial state, which shows that the final state is reached after `k` steps, for `k` at most the
number of VM rows. The balance check is sound for the number of interactions with the VM channel,
which bounds `k` as well: for LogUp, `k` is less than the characteristic, so that a step counter in
the field doesn't wrap around.

The main proof idea is captured by `exists_reached_of_perm` in `Balance.lean`, a theorem which
states the VM interaction situation in an abstract setting.

Here, we introduce the `VmTables` structure (capturing basic assumptions we put on a VM definition)
as well as the `SoundVmChannel` property (capturing what we mean with soundness for a VM), and then
go on to prove our main theorem, `addVm_soundVmChannel_of_soundChannels`, which shows soundness for
a VM added on top of a `SoundChannels` ensemble.
-/

namespace Air.Flat

structure VmStep (Message : TypeMap) [ProvableType Message] (F : Type) where
  enabled : Expression F
  pull : Var Message F
  push : Var Message F

structure VmTables (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : Channel F Message
  /-- The states that the VM reaches after `k` steps from its initial state. -/
  Reached : ℕ → Message F → ProverData F → Prop
  /-- Reached states satisfy the guarantees of the channel. -/
  guarantees_of_reached : ∀ k state data, Reached k state data → channel.Guarantees state data

  tables : List (Component F)
  unique_names : (tables.map (·.circuit.name)).Nodup := by simp
  verifier : Verifier.Program F PublicIO
  /-- The final state, which the verifier pulls, as a function of the public input. -/
  final : PublicIO F → Message F

  -- Each row of a table performs one step: if enabled, it pulls a state and pushes the next state,
  -- and the table's spec says that the next state is reached one step after the pulled one.
  tables_channel : tables.Forall fun table =>
    ∃ enabled : Expression F, ∃ pull push : Var Message F,
      ⟨ channel, [(channel.pulledIf enabled pull).toRaw, (channel.pushedIf enabled push).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      (∀ env, ConstraintsHold.Shallow env table.rowOperations →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1) ∧
      ∀ env, table.circuit.Spec (eval env table.rowInputVar) (table.rowOutput env) env.data →
        Expression.eval env enabled = 1 →
        ∀ k, Reached k (eval env pull) env.data → Reached (k + 1) (eval env push) env.data

  -- On the VM channel, the public verifier pulls the final state and pushes the initial state,
  -- which is reached after `0` steps. Its interactions on other channels are unconstrained.
  verifier_channel : ∃ pull push : Var Message F,
    verifier.circuitOperations.interactionsWith channel.toRaw =
      [(channel.pulled pull).toRaw, (channel.pushed push).toRaw] ∧
    ∀ data : ProverData F,
      eval data.publicEnvironment pull = final (data.getPublicInput PublicIO) ∧
      Reached 0 (eval data.publicEnvironment push) data

instance (vm : VmTables F PublicIO) : ProvableType vm.Message := vm.provableMessage

/--
What a VM shows about its public input: the final state is reached after `k` steps, for `k` less
than a number of interactions that the balance check is sound for.
-/
def VmTables.FinalReached (vm : VmTables F PublicIO) (balance : Balance F)
    (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ∃ k count, balance.fits count ∧ k < count ∧ vm.Reached k (vm.final publicInput) data

/--
Soundness for a VM ensemble: table constraints and channel balance, with fewer interactions with the
closed channels than the field has elements, imply the verifier guarantees, and `FinalReached`, the
statement that the VM shows about its public input.
-/
def Ensemble.SoundVmChannel (ens : Ensemble F PublicIO) (balance : Balance F)
    (closed : List (RawChannel F)) (FinalReached : PublicIO F → ProverData F → Prop) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.InteractionsFit balance →
    witness.FitField closed →
    witness.Balanced balance →
      ens.VerifierGuarantees witness.data ∧ FinalReached witness.publicInput witness.data

structure SoundVmEnsemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO]
    (balance : Balance F) extends ensemble : Ensemble F PublicIO where
  closed : List (RawChannel F)
  closed_subset : closed ⊆ ensemble.channels
  /-- The statement that the VM shows about the public input and the prover data. -/
  FinalReached : PublicIO F → ProverData F → Prop
  soundVmChannel : ensemble.SoundVmChannel balance closed FinalReached

namespace SoundVmEnsemble
variable {balance : Balance F}

/-- Declare the prover's private input: its type, and the hint tables viewing it. -/
def withProverInput (ens : SoundVmEnsemble F PublicIO balance) (ProverInput : TypeMap)
    [ProvableType ProverInput] (hintTables : List HintTable) :
    SoundVmEnsemble F PublicIO balance where
  ensemble := ens.ensemble.withProverInput ProverInput hintTables
  closed := ens.closed
  closed_subset := ens.closed_subset
  FinalReached := ens.FinalReached
  -- the witnesses of both ensembles have the same tables
  soundVmChannel witness := ens.soundVmChannel { witness with }

@[circuit_norm] lemma withProverInput_ensemble (ens : SoundVmEnsemble F PublicIO balance)
    (ProverInput : TypeMap) [ProvableType ProverInput] (hintTables : List HintTable) :
    (ens.withProverInput ProverInput hintTables).ensemble =
      ens.ensemble.withProverInput ProverInput hintTables := rfl

@[circuit_norm] lemma withProverInput_finalReached (ens : SoundVmEnsemble F PublicIO balance)
    (ProverInput : TypeMap) [ProvableType ProverInput] (hintTables : List HintTable) :
    (ens.withProverInput ProverInput hintTables).FinalReached = ens.FinalReached := rfl

/--
Bundle a sound VM ensemble with its public statement. `Assumptions` refer to the public input and
the table heights, `Spec` only to the public input. The verifier spec and `FinalReached` are
evaluated on prover data derived from the witness, so the bridge from them to `Spec` quantifies over
witnesses.
-/
def toFormal (ens : SoundVmEnsemble F PublicIO balance)
    (Assumptions : PublicIO F → List ℕ → Prop) (Spec : PublicIO F → Prop)
    (assumptionsConsistency : ens.ensemble.AssumptionsConsistency Assumptions)
    (spec_of_finalReached : ∀ witness : EnsembleWitness ens.ensemble,
      Assumptions witness.publicInput witness.heights → ens.VerifierSpec witness.data →
      ens.FinalReached witness.publicInput witness.data → Spec witness.publicInput)
    (ProverAssumptions : PublicIO F → ens.ensemble.ProverInput F → Prop := fun _ _ => True)
    (closedFit : ∀ publicInput heights, Assumptions publicInput heights →
      ens.FitField ens.closed heights := by exact fun _ _ _ _ h_closed => nomatch h_closed) :
    FormalEnsemble F PublicIO balance where
  ensemble := ens.ensemble
  Assumptions
  Spec
  ProverAssumptions
  soundness := by
    intro publicInput heights assumptions
      ⟨fit, witness, input_eq, heights_eq, constraints, balanced⟩
    subst input_eq heights_eq
    obtain ⟨verifierGuarantees, finalReached⟩ := ens.soundVmChannel witness
      (Ensemble.assumptions_of_assumptionsConsistency assumptionsConsistency witness assumptions)
      constraints (EnsembleWitness.interactionsFit_of_heights fit)
      (EnsembleWitness.fitField_of_heights ens.closed_subset (closedFit _ _ assumptions)) balanced
    exact spec_of_finalReached witness assumptions
      (ens.ensemble.verifierSpec_of_verifierGuarantees _ verifierGuarantees) finalReached
end SoundVmEnsemble
end Air.Flat

/-- Instead of first map-flattening on the inside, then on the outside,
we can map to a 3D array, then flatten the outside, and only then the inside.
Good if you want to preserve the inner structure. -/
lemma List.flatMap_flatMap {α β γ : Type*} (l : List γ) (g : γ → List α) (f : γ → α → List β) :
  l.flatMap (fun x => (g x).flatMap (f x)) = (l.map (fun x => (g x).map (f x))).flatten.flatten := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [ih]
    rfl

namespace Air.Flat
namespace VmTables
variable {vm : VmTables F PublicIO}

theorem tables_channel_of_mem (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
  ∃ enabled : Expression F, ∃ pull push : Var vm.Message F,
    ⟨ vm.channel,
      [(vm.channel.pulledIf enabled pull).toRaw,
        (vm.channel.pushedIf enabled push).toRaw] ⟩ ∈ table.exposedChannels ∧
    (∀ env, table.operations.ConstraintsHold env →
      Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1) ∧
    ∀ env, table.Spec env → Expression.eval env enabled = 1 →
      ∀ k, vm.Reached k (eval env pull) env.data → vm.Reached (k + 1) (eval env push) env.data := by
  have h := vm.tables_channel
  simp_rw [List.forall_iff_forall_mem] at h
  simp_rw [table.constraintsHold_iff]
  obtain ⟨ enabled, pull, push, h_exposed, h_enabled, h_step ⟩ := h _ table_mem
  refine ⟨ enabled, pull, push, h_exposed, ?_, ?_ ⟩
  swap
  · simp only [Component.Spec, Component.rowInput, ← eval_varFromOffset_valueFromOffset]
    exact h_step
  intro env h_constraints
  apply h_enabled
  apply FlatOperation.shallowConstraints_of_constraintsHoldFlat
  rw [Circuit.constraintsHold_toFlat_iff]
  exact h_constraints

noncomputable def step (vm : VmTables F PublicIO) {table : Component F}
    (table_mem : table ∈ vm.tables) : VmStep vm.Message F where
  enabled := (vm.tables_channel_of_mem table_mem).choose
  pull := (vm.tables_channel_of_mem table_mem).choose_spec.choose
  push := (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose

/-- Concrete version of VmTables.tables_channel -/
theorem tables_channel' (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
  let step := vm.step table_mem
  ⟨ vm.channel,
    [(vm.channel.pulledIf step.enabled step.pull).toRaw,
      (vm.channel.pushedIf step.enabled step.push).toRaw] ⟩ ∈ table.exposedChannels :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.1

theorem step_enabled_isBool (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
    ∀ env, table.operations.ConstraintsHold env →
      IsBool (Expression.eval env (vm.step table_mem).enabled) :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.2.1

theorem step_reached (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
    ∀ env, table.Spec env → Expression.eval env (vm.step table_mem).enabled = 1 →
      ∀ k, vm.Reached k (eval env (vm.step table_mem).pull) env.data →
        vm.Reached (k + 1) (eval env (vm.step table_mem).push) env.data :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.2.2

noncomputable def verifierPull (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose

noncomputable def verifierPush (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose_spec.choose

/-- Concrete version of VmTables.verifier_channel -/
theorem verifier_channel' (vm : VmTables F PublicIO) :
  vm.verifier.circuitOperations.interactionsWith vm.channel.toRaw =
    [(vm.channel.pulled vm.verifierPull).toRaw,
      (vm.channel.pushed vm.verifierPush).toRaw] :=
  vm.verifier_channel.choose_spec.choose_spec.1

theorem eval_verifierPull (vm : VmTables F PublicIO) (data : ProverData F) :
    eval data.publicEnvironment vm.verifierPull = vm.final (data.getPublicInput PublicIO) :=
  (vm.verifier_channel.choose_spec.choose_spec.2 data).1

theorem reached_verifierPush (vm : VmTables F PublicIO) (data : ProverData F) :
    vm.Reached 0 (eval data.publicEnvironment vm.verifierPush) data :=
  (vm.verifier_channel.choose_spec.choose_spec.2 data).2

lemma interactionsWith_eq {vm : VmTables F PublicIO} {table} (h : table ∈ vm.tables) :
  table.operations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf (vm.step h).enabled (vm.step h).pull).toRaw,
    (vm.channel.pushedIf (vm.step h).enabled (vm.step h).push).toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  apply vm.tables_channel'
end VmTables

/-- What adding the tables, channel and verifier of a VM to an ensemble requires: the components
keep unique names, the VM channel has a new name, and the VM uses only the VM channel and channels
of the ensemble. -/
structure VmTables.FitsInto (vm : VmTables F PublicIO) (ens : Ensemble F PublicIO) : Prop where
  unique_names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup
  fresh_channel : vm.channel.name ∉ ens.channels.map (·.name)
  tables_channels : ∀ table ∈ vm.tables, table.circuit.channels ⊆ vm.channel.toRaw :: ens.channels
  verifier_channels : vm.verifier.channels ⊆ vm.channel.toRaw :: ens.channels

namespace Ensemble

def addVm (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (fits : vm.FitsInto ens) :
    Ensemble F PublicIO :=
  { ens with
    channels := vm.channel :: ens.channels
    unique_channel_names := List.nodup_cons.mpr ⟨fits.fresh_channel, ens.unique_channel_names⟩
    tables := vm.tables ++ ens.tables
    unique_names := fits.unique_names
    tables_channels table h_table := by
      rcases List.mem_append.mp h_table with h_table | h_table
      · exact fits.tables_channels table h_table
      · exact List.Subset.trans (ens.tables_channels table h_table) (List.subset_cons_self _ _)
    verifier := vm.verifier
    verifier_channels := fits.verifier_channels }

@[circuit_norm] lemma addVm_channels (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
    (fits) :
  (ens.addVm vm fits).channels = vm.channel.toRaw :: ens.channels := rfl
@[circuit_norm] lemma addVm_tables (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (fits) :
  (ens.addVm vm fits).tables = vm.tables ++ ens.tables := rfl
@[circuit_norm] lemma addVm_verifier (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
    (fits) :
  (ens.addVm vm fits).verifier = vm.verifier := rfl
end Ensemble

/-- A witness of an ensemble extended by a VM. Its first `vm.tables.length` tables belong to the VM.
-/
abbrev VmWitness (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
    (fits : vm.FitsInto ens) : Type 1 :=
  EnsembleWitness (ens.addVm vm fits)

namespace VmWitness
variable {ens : Ensemble F PublicIO} {vm : VmTables F PublicIO}
  {fits : vm.FitsInto ens}

abbrev vmTables (witness : VmWitness ens vm fits) : List (Table F) :=
  witness.tables.take vm.tables.length

def VmConstraints (witness : VmWitness ens vm fits) : Prop :=
  ∀ table ∈ witness.vmTables, table.Constraints

noncomputable def vmInteractionsWith (witness : VmWitness ens vm fits)
    (channel : RawChannel F) : List (Interaction F) :=
  witness.verifierInteractionsWith channel ++
    witness.vmTables.flatMap (·.interactionsWith channel)

lemma component_mem_tables_of_mem_vmTables
    {witness : VmWitness ens vm fits} {table : Table F} :
    table ∈ witness.vmTables → table.component ∈ vm.tables := by
  intro htable
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htable
  have hi_vm : i < vm.tables.length := by
    have := hi
    simp [List.length_take] at this
    omega
  have hi_full : i < (ens.addVm vm fits).tables.length := by
    simp [Ensemble.addVm]
    omega
  have component_eq := witness.same_circuits i hi_full
  rw [List.getElem_take, ← component_eq]
  simp [Ensemble.addVm, hi_vm]

noncomputable def rowEnabled (witness : VmWitness ens vm fits)
    {table} (h : table ∈ witness.vmTables) (row : Array F) : F :=
  (table.environment row)
    (vm.step (witness.component_mem_tables_of_mem_vmTables h)).enabled

noncomputable def rowPull (witness : VmWitness ens vm fits)
    {table} (h : table ∈ witness.vmTables) (row : Array F) : vm.Message F :=
  eval (table.environment row)
    (vm.step (witness.component_mem_tables_of_mem_vmTables h)).pull

noncomputable def rowPush (witness : VmWitness ens vm fits)
    {table} (h : table ∈ witness.vmTables) (row : Array F) : vm.Message F :=
  eval (table.environment row)
    (vm.step (witness.component_mem_tables_of_mem_vmTables h)).push

noncomputable def verifierPull (witness : VmWitness ens vm fits) : vm.Message F :=
  eval witness.data.publicEnvironment vm.verifierPull

noncomputable def verifierPush (witness : VmWitness ens vm fits) : vm.Message F :=
  eval witness.data.publicEnvironment vm.verifierPush

noncomputable def verifierPair (witness : VmWitness ens vm fits) :
    Interaction F × Interaction F :=
  (vm.channel.pulledValue witness.verifierPull,
    vm.channel.pushedValue witness.verifierPush)

lemma verifierInteractionsWith_eq
    (witness : VmWitness ens vm fits) :
    witness.verifierInteractionsWith vm.channel.toRaw =
      [witness.verifierPair.1, witness.verifierPair.2] := by
  have h : (ens.addVm vm fits).verifierOperations.interactionsWith vm.channel.toRaw = [
      (vm.channel.pulled vm.verifierPull).toRaw,
      (vm.channel.pushed vm.verifierPush).toRaw] := by
    exact vm.verifier_channel'
  rw [EnsembleWitness.verifierInteractionsWith, Operations.interactionValuesWith_eq_map, h]
  simp only [List.map_cons, List.map_nil, verifierPair, verifierPull, verifierPush,
    Channel.eval_pulled, Channel.eval_pushed]

lemma interactionValuesWith_eq (witness : VmWitness ens vm fits)
    {table} (h : table ∈ witness.vmTables) (row : Array F) :
  table.component.operations.interactionValuesWith vm.channel.toRaw
      (table.environment row) = [
    vm.channel.pulledIfValue (witness.rowEnabled h row) (witness.rowPull h row),
    vm.channel.pushedIfValue (witness.rowEnabled h row) (witness.rowPush h row) ] := by
  simp only [circuit_norm, vm.interactionsWith_eq (witness.component_mem_tables_of_mem_vmTables h),
    rowEnabled, rowPull, rowPush, AbstractInteraction.eval, ProvableType.toElements_eval]

/-- The pairs of a pull and a push of the VM channel, one for every row of the VM tables. -/
noncomputable def rowPairs (witness : VmWitness ens vm fits) :
    List (Interaction F × Interaction F) :=
  witness.vmTables.attach.flatMap fun ⟨ table, h ⟩ =>
    table.table.map fun row =>
      (vm.channel.pulledIfValue (witness.rowEnabled h row) (witness.rowPull h row),
        vm.channel.pushedIfValue (witness.rowEnabled h row) (witness.rowPush h row))

lemma mem_rowPairs_iff {witness : VmWitness ens vm fits}
    {pair : Interaction F × Interaction F} :
  pair ∈ witness.rowPairs ↔
    ∃ (table : Table F) (h : table ∈ witness.vmTables), ∃ row ∈ table.table,
      pair = (vm.channel.pulledIfValue (witness.rowEnabled h row) (witness.rowPull h row),
        vm.channel.pushedIfValue (witness.rowEnabled h row) (witness.rowPush h row)) := by
  simp [rowPairs]
  tauto

/-- The number of VM rows. -/
def steps (witness : VmWitness ens vm fits) : ℕ :=
  witness.vmTables.map (·.length) |>.sum

lemma length_rowPairs (witness : VmWitness ens vm fits) :
    witness.rowPairs.length = witness.steps := by
  simp [rowPairs, steps, vmTables, circuit_norm]

lemma rowEnabled_isBool_of_vmConstraints {witness : VmWitness ens vm fits} :
    witness.VmConstraints →
    ∀ table (h : table ∈ witness.vmTables), ∀ row ∈ table.table,
      IsBool (witness.rowEnabled h row) := by
  intro constraints table table_mem row row_mem
  exact vm.step_enabled_isBool (witness.component_mem_tables_of_mem_vmTables table_mem) _
    (constraints table table_mem row row_mem)

lemma interactionss_eq_rowPairs (witness : VmWitness ens vm fits) :
  [witness.verifierInteractionsWith vm.channel.toRaw] ++
      witness.vmTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    (witness.verifierPair :: witness.rowPairs).map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [witness.verifierInteractionsWith_eq]
  simp only [rowPairs, List.flatMap_def, List.map_flatten, List.map_cons,
    List.singleton_append]
  congr 1
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ⟨ table, table_mem ⟩ _
  simp [Table.interactionssWith, witness.interactionValuesWith_eq table_mem]

lemma vmInteractionsWith_eq_flattenPairs (witness : VmWitness ens vm fits) :
    witness.vmInteractionsWith vm.channel.toRaw =
      (witness.verifierPair :: witness.rowPairs).flattenPairs := by
  have unfold_interactions : witness.vmInteractionsWith vm.channel.toRaw =
      ([witness.verifierInteractionsWith vm.channel.toRaw] ++
        witness.vmTables.flatMap
          (·.interactionssWith vm.channel.toRaw)).flatten := by
    simp only [vmInteractionsWith, Table.interactionsWith, Table.interactionssWith,
      List.singleton_append, List.flatten_cons]
    rw [List.flatMap_flatMap, List.flatMap_def]
  rw [unfold_interactions, interactionss_eq_rowPairs, List.flattenPairs]

lemma length_vmInteractionsWith (witness : VmWitness ens vm fits) :
    (witness.vmInteractionsWith vm.channel.toRaw).length = 2 * (witness.steps + 1) := by
  rw [vmInteractionsWith_eq_flattenPairs, List.length_flattenPairs, List.length_cons,
    length_rowPairs]

/--
The VM soundness theorem for `VmTables`: if the interactions with the VM channel are balanced, and
the guarantees of the VM channel imply the spec of every VM row, then the final state is reached
after at most as many steps as there are VM rows.
-/
theorem exists_reached_final (witness : VmWitness ens vm fits)
    (balance : BalancedInteractions (witness.vmInteractionsWith vm.channel.toRaw))
    (constraints : witness.VmConstraints)
    (spec : ∀ table ∈ witness.vmTables, ∀ row ∈ table.table,
      table.component.operations.ChannelGuarantees vm.channel.toRaw (table.environment row) →
      table.component.Spec (table.environment row)) :
    ∃ k ≤ witness.steps, vm.Reached k (vm.final witness.publicInput) witness.data := by
  -- we follow the messages of reached states
  let Reached k (msg : Array F) := ∃ state : vm.Message F,
    (toElements state).toArray = msg ∧ vm.Reached k state witness.data
  have reached_iff {k} {state : vm.Message F} :
      Reached k (toElements state).toArray ↔ vm.Reached k state witness.data := by
    simp only [Reached, Vector.toArray_inj]
    constructor
    · rintro ⟨state', h_state, reached⟩
      rwa [← ProvableType.fromElements_toElements state', h_state,
        ProvableType.fromElements_toElements] at reached
    · exact fun reached => ⟨state, rfl, reached⟩
  rw [vmInteractionsWith_eq_flattenPairs] at balance
  have transitions : ∀ t ∈ witness.rowPairs, Interaction.Transition t := by
    intro t t_mem
    obtain ⟨table, table_mem, row, row_mem, rfl⟩ := mem_rowPairs_iff.mp t_mem
    exact ⟨rfl, rfl, rfl,
      witness.rowEnabled_isBool_of_vmConstraints constraints table table_mem row row_mem⟩
  have step : ∀ t ∈ witness.rowPairs, t.1.mult = 1 →
      ∀ k, Reached k t.1.msg → Reached (k + 1) t.2.msg := by
    intro t t_mem enabled k reached
    obtain ⟨table, table_mem, row, row_mem, rfl⟩ := mem_rowPairs_iff.mp t_mem
    simp only [Channel.pulledIfValue, Channel.pushedIfValue, reached_iff] at enabled reached ⊢
    rw [show witness.data = (table.environment row).data from
      (witness.same_data table (List.mem_of_mem_take table_mem)).symm] at reached ⊢
    apply vm.step_reached _ _ ?_ enabled k reached
    apply spec table table_mem row row_mem
    -- the pull of the row gets its guarantee from the reached state
    rw [Operations.ChannelGuarantees, ← Operations.forall_interactionsWith_iff]
    intro i i_mem
    rw [← AbstractInteraction.eval_guarantees]
    have := witness.interactionValuesWith_eq table_mem row
    rw [Operations.interactionValuesWith_eq_map] at this
    have i_mem' := List.mem_map_of_mem (f := AbstractInteraction.eval (table.environment row)) i_mem
    rw [this] at i_mem'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at i_mem'
    rcases i_mem' with h_i | h_i <;> rw [h_i]
    · intro _ _
      simp only [Channel.pulledIfValue, Channel.toRaw, Interaction.msgVector, Vector.mk_toArray,
        ProvableType.fromElements_toElements]
      exact vm.guarantees_of_reached _ _ _ reached
    · exact Channel.pushedIfValue_guarantees
  obtain ⟨k, hk, reached⟩ := exists_reached_of_balancedInteractions Reached
    witness.verifierPair.1 witness.verifierPair.2 witness.rowPairs balance
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ transitions step 0
    (reached_iff.mpr (vm.reached_verifierPush witness.data))
  simp only [verifierPair, Channel.pulledValue, reached_iff, verifierPull, vm.eval_verifierPull,
    witness.data_getPublicInput] at reached
  rw [zero_add, length_rowPairs] at hk
  exact ⟨k, hk, reached⟩

/-! ### Splitting into the VM tables and the original tables -/

lemma tables_length (witness : VmWitness ens vm fits) :
    witness.tables.length = vm.tables.length + ens.tables.length := by
  rw [← witness.same_length]
  simp [Ensemble.addVm]

/-- The tables of the original ensemble, which come after the VM tables. -/
abbrev oldTables (witness : VmWitness ens vm fits) : List (Table F) :=
  witness.tables.drop vm.tables.length

lemma vmTables_append_oldTables (witness : VmWitness ens vm fits) :
    witness.vmTables ++ witness.oldTables = witness.tables :=
  List.take_append_drop _ _

lemma mem_oldTables_of_not_mem_vmTables {witness : VmWitness ens vm fits} {table : Table F} :
    table ∈ witness.tables → table ∉ witness.vmTables → table ∈ witness.oldTables := by
  intro h_table h_vm
  rw [← witness.vmTables_append_oldTables, List.mem_append] at h_table
  exact h_table.resolve_left h_vm

lemma oldTables_map_component (witness : VmWitness ens vm fits) :
    witness.oldTables.map (·.component) = ens.tables := by
  apply List.ext_getElem
  · simp [List.length_drop, witness.tables_length]
  · intro i hi hi'
    have hi_full : vm.tables.length + i < (ens.addVm vm fits).tables.length := by
      simp [Ensemble.addVm]
      omega
    rw [List.getElem_map, List.getElem_drop, ← witness.same_circuits _ hi_full]
    simp [Ensemble.addVm]

lemma component_mem_tables_of_mem_oldTables {witness : VmWitness ens vm fits} {table : Table F} :
    table ∈ witness.oldTables → table.component ∈ ens.tables := by
  intro h_table
  rw [← witness.oldTables_map_component]
  exact List.mem_map_of_mem h_table

/-- The VM tables, as tables sharing the witness's prover data. -/
def vmContext (witness : VmWitness ens vm fits) : Tables F where
  tables := witness.vmTables
  data := witness.data
  same_data table h_table := witness.same_data table (List.mem_of_mem_take h_table)

/-- The original ensemble's tables, as tables sharing the witness's prover data. -/
def oldContext (witness : VmWitness ens vm fits) : Tables F where
  tables := witness.oldTables
  data := witness.data
  same_data table h_table := witness.same_data table (List.mem_of_mem_drop h_table)

lemma vmContext_append_oldContext (witness : VmWitness ens vm fits) :
    witness.vmContext.append witness.oldContext rfl = witness.toTables := by
  simp [vmContext, oldContext, EnsembleWitness.toTables, Tables.append]

lemma toTables_perm (witness : VmWitness ens vm fits) :
    witness.toTables.tables.Perm (witness.oldContext.tables ++ witness.vmContext.tables) :=
  (List.Perm.of_eq witness.vmTables_append_oldTables.symm).trans List.perm_append_comm

lemma vmConstraints_of_constraints {witness : VmWitness ens vm fits} :
    witness.Constraints → witness.VmConstraints :=
  fun constraints table h_table => constraints table (List.mem_of_mem_take h_table)

lemma oldContext_constraints_of_constraints {witness : VmWitness ens vm fits} :
    witness.Constraints → witness.oldContext.Constraints :=
  fun constraints table h_table => constraints table (List.mem_of_mem_drop h_table)

lemma vmContext_assumptions_of_assumptions {witness : VmWitness ens vm fits} :
    witness.Assumptions → witness.vmContext.Assumptions :=
  fun assumptions table h_table => assumptions table (List.mem_of_mem_take h_table)

lemma oldContext_assumptions_of_assumptions {witness : VmWitness ens vm fits} :
    witness.Assumptions → witness.oldContext.Assumptions :=
  fun assumptions table h_table => assumptions table (List.mem_of_mem_drop h_table)

/-- If the original tables don't use the VM channel, all of its interactions come from the VM. -/
lemma interactionsWith_eq_vmInteractionsWith (witness : VmWitness ens vm fits)
    (not_mem_vm_channel : ∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) :
    witness.interactionsWith vm.channel.toRaw = witness.vmInteractionsWith vm.channel.toRaw := by
  simp only [EnsembleWitness.interactionsWith, vmInteractionsWith, EnsembleWitness.toTables,
    Tables.interactionsWith]
  rw [← witness.vmTables_append_oldTables, List.flatMap_append]
  suffices witness.oldTables.flatMap (·.interactionsWith vm.channel.toRaw) = [] by
    rw [this, List.append_nil]
  simp only [List.flatMap_eq_nil_iff]
  intro table mem_table
  apply Table.interactionsWith_nil_of_channel_not_mem
  exact not_mem_vm_channel _ (component_mem_tables_of_mem_oldTables mem_table)
end VmWitness

namespace Ensemble

theorem addVm_soundVmChannel_of_soundChannels (ens : Ensemble F PublicIO) {balance : Balance F}
      -- given a sound channels ensemble with lists of ordered and closed channels
    {ordered closed : List (RawChannel F)} (soundChannels : ens.SoundChannels ordered closed)
    (ordered_subset : ordered ⊆ ens.channels)
    -- and given a VM channel + tables + verifier
    (vm : VmTables F PublicIO)
    (fits : vm.FitsInto ens)
    -- and the guarantees of the closed channels in the ensemble with the VM
    (closed_guarantees : ∀ witness : EnsembleWitness (ens.addVm vm fits), witness.Assumptions →
      witness.Constraints → witness.InteractionsFit balance → witness.FitField closed →
      witness.Balanced balance →
      ∀ channel ∈ closed, ∀ i ∈ witness.interactionsWith channel, i.Guarantees witness.data) :
    -- assuming that none of the existing tables interacted with the VM channel
    (∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) →
    -- assuming that the VM tables' and verifier's channelsWithGuarantees are either finished or the VM channel
    (vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: (ordered ++ closed) ∧
      ∀ table ∈ vm.tables,
        table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: (ordered ++ closed)) →
    -- and assuming the VM tables' channelsWithRequirements contain none of the finished ones
    (∀ channel ∈ ordered ++ closed, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the VM tables satisfies SoundVmChannel
    (ens.addVm vm fits).SoundVmChannel balance closed (vm.FinalReached balance) := by
  intro not_mem_vm_channel grts_subset reqs_disjoint (witness : VmWitness ens vm fits) assumptions
    constraints fit closed_fit balanced
  have balance := witness.balancedChannels_of_balanced fit balanced
  have consistent := soundChannels.right.right
  -- the guarantees of the closed channels hold in every table
  have closed_grts : ∀ channel ∈ closed, ∀ table ∈ witness.tables,
      table.ChannelGuarantees channel := by
    intro channel h_channel table h_table
    rw [Table.channelGuarantees_iff_forall, witness.same_data table h_table]
    intro i h_i
    apply closed_guarantees witness assumptions constraints fit closed_fit balanced channel h_channel i
    rw [witness.mem_interactionsWith]
    exact .inr ⟨table, h_table, h_i⟩
  /-
  the high level plan is to apply `exists_reached_final`.

  1) we need to narrow vm channel balance to just the vm tables
  2) guarantees for finished channels follows from soundChannels + constraints, using
     `spec_and_guarantees_of_soundChannels` and `guarantees_of_requirements_append`
     as the key lemmas.
  3) the combination of guarantees for finished channels + vm constraints gives us the main condition:
     "vm guarantees → vm spec", by invoking `spec_of_partial_guarantees_of_constraints`.
  4) finally, the final state is reached, which gives the verifier its guarantees, and the number of
     interactions with the vm channel bounds the number of steps.
  -/
  -- the vm channel interactions are constrained to vm tables, which lets us supply the balance
  -- condition
  have vm_balance := balance vm.channel.toRaw (by simp [Ensemble.addVm])
  simp only [circuit_norm] at vm_balance
  rw [witness.interactionsWith_eq_vmInteractionsWith not_mem_vm_channel] at vm_balance
  set vmChannel := vm.channel.toRaw
  -- next, we work on instantiating `spec_of_partial_guarantees_of_constraints`
  -- which will give us exactly the last hypothesis of `exists_reached_final`
  -- first, unify channel subset assumptions to all tables
  have grts_subset_all : ∀ table ∈ witness.vmTables,
      table.channelsWithGuarantees ⊆ vmChannel :: (ordered ++ closed) := by
    intro table h_table
    exact grts_subset.2 table.component (witness.component_mem_tables_of_mem_vmTables h_table)
  have vm_reqs_disjoint : ∀ channel ∈ ordered ++ closed, ∀ table ∈ witness.vmTables,
      channel ∉ table.channelsWithRequirements := by
    intro channel channel_mem table table_mem
    exact (reqs_disjoint channel channel_mem).2 _
      (witness.component_mem_tables_of_mem_vmTables table_mem)
  have vm_constraints := witness.vmConstraints_of_constraints constraints
  -- establish partial balance + specialize to old ensemble
  have ordered_finished : ∀ channel ∈ ordered,
      (ens.addVm vm fits).OrderedChannel channel := by
    intro channel channel_mem
    have ordered := (soundChannels.right.left channel channel_mem).right.left
    have no_requirements := reqs_disjoint channel (List.mem_append_left _ channel_mem)
    clear * - ordered no_requirements
    simp_all [circuit_norm, orderedChannel_of_no_requirements, orderedChannelLt_of_no_requirements]
  have partial_balance : ∀ channel ∈ ordered,
      PartialBalancedChannel witness.toTables channel := by
    intro channel channel_mem
    apply Ensemble.partialBalancedChannel_of_balancedChannel
    · exact ordered_finished channel channel_mem
    · exact balance channel (by simp [Ensemble.addVm, ordered_subset channel_mem])
  have old_partial_balance : ∀ channel ∈ ordered,
      PartialBalancedChannel witness.oldContext channel := by
    intro channel channel_mem
    apply partialBalancedChannel_of_sublist (partial_balance _ channel_mem)
    exact ⟨witness.vmContext.tables, witness.toTables_perm, vm_constraints,
      vm_reqs_disjoint _ (List.mem_append_left _ channel_mem)⟩
  -- invoke old tables soundness to get reqs for ordered channels from constraints
  have finished_reqs : ∀ channel ∈ ordered, ∀ table ∈ witness.oldContext.tables,
      table.ChannelRequirements channel := by
    intro channel channel_mem table table_mem
    refine spec_and_guarantees_of_soundChannels (witness := witness.oldContext) (closed := closed)
      ?_ (witness.oldContext_assumptions_of_assumptions assumptions)
      (witness.oldContext_constraints_of_constraints constraints) old_partial_balance
      (fun channel h_channel table h_table =>
        closed_grts channel h_channel table (List.mem_of_mem_drop h_table))
      table table_mem
      |>.right channel channel_mem |>.right
    have old_sound_channels : _root_.SoundChannels ens.tables ordered closed := ⟨
      ens.channelsWithGuarantees_subset_iff.mp soundChannels.left |>.right,
      fun channel h_channel => (soundChannels.right.left channel h_channel).right.left,
      soundChannels.right.right⟩
    simpa only [VmWitness.oldContext, witness.oldTables_map_component] using old_sound_channels
  -- invoke `guarantees_of_requirements_append` to get grts for ordered channels in vm tables
  have finished_grts : ∀ table ∈ witness.vmTables, ∀ channel ∈ ordered ++ closed,
      table.ChannelGuarantees channel := by
    intro table table_mem channel channel_mem
    rcases List.mem_append.mp channel_mem with channel_mem | channel_mem
    · have : channel.Consistent := consistent channel channel_mem
      apply guarantees_of_requirements_append (ts := witness.vmContext) (ss := witness.oldContext)
        rfl vm_constraints (vm_reqs_disjoint _ (List.mem_append_left _ channel_mem))
        (witness.vmContext_append_oldContext ▸ partial_balance _ channel_mem)
        (finished_reqs _ channel_mem)
        _ table_mem
    · exact closed_grts channel channel_mem table (List.mem_of_mem_take table_mem)
  -- invoke `spec_of_partial_guarantees_of_constraints` to get the spec of every vm row from the
  -- guarantees of the vm channel, and use it in `exists_reached_final`
  have spec (table) (h_table : table ∈ witness.vmTables) :=
    table.spec_of_partial_guarantees_of_constraints (unfinished := vmChannel)
    (witness.vmContext_assumptions_of_assumptions assumptions table h_table)
    (vm_constraints table h_table)
    (grts_subset_all table h_table) (finished_grts table h_table)
  obtain ⟨k, hk, reached⟩ := witness.exists_reached_final vm_balance vm_constraints spec
  -- the final state gets the guarantees of the vm channel, since it is reached
  have vm_verifier_guarantees :
      (ens.addVm vm fits).VerifierChannelGuarantees witness.data vmChannel := by
    rw [witness.verifierChannelGuarantees_iff_forall, witness.verifierInteractionsWith_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl)
    · intro _ _
      simp only [VmWitness.verifierPair, Channel.pulledValue, Channel.toRaw,
        Interaction.msgVector, Vector.mk_toArray, ProvableType.fromElements_toElements,
        VmWitness.verifierPull, vm.eval_verifierPull, witness.data_getPublicInput]
      exact vm.guarantees_of_reached _ _ _ reached
    · simp [VmWitness.verifierPair, Interaction.Guarantees, Channel.pushedValue]
  have finished_verifier_guarantees : ∀ channel ∈ ordered ++ closed,
      (ens.addVm vm fits).VerifierChannelGuarantees witness.data channel := by
    intro channel channel_mem
    rcases List.mem_append.mp channel_mem with h_ordered | h_closed
    swap
    · rw [witness.verifierChannelGuarantees_iff_forall]
      intro i h_i
      apply closed_guarantees witness assumptions constraints fit closed_fit balanced channel h_closed i
      rw [witness.mem_interactionsWith]
      exact .inl h_i
    let : channel.Consistent := consistent channel h_ordered
    apply Ensemble.verifierChannelGuarantees_of_tableRequirements
    · exact .inr (reqs_disjoint channel channel_mem).1
    · exact balance channel (by simp [Ensemble.addVm, ordered_subset h_ordered])
    intro table h_table
    by_cases h_vm : table ∈ witness.vmTables
    · exact table.requirements_of_not_mem_of_constraints (vm_constraints table h_vm)
        (vm_reqs_disjoint channel channel_mem table h_vm)
    · exact finished_reqs channel h_ordered table
        (witness.mem_oldTables_of_not_mem_vmTables h_table h_vm)
  refine ⟨?_, k, (witness.interactionsWith vmChannel).length,
    fit vmChannel (by simp [Ensemble.addVm, vmChannel]), ?_, reached⟩
  · rw [Ensemble.verifierGuarantees_iff]
    intro channel h_channel
    rcases List.mem_cons.mp (grts_subset.1 h_channel) with rfl | h_finished
    · exact vm_verifier_guarantees
    · exact finished_verifier_guarantees channel h_finished
  -- there are more interactions with the vm channel than vm rows
  rw [witness.interactionsWith_eq_vmInteractionsWith not_mem_vm_channel,
    witness.length_vmInteractionsWith]
  omega
end Ensemble

namespace SoundEnsemble
variable {balance : Balance F}

/-- A VM's tables and verifier fit into a sound ensemble whose channels they use: their guarantees
come from finished channels or the VM channel, and their requirements go to the VM channel or to
channels of the ensemble that aren't finished. -/
theorem vmFitsInto (ens : SoundEnsemble F PublicIO balance) (vm : VmTables F PublicIO)
    (fresh_channel : vm.channel.name ∉ ens.channels.map (·.name))
    (grts_subset_finished : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished)
    (reqs_unfinished : (∀ channel ∈ vm.verifier.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished) ∧
      ∀ table ∈ vm.tables, ∀ channel ∈ table.circuit.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished)
    (names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup) :
    vm.FitsInto ens.ensemble where
  unique_names := names
  fresh_channel
  tables_channels table h_table channel h_channel := by
    rcases List.mem_append.mp h_channel with h_channel | h_channel
    · rcases List.mem_cons.mp (grts_subset_finished.2 table h_table h_channel) with rfl | h_finished
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ens.finished_subset h_finished)
    · exact (reqs_unfinished.2 table h_table channel h_channel).1
  verifier_channels channel h_channel := by
    rcases List.mem_append.mp h_channel with h_channel | h_channel
    · rcases List.mem_cons.mp (grts_subset_finished.1 h_channel) with rfl | h_finished
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ens.finished_subset h_finished)
    · exact (reqs_unfinished.1 channel h_channel).1

/-- The closed channels of a sound ensemble keep their guarantees when a VM is added, since the VM
doesn't push to them. -/
theorem addVm_closedGuarantees (ens : SoundEnsemble F PublicIO balance) (vm : VmTables F PublicIO)
    (fits : vm.FitsInto ens.ensemble)
    (reqs_unfinished : (∀ channel ∈ vm.verifier.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished) ∧
      ∀ table ∈ vm.tables, ∀ channel ∈ table.circuit.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished)
    (witness : EnsembleWitness (ens.ensemble.addVm vm fits)) :
    witness.Assumptions → witness.Constraints → witness.InteractionsFit balance →
      witness.FitField (ens.closed.map (·.channel)) → witness.Balanced balance →
      ∀ channel ∈ ens.closed.map (·.channel), ∀ i ∈ witness.interactionsWith channel,
        i.Guarantees witness.data := by
  intro assumptions constraints fit closed_fit balanced channel h_channel
  obtain ⟨closedChannel, h_closed, rfl⟩ := List.mem_map.mp h_channel
  have h_finished : closedChannel.channel ∈ ens.finished := List.mem_append_right _ h_channel
  have h_mem := List.mem_cons_of_mem vm.channel.toRaw (ens.closed_subset h_channel)
  apply closedChannel.guarantees_of_balanced witness assumptions constraints (fit _ h_mem)
    (closed_fit _ h_channel) (balanced _ h_mem)
  · intro table h_table h_owner
    apply table.requirements_of_not_mem_of_constraints (constraints table h_table)
    intro h_req
    rcases List.mem_append.mp (witness.component_mem_tables_of_mem h_table) with h_vm | h_old
    · exact (reqs_unfinished.2 _ h_vm _ h_req).2 h_finished
    · exact ens.closed_requirements closedChannel h_closed _ h_old h_owner h_req
  · apply Ensemble.verifierChannelRequirements_of_not_mem
    exact fun h_req => (reqs_unfinished.1 _ h_req).2 h_finished

/-- Add a VM on top of a sound ensemble, see `vmFitsInto` for the conditions on its channels. -/
def addVm (ens : SoundEnsemble F PublicIO balance) (vm : VmTables F PublicIO)
    (fresh_channel : vm.channel.name ∉ ens.channels.map (·.name) := by simp [circuit_norm])
    (grts_subset_finished : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished
      := by simp [circuit_norm])
    (reqs_unfinished : (∀ channel ∈ vm.verifier.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished) ∧
      ∀ table ∈ vm.tables, ∀ channel ∈ table.circuit.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished
      := by simp [circuit_norm])
    (names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup := by simp [circuit_norm]) :
    SoundVmEnsemble F PublicIO balance where
  __ := ens.ensemble.addVm vm
    (ens.vmFitsInto vm fresh_channel grts_subset_finished reqs_unfinished names)
  closed := ens.closed.map (·.channel)
  closed_subset := List.Subset.trans ens.closed_subset (List.subset_cons_self _ _)
  FinalReached := vm.FinalReached balance
  soundVmChannel := ens.ensemble.addVm_soundVmChannel_of_soundChannels
    ens.soundChannels ens.ordered_subset vm
    (ens.vmFitsInto vm fresh_channel grts_subset_finished reqs_unfinished names)
    (ens.addVm_closedGuarantees vm _ reqs_unfinished)
    (fun table h_table h_mem =>
      fresh_channel (List.mem_map.mpr ⟨_, ens.tables_channels table h_table h_mem, rfl⟩))
    grts_subset_finished
    (fun channel h_finished =>
      ⟨fun h => (reqs_unfinished.1 channel h).2 h_finished,
        fun table h_table h => (reqs_unfinished.2 table h_table channel h).2 h_finished⟩)

variable {soundEns : SoundEnsemble F PublicIO balance} {vm : VmTables F PublicIO}
  {fresh : vm.channel.name ∉ soundEns.channels.map (·.name)}
  {gsf : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished ∧
    ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished}
  {reqs : (∀ channel ∈ vm.verifier.channelsWithRequirements,
      channel ∈ vm.channel.toRaw :: soundEns.channels ∧ channel ∉ soundEns.finished) ∧
    ∀ table ∈ vm.tables, ∀ channel ∈ table.circuit.channelsWithRequirements,
      channel ∈ vm.channel.toRaw :: soundEns.channels ∧ channel ∉ soundEns.finished}
  {names : ((vm.tables ++ soundEns.tables).map (·.circuit.name)).Nodup}

@[circuit_norm] lemma addVm_tables :
  (soundEns.addVm vm fresh gsf reqs names).tables = vm.tables ++ soundEns.tables := rfl
@[circuit_norm] lemma addVm_channels :
  (soundEns.addVm vm fresh gsf reqs names).channels = vm.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addVm_verifier :
  (soundEns.addVm vm fresh gsf reqs names).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_closed :
  (soundEns.addVm vm fresh gsf reqs names).closed = soundEns.closed.map (·.channel) := rfl
@[circuit_norm] lemma addVm_finalReached :
  (soundEns.addVm vm fresh gsf reqs names).FinalReached = vm.FinalReached balance := rfl
@[circuit_norm] lemma addVm_ensemble :
  (soundEns.addVm vm fresh gsf reqs names).ensemble = soundEns.ensemble.addVm vm
    (soundEns.vmFitsInto vm fresh gsf reqs names) := rfl

end SoundEnsemble
end Air.Flat
