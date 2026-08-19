import Clean.Air.FlatEnsemble
import Clean.Air.OrderedChannel

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-
## VM ensembles

VM-like ensembles have a "main channel" that stores the VM state, which we'll call a _VM channel_.
One or more tables pull from, then push to, this channel in their row circuit; thereby performing one VM transition.

The public input/output of such an ensemble is the initial push (initial state) and the final pull (final state).
The statement to prove is that there exists a sequence of valid VM transitions from the initial state to the final state.
Note that this does not, in general, require that every row in the trace participates in a single transition path!
In addition to the main (valid) transition path, there can be additional closed cycles of VM steps.

What is more, the unused cycles can be "invalid" in the sense that we generally cannot prove that their guarantees are satisfied,
because we get a circular implication sequence of the form ... → guarantees → requirements → guarantees → ...

Consequently, from the assumptions (constraints + balance), we _cannot_ prove global soundness for a VM channel in the sense that
all guarantees for that channel must hold (like we did above for the `SoundChannels` case).

This is why we need a weaker statement about VM channels which still allows us to prove soundness of the overall ensemble.
Essentially, it amounts to the simple idea that for any cycle, if just _one_ of the guarantees or requirements hold,
then all of them do.
This holds in a very general sense and is applied to the "cycle" which contains the input + output interactions as
start and end points.
Thus, assuming the _input satisfies the requirements_ (a very sensible assumption), we can conclude that
the _output satisfies the guarantees_. The latter can usually be engineered to be exactly the statement we actually care about.

The main proof idea is captured by `guarantees_of_requirements_of_requirements_of_guarantees` in `Balance.lean`,
a theorem which states the VM interaction situation in a rather abstract setting.

Here, we introduce the `VmTables` structure (capturing basic assumptions we put on a VM definition) as well as the
`SoundVmChannel` class (capturing what we mean with soundness for a VM), and then go on to prove our main theorem,
`addVm_soundVmChannel_of_soundChannels`, which shows soundness for a VM added on top of a `SoundChannels` ensemble.
-/

namespace Air.Flat

structure VmStep (Message : TypeMap) [ProvableType Message] (F : Type) where
  enabled : Expression F
  pull : Var Message F
  push : Var Message F

structure VmTables (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : Channel F Message

  tables : List (Component F)
  unique_names : (tables.map (·.circuit.name)).Nodup
  verifier : Verifier.Program F PublicIO

  /-- VM components are checked row by row.

  This is not a new restriction: every VM obligation below -- `tables_channel`, the interaction
  count, the row-shaped soundness argument -- is already stated in terms of a single row's
  `rowOperations` at `rowOffset`. Making it a field records that explicitly, and is what
  `vmTables_windowRows_eq_one` transports to the committed traces via `same_circuits`. -/
  tables_windowRows : tables.Forall (fun table => table.windowRows = 1) := by
    simp only [List.Forall, and_true, true_and] <;> rfl

  tables_channel : tables.Forall fun table =>
    ∃ enabled : Expression F, ∃ pull push : Var Message F,
      ⟨ channel, [(channel.pulledIf enabled pull).toRaw, (channel.pushedIf enabled push).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      ∀ env, ConstraintsHold.Shallow env table.rowOperations →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1

  -- The public verifier pulls the final state and pushes the initial state on the VM channel.
  verifier_channel : ∃ m1 m2, verifier.interactions =
    [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw]

  -- verifier requirements hold unconditionally (without relying on channel guarantees)
  verifier_requirements :
    ∀ env,
      Operations.ChannelRequirements channel env verifier.circuitOperations

instance (vm : VmTables F PublicIO) : ProvableType vm.Message := vm.provableMessage

def VmTables.toEnsemble (vm : VmTables F PublicIO) : Ensemble F PublicIO where
  channels := [vm.channel.toRaw]
  tables := vm.tables
  unique_names := vm.unique_names
  verifier := vm.verifier

/--
Soundness for a VM ensemble is simple:
- the ensemble spec is the verifier spec
- the verifier spec follows from verifier guarantees
- verifier guarantees follow from table constraints and channel balance
-/
def Ensemble.SoundVmChannel (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.BalancedChannels →
      ens.VerifierGuarantees witness.publicInput witness.data

structure SoundVmEnsemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO]
    extends ensemble : Ensemble F PublicIO where
  soundVmChannel : ensemble.SoundVmChannel

namespace SoundVmEnsemble
def toFormal (F : Type) [FiniteField F] (ens : SoundVmEnsemble F PublicIO)
  -- TODO is this useful in practice? Right now, tables don't have access to public input so that's weird
  (ExtraAssumptions : PublicIO F → ProverData F → Prop)
  (extraAssumptionsConsistency : ∀ publicInput data, ExtraAssumptions publicInput data →
    ∀ table ∈ ens.ensemble.tables, ∀ input, table.Assumptions input data) :
    FormalEnsemble F PublicIO where
  ensemble := ens.ensemble
  Assumptions publicInput := ∀ data, ExtraAssumptions publicInput data
  Spec publicInput := ∃ data, ens.VerifierSpec publicInput data
  soundness := by
    simp only [Ensemble.Soundness, Ensemble.Statement]
    intro input assumptions ⟨witness, input_eq, constraints, _boundaries, balance⟩
    use witness.data
    have extra_assumptions := assumptions witness.data
    simp only [← input_eq, circuit_norm] at *
    have soundVm := ens.soundVmChannel witness ?assumptions constraints balance
    exact ens.ensemble.verifierSoundness witness.publicInput witness.data soundVm
    intro table h_table env h_env
    simp only [Component.RowAssumptions]
    have hcomponent := EnsembleWitness.mem_component_of_mem h_table
    rw [RowEnvs.data_eq_of_mem h_env]
    have hresidual := extraAssumptionsConsistency witness.publicInput witness.data
      extra_assumptions table.component hcomponent (table.component.rowInput env)
    exact hresidual

variable {ens : SoundVmEnsemble F PublicIO} {ExtraAssumptions : PublicIO F → ProverData F → Prop}
  {eac : ∀ publicInput data, ExtraAssumptions publicInput data →
    ∀ table ∈ ens.tables, ∀ input, table.Assumptions input data}

@[circuit_norm] lemma toFormal_spec publicInput :
  (ens.toFormal F ExtraAssumptions eac).Spec publicInput ↔
    ∃ data, ens.ensemble.VerifierSpec publicInput data := by
  simp only [toFormal]

@[circuit_norm] lemma toFormal_assumptions publicInput :
  (ens.toFormal F ExtraAssumptions eac).Assumptions publicInput ↔
    ∀ data, ExtraAssumptions publicInput data := by
  simp only [toFormal, circuit_norm]
end SoundVmEnsemble
end Air.Flat

def List.flattenPairs {α : Type} (pairs : List (α × α)) : List α :=
  pairs.map (fun (a, b) => [a, b]) |>.flatten

lemma List.flattenPairs_cons {α : Type} (a b : α) (pairs : List (α × α)) :
    List.flattenPairs ((a, b) :: pairs) = [a, b] ++ List.flattenPairs pairs := by
  simp [List.flattenPairs]

lemma List.zip_flattenPairs_perm {α : Type} {as bs : List α} :
    bs.length = as.length → List.Perm (List.zip as bs).flattenPairs (as ++ bs) := by
  open List in
  suffices ∀ n, as.length = n → bs.length = n →
    Perm (zip as bs).flattenPairs (as ++ bs) from this as.length rfl
  intro n as_len bs_len
  induction n generalizing as bs with
  | zero => simp_all [flattenPairs]
  | succ n ih =>
    rcases as with rfl | ⟨ a, as ⟩; nomatch as_len
    rcases bs with rfl | ⟨ b, bs ⟩; nomatch bs_len
    simp only [length_cons, Nat.add_right_cancel_iff] at as_len bs_len
    specialize ih as_len bs_len
    simp only [zip_cons_cons, flattenPairs_cons, cons_append, nil_append]
    grw [perm_cons, ← perm_cons_append_cons _ perm_rfl, perm_cons, ih]

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

lemma List.zip_flatten_flatten {α : Type} (as bs : List (List (α)))
  (same_lengths : as.length = bs.length ∧ (∀ i (hi : i < as.length) (hi' : i < bs.length), as[i].length = bs[i].length)) :
    List.zip as.flatten bs.flatten = ((as.zip bs).map (fun (t, s) => t.zip s)).flatten := by
  revert same_lengths
  suffices ∀ n, (_ : as.length = n) → (_ : bs.length = n) →
    (∀ i (hi : i < n), as[i].length = bs[i].length) →
      List.zip as.flatten bs.flatten = ((as.zip bs).map (fun t => t.1.zip t.2)).flatten by
    rintro ⟨ same_length, same_lengths ⟩
    apply this as.length rfl same_length.symm
    intro i hi
    exact same_lengths i hi (by linarith)
  intro n alen blen same_lengths
  induction n generalizing as bs with
  | zero =>
    simp at alen blen
    simp [alen, blen]
  | succ n ih =>
    rcases as with rfl | ⟨ a, as ⟩; simp
    rcases bs with rfl | ⟨ b, bs ⟩; simp
    simp at alen blen
    have same_length_zero : a.length = b.length := same_lengths 0 (by linarith)
    have same_length_succ i (hi : i < n) : as[i].length = bs[i].length := same_lengths (i + 1) (by linarith)
    simp only [List.flatten_cons, List.zip_cons_cons, List.map_cons]
    rw [List.zip_append same_length_zero]
    specialize ih as bs alen blen same_length_succ
    rw [ih]

lemma List.zip_map_fst_snd {α β : Type} (pairs : List (α × β)) :
    List.zip (pairs.map Prod.fst) (pairs.map Prod.snd) = pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
    simp [ih]

namespace Air.Flat
namespace VmTables
variable {vm : VmTables F PublicIO}

@[circuit_norm] lemma toEnsemble_tables (vm : VmTables F PublicIO) :
  vm.toEnsemble.tables = vm.tables := rfl
@[circuit_norm] lemma toEnsemble_verifier (vm : VmTables F PublicIO) :
  vm.toEnsemble.verifier = vm.verifier := rfl

theorem tables_channel_of_mem (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
  ∃ enabled : Expression F, ∃ pull push : Var vm.Message F,
    ⟨ vm.channel,
      [(vm.channel.pulledIf enabled pull).toRaw,
        (vm.channel.pushedIf enabled push).toRaw] ⟩ ∈ table.exposedChannels ∧
    ∀ env, table.operations.ConstraintsHold env →
      Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1 := by
  have h := vm.tables_channel
  simp_rw [List.forall_iff_forall_mem] at h
  simp_rw [table.constraintsHold_iff]
  obtain ⟨ enabled, pull, push, h_exposed, h_enabled ⟩ := h _ table_mem
  use enabled, pull, push, h_exposed
  intro env h_constraints
  apply h_enabled
  apply FlatOperation.shallowConstraints_of_constraintsHoldFlat
  rw [Circuit.constraintsHold_toFlat_iff]
  exact h_constraints

noncomputable def tableStep (vm : VmTables F PublicIO) {table : Component F}
    (table_mem : table ∈ vm.tables) : VmStep vm.Message F where
  enabled := (vm.tables_channel_of_mem table_mem).choose
  pull := (vm.tables_channel_of_mem table_mem).choose_spec.choose
  push := (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose

/-- Concrete version of VmTables.tables_channel -/
theorem tables_channel' (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
  let step := vm.tableStep table_mem
  ⟨ vm.channel,
    [(vm.channel.pulledIf step.enabled step.pull).toRaw,
      (vm.channel.pushedIf step.enabled step.push).toRaw] ⟩ ∈ table.exposedChannels :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.left

theorem tableStep_enabled_isBool (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
    ∀ env, table.operations.ConstraintsHold env →
      IsBool (Expression.eval env (vm.tableStep table_mem).enabled) :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.right

noncomputable def verifierPull (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose

noncomputable def verifierPush (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose_spec.choose

/-- Concrete version of VmTables.verifier_channel -/
theorem verifier_channel' (vm : VmTables F PublicIO) :
  vm.verifier.interactions =
    [(vm.channel.pulled vm.verifierPull).toRaw,
      (vm.channel.pushed vm.verifierPush).toRaw] :=
  vm.verifier_channel.choose_spec.choose_spec

noncomputable def verifierStep (vm : VmTables F PublicIO) : VmStep vm.Message F where
  enabled := 1
  pull := vm.verifierPull
  push := vm.verifierPush

lemma interactionsWith_eq {vm : VmTables F PublicIO} {table} (_ : table ∈ vm.tables) :
  table.operations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf (vm.tableStep ‹_›).enabled (vm.tableStep ‹_›).pull).toRaw,
    (vm.channel.pushedIf (vm.tableStep ‹_›).enabled (vm.tableStep ‹_›).push).toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  apply vm.tables_channel'

lemma verifierInteractionsWith_eq {vm : VmTables F PublicIO} :
  vm.toEnsemble.verifierOperations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf vm.verifierStep.enabled vm.verifierStep.pull).toRaw,
    (vm.channel.pushedIf vm.verifierStep.enabled vm.verifierStep.push).toRaw ] := by
  classical
  change vm.verifier.circuitOperations.interactionsWith vm.channel.toRaw = _
  rw [Operations.interactionsWith,
    Verifier.Operations.circuitOperations_interactions]
  change List.filter (fun (interaction : AbstractInteraction F) ↦
    decide (interaction.channel = vm.channel.toRaw))
    vm.verifier.interactions = _
  rw [vm.verifier_channel']
  simp only [verifierStep]
  simp only [Channel.pulledIf, Channel.pushedIf, pulledIf_one_eq_pulled,
    pushedIf_one_eq_pushed]
  have pull_channel : (vm.channel.pulled vm.verifierPull).toRaw.channel =
      vm.channel.toRaw := rfl
  have push_channel : (vm.channel.pushed vm.verifierPush).toRaw.channel =
      vm.channel.toRaw := rfl
  simp [pull_channel, push_channel]
  constructor <;> rfl
end VmTables

namespace Ensemble

def addVm (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
    (unique_names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup) : Ensemble F PublicIO where
  channels := vm.channel :: ens.channels
  tables := vm.tables ++ ens.tables
  unique_names
  verifier := vm.verifier

@[circuit_norm] lemma addVm_channels (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (names) :
  (ens.addVm vm names).channels = vm.channel.toRaw :: ens.channels := rfl
@[circuit_norm] lemma addVm_tables (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (names) :
  (ens.addVm vm names).tables = vm.tables ++ ens.tables := rfl
@[circuit_norm] lemma addVm_verifier (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (names) :
  (ens.addVm vm names).verifier = vm.verifier := rfl
end Ensemble

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO} {vm : VmTables F PublicIO}
  {names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup}

abbrev vmTables (witness : EnsembleWitness (ens.addVm vm names)) : List (Table F) :=
  witness.tables.take vm.tables.length

def VmConstraints (witness : EnsembleWitness (ens.addVm vm names)) : Prop :=
  ∀ table ∈ witness.vmTables, table.Constraints witness.data

noncomputable def vmInteractionsWith (witness : EnsembleWitness (ens.addVm vm names))
    (channel : RawChannel F) : List (Interaction F) :=
  witness.verifierInteractionsWith channel ++
    witness.vmTables.flatMap (·.interactionsWith witness.data channel)

lemma vmMemTablesComponent
    {witness : EnsembleWitness (ens.addVm vm names)} {table : Table F} :
    table ∈ witness.vmTables → table.component ∈ vm.tables := by
  intro htable
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htable
  have hi_vm : i < vm.tables.length := by
    have := hi
    simp [List.length_take] at this
    omega
  have hi_full : i < (ens.addVm vm names).tables.length := by
    simp [Ensemble.addVm]
    omega
  have component_eq := witness.same_circuits i hi_full
  rw [List.getElem_take, ← component_eq]
  simp [Ensemble.addVm, hi_vm]

/--
Every committed VM trace is checked *row by row*.

`Ensemble.addVm` only ever adds components with `windowRows = 1`, and `same_circuits` binds the
witness's table to the ensemble's component -- which now *carries* the window, rather than the
window being a separate tag alongside it. So the prover cannot commit a VM component as a
multi-row-window trace: that is not merely forbidden, it is unstateable. This is what lets the
rest of this file keep reasoning about rows.
-/
lemma vmTables_windowRows_eq_one
    {witness : EnsembleWitness (ens.addVm vm names)} {table : Table F} :
    table ∈ witness.vmTables → table.component.windowRows = 1 := by
  intro htable
  have hmem := vmMemTablesComponent htable
  exact (List.forall_iff_forall_mem.mp vm.tables_windowRows) table.component hmem

noncomputable def vmRowEnabled (witness : EnsembleWitness (ens.addVm vm names))
    {table} (_ : table ∈ witness.vmTables) (row : Array F) : F :=
  (Environment.fromArray row witness.data)
    (vm.tableStep (witness.vmMemTablesComponent ‹_›)).enabled

noncomputable def vmRowPull (witness : EnsembleWitness (ens.addVm vm names))
    {table} (_ : table ∈ witness.vmTables) (row : Array F) : vm.Message F :=
  eval (Environment.fromArray row witness.data)
    (vm.tableStep (witness.vmMemTablesComponent ‹_›)).pull

noncomputable def vmRowPush (witness : EnsembleWitness (ens.addVm vm names))
    {table} (_ : table ∈ witness.vmTables) (row : Array F) : vm.Message F :=
  eval (Environment.fromArray row witness.data)
    (vm.tableStep (witness.vmMemTablesComponent ‹_›)).push

noncomputable def vmVerifierEnabled (witness : EnsembleWitness (ens.addVm vm names)) : F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.enabled

lemma vmVerifierEnabled_eq_one (witness : EnsembleWitness (ens.addVm vm names)) : witness.vmVerifierEnabled = 1 := by
  simp only [vmVerifierEnabled, VmTables.verifierStep, circuit_norm]

noncomputable def vmVerifierPull (witness : EnsembleWitness (ens.addVm vm names)) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.pull

noncomputable def vmVerifierPush (witness : EnsembleWitness (ens.addVm vm names)) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.push

noncomputable def vmVerifierPair (witness : EnsembleWitness (ens.addVm vm names)) :
    Interaction F × Interaction F :=
  (vm.channel.pulledValue witness.vmVerifierPull,
    vm.channel.pushedValue witness.vmVerifierPush)

lemma vmVerifierInteractionValuesWith_eq
    (witness : EnsembleWitness (ens.addVm vm names)) :
    witness.verifierInteractionsWith vm.channel.toRaw =
      [witness.vmVerifierPair.1, witness.vmVerifierPair.2] := by
  have h : (ens.addVm vm names).verifierOperations.interactionsWith vm.channel.toRaw = [
      (vm.channel.pulled vm.verifierPull).toRaw,
      (vm.channel.pushed vm.verifierPush).toRaw] := by
    exact vm.verifierInteractionsWith_eq
  rw [EnsembleWitness.verifierInteractionsWith, Operations.interactionValuesWith_eq_map, h]
  simp only [List.map_cons, List.map_nil, vmVerifierPair, vmVerifierPull, vmVerifierPush,
    VmTables.verifierStep, Channel.eval_pulled, Channel.eval_pushed]

lemma vmInteractionValuesWith_eq (witness : EnsembleWitness (ens.addVm vm names))
    {table} (_ : table ∈ witness.vmTables) (row : Array F) :
  table.component.operations.interactionValuesWith vm.channel.toRaw
      (Environment.fromArray row witness.data) = [
    vm.channel.pulledIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPull ‹_› row),
    vm.channel.pushedIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPush ‹_› row) ] := by
  simp only [circuit_norm, vm.interactionsWith_eq (witness.vmMemTablesComponent ‹_›),
    vmRowEnabled, vmRowPull, vmRowPush, AbstractInteraction.eval, ProvableType.toElements_eval]

lemma vmInteractionValuesWith_length (witness : EnsembleWitness (ens.addVm vm names))
    {table} (_ : table ∈ witness.vmTables) (row : Array F) :
  (table.component.operations.interactionValuesWith vm.channel.toRaw
    (Environment.fromArray row witness.data)).length = 2 := by
  simp [witness.vmInteractionValuesWith_eq ‹_› row]

noncomputable def vmInteractionPairs (witness : EnsembleWitness (ens.addVm vm names)) : List (Interaction F × Interaction F) :=
  witness.vmVerifierPair ::
  (witness.vmTables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row =>
      (vm.channel.pulledIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPull ‹_› row),
        vm.channel.pushedIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPush ‹_› row)))

lemma mem_vmInteractionPairs_iff {witness : EnsembleWitness (ens.addVm vm names)} {pair : Interaction F × Interaction F} :
  pair ∈ witness.vmInteractionPairs ↔
    pair = witness.vmVerifierPair ∨
      ∃ (table : Table F) (_ : table ∈ witness.vmTables), ∃ row ∈ table.table,
      pair = (vm.channel.pulledIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPull ‹_› row),
        vm.channel.pushedIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPush ‹_› row)) := by
  simp [vmInteractionPairs]
  tauto

noncomputable def vmPulls (witness : EnsembleWitness (ens.addVm vm names)) : List (Interaction F) :=
  witness.vmInteractionPairs.map Prod.fst

noncomputable def vmPushes (witness : EnsembleWitness (ens.addVm vm names)) : List (Interaction F) :=
  witness.vmInteractionPairs.map Prod.snd

lemma zip_vmPulls_vmPushes_eq_vmInteractionPairs {witness : EnsembleWitness (ens.addVm vm names)} :
    List.zip witness.vmPulls witness.vmPushes = witness.vmInteractionPairs := by
  simp only [vmPulls, vmPushes, List.zip_map_fst_snd]

lemma mem_vmPulls_iff {witness : EnsembleWitness (ens.addVm vm names)} {pull : Interaction F} :
  pull ∈ witness.vmPulls ↔
    pull = witness.vmVerifierPair.1 ∨
      ∃ (table : Table F) (_ : table ∈ witness.vmTables), ∃ row ∈ table.table,
      pull = vm.channel.pulledIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPull ‹_› row) := by
  simp [vmPulls, vmInteractionPairs]
  tauto

lemma mem_vmPushes_iff {witness : EnsembleWitness (ens.addVm vm names)} {push : Interaction F} :
  push ∈ witness.vmPushes ↔
    push = witness.vmVerifierPair.2 ∨
      ∃ (table : Table F) (_ : table ∈ witness.vmTables), ∃ row ∈ table.table,
      push = vm.channel.pushedIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPush ‹_› row) := by
  simp [vmPushes, vmInteractionPairs]
  tauto

def vmSteps (witness : EnsembleWitness (ens.addVm vm names)) : ℕ :=
  witness.vmTables.map (·.length) |>.sum

@[circuit_norm]
lemma vmPulls_length {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPulls.length = witness.vmSteps + 1 := by
  simp [vmSteps, vmPulls, vmInteractionPairs, vmTables, circuit_norm]

@[circuit_norm]
lemma vmPushes_length {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPushes.length = witness.vmSteps + 1 := by
  simp [vmSteps, vmPushes, vmInteractionPairs, vmTables, circuit_norm]

lemma vmRowEnabled_isBool_of_constraints {witness : EnsembleWitness (ens.addVm vm names)} :
    witness.VmConstraints →
    ∀ table (_ : table ∈ witness.vmTables), ∀ row ∈ table.table,
      IsBool (witness.vmRowEnabled ‹_› row) := by
  intro constraints table table_mem row row_mem
  exact vm.tableStep_enabled_isBool (witness.vmMemTablesComponent table_mem) _
    (constraints table table_mem _
      (Table.mem_envs_of_mem_table (vmTables_windowRows_eq_one table_mem) row_mem))

lemma vmPulls_mult {witness : EnsembleWitness (ens.addVm vm names)} :
  witness.VmConstraints →
    ∀ pull ∈ witness.vmPulls, pull.mult = 0 ∨ pull.mult = -1 := by
  intro constraints pull h_pull
  rw [witness.mem_vmPulls_iff] at h_pull
  rcases h_pull with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [vmVerifierPair, Channel.pulledValue]
  · simp only [circuit_norm, neg_inj]
    apply witness.vmRowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›

lemma vmPushes_mult {witness : EnsembleWitness (ens.addVm vm names)} :
  witness.VmConstraints →
    ∀ push ∈ witness.vmPushes, push.mult = 0 ∨ push.mult = 1 := by
  intro constraints push h_push
  rw [witness.mem_vmPushes_iff] at h_push
  rcases h_push with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [vmVerifierPair, Channel.pushedValue]
  · simp only [circuit_norm]
    apply witness.vmRowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›

lemma vmPulls_zero_iff_vmPushes_zero {witness : EnsembleWitness (ens.addVm vm names)} :
    ∀ i (hi : i < witness.vmPulls.length) (hi' : i < witness.vmPushes.length),
      witness.vmPulls[i].mult = 0 ↔ witness.vmPushes[i].mult = 0 := by
  intro i hi_p hi_q
  simp only [vmPulls, vmPushes, List.getElem_map]
  have hi : i < witness.vmInteractionPairs.length := by
    simpa [vmPulls, vmInteractionPairs] using hi_p
  have pair_mem : witness.vmInteractionPairs[i]'hi ∈ witness.vmInteractionPairs := List.getElem_mem _
  rw [mem_vmInteractionPairs_iff] at pair_mem
  rcases pair_mem with hpair | ⟨table, table_mem, row, row_mem, hpair⟩
  · rw [hpair]
    simp [vmVerifierPair, Channel.pulledValue, Channel.pushedValue]
  · rw [hpair]
    simp only [circuit_norm]

@[circuit_norm]
lemma vmPulls_channel {witness : EnsembleWitness (ens.addVm vm names)} : ∀ pull ∈ witness.vmPulls, pull.channel = vm.channel.toRaw := by
  intro pull h_pull
  rw [mem_vmPulls_iff] at h_pull
  rcases h_pull with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [vmVerifierPair, Channel.pulledValue]
  · simp only [circuit_norm]

@[circuit_norm]
lemma vmPushes_channel {witness : EnsembleWitness (ens.addVm vm names)} : ∀ push ∈ witness.vmPushes, push.channel = vm.channel.toRaw := by
  intro push h_push
  rw [mem_vmPushes_iff] at h_push
  rcases h_push with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [vmVerifierPair, Channel.pushedValue]
  · simp only [circuit_norm]

lemma vmInteractionss_eq_interactionPairs (witness : EnsembleWitness (ens.addVm vm names)) :
  [witness.verifierInteractionsWith vm.channel.toRaw] ++
      witness.vmTables.flatMap (·.interactionssWith witness.data vm.channel.toRaw) =
    witness.vmInteractionPairs.map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [witness.vmVerifierInteractionValuesWith_eq]
  simp only [vmInteractionPairs, List.flatMap_def, List.map_flatten, List.map_cons,
    List.singleton_append]
  congr 1
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ⟨ table, table_mem ⟩ _
  simp [RowEnvs.interactionssWith, Table.component_eq,
    Table.envs_eq_of_flat _ _ (witness.vmTables_windowRows_eq_one table_mem),
    witness.vmInteractionValuesWith_eq table_mem]

lemma vmInteractionss_eq_pulls_pushes (witness : EnsembleWitness (ens.addVm vm names)) :
  [witness.verifierInteractionsWith vm.channel.toRaw] ++
      witness.vmTables.flatMap (·.interactionssWith witness.data vm.channel.toRaw) =
    (List.zip witness.vmPulls witness.vmPushes).map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [vmInteractionss_eq_interactionPairs]
  simp [vmPulls, vmPushes, List.zip_map_fst_snd]

lemma vmInteractions_eq_pulls_pushes (witness : EnsembleWitness (ens.addVm vm names)) :
  witness.vmInteractionsWith vm.channel.toRaw =
    (List.zip witness.vmPulls witness.vmPushes).flattenPairs := by
  have unfold_interactions : witness.vmInteractionsWith vm.channel.toRaw =
      ([witness.verifierInteractionsWith vm.channel.toRaw] ++
        witness.vmTables.flatMap
          (·.interactionssWith witness.data vm.channel.toRaw)).flatten := by
    simp only [vmInteractionsWith, RowEnvs.interactionsWith, RowEnvs.interactionssWith,
      List.singleton_append, List.flatten_cons]
    rw [List.flatMap_flatMap, List.flatMap_def]
  rw [unfold_interactions, vmInteractionss_eq_pulls_pushes, List.flattenPairs]

lemma vmMem_zip_pulls_pushes_iff (witness : EnsembleWitness (ens.addVm vm names)) (pull push : Interaction F) :
  (pull, push) ∈ List.zip witness.vmPulls witness.vmPushes ↔
    (pull, push) = witness.vmVerifierPair ∨
      ∃ table ∈ witness.vmTables, ∃ row ∈ table.table,
        table.component.operations.interactionValuesWith vm.channel.toRaw
          (Environment.fromArray row witness.data) = [pull, push] := by
  rw [witness.zip_vmPulls_vmPushes_eq_vmInteractionPairs,
    witness.mem_vmInteractionPairs_iff]
  constructor
  · rintro (h_verifier | ⟨table, h_table, row, h_row, h_pair⟩)
    · exact Or.inl h_verifier
    · right
      refine ⟨table, h_table, row, h_row, ?_⟩
      rw [witness.vmInteractionValuesWith_eq h_table]
      exact congrArg (fun pair => [pair.1, pair.2]) h_pair.symm
  · rintro (h_verifier | ⟨table, h_table, row, h_row, h_interactions⟩)
    · exact Or.inl h_verifier
    · right
      refine ⟨table, h_table, row, h_row, ?_⟩
      rw [witness.vmInteractionValuesWith_eq h_table] at h_interactions
      simp only [List.cons.injEq, and_true] at h_interactions
      exact Prod.ext h_interactions.left.symm h_interactions.right.symm

lemma vmPullRequirementsOfConstraints {witness : EnsembleWitness (ens.addVm vm names)} :
  witness.VmConstraints →
    ∀ pull ∈ witness.vmPulls, pull.Requirements witness.data := by
  intro constraints pull h_pull
  rw [witness.mem_vmPulls_iff] at h_pull
  rcases h_pull with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · have verifier_requirements := vm.verifier_requirements
      (Environment.fromInput witness.publicInput witness.data)
    change (ens.addVm vm names).VerifierChannelRequirements witness.publicInput witness.data
      vm.channel.toRaw at verifier_requirements
    rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements
    apply verifier_requirements
    rw [witness.vmVerifierInteractionValuesWith_eq]
    simp
  · apply Channel.pulledIfValue_requirements_of_isBool_enabled
    apply witness.vmRowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›

lemma vmPushGuarantees {witness : EnsembleWitness (ens.addVm vm names)} :
  ∀ push ∈ witness.vmPushes, push.Guarantees witness.data := by
  intro push h_push
  rw [witness.mem_vmPushes_iff] at h_push
  rcases h_push with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  <;> apply Channel.pushedIfValue_guarantees

lemma vmPulls_length_pos {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPulls.length > 0 := by
  simp [vmPulls_length]
lemma vmPushes_length_pos {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPushes.length > 0 := by
  simp [vmPushes_length]

lemma vmPulls_getElem_zero_eq (witness : EnsembleWitness (ens.addVm vm names)) :
    witness.vmPulls[0]'vmPulls_length_pos =
      vm.channel.pulledIfValue witness.vmVerifierEnabled witness.vmVerifierPull := by
  rw [witness.vmVerifierEnabled_eq_one]
  rfl

lemma vmPushes_getElem_zero_eq (witness : EnsembleWitness (ens.addVm vm names)) :
    witness.vmPushes[0]'vmPushes_length_pos =
      vm.channel.pushedIfValue witness.vmVerifierEnabled witness.vmVerifierPush := by
  rw [witness.vmVerifierEnabled_eq_one]
  rfl

lemma activeInteractions_vmPulls_length_pos {witness : EnsembleWitness (ens.addVm vm names)} :
    (activeInteractions witness.vmPulls).length > 0 := by
  simp_rw [activeInteractions, ←List.countP_eq_length_filter, List.countP_pos_iff]
  use witness.vmPulls[0]'vmPulls_length_pos, List.getElem_mem vmPulls_length_pos
  rw [witness.vmPulls_getElem_zero_eq]
  simp [circuit_norm, vmVerifierEnabled_eq_one]

lemma activeInteractions_vmPushes_length_pos {witness : EnsembleWitness (ens.addVm vm names)} :
    (activeInteractions witness.vmPushes).length > 0 := by
  simp_rw [activeInteractions, ←List.countP_eq_length_filter, List.countP_pos_iff]
  use witness.vmPushes[0]'vmPushes_length_pos, List.getElem_mem vmPushes_length_pos
  rw [witness.vmPushes_getElem_zero_eq]
  simp [circuit_norm, vmVerifierEnabled_eq_one]

lemma activeInteractions_vmPulls_getElem_zero_eq {witness : EnsembleWitness (ens.addVm vm names)} :
    (activeInteractions witness.vmPulls)[0]'activeInteractions_vmPulls_length_pos =
      vm.channel.pulledIfValue witness.vmVerifierEnabled witness.vmVerifierPull := by
  rw [witness.vmVerifierEnabled_eq_one]
  simp [activeInteractions, vmPulls, vmInteractionPairs, vmVerifierPair,
    Channel.pulledValue, Channel.pulledIfValue]

lemma activeInteractions_vmPushes_getElem_zero_eq {witness : EnsembleWitness (ens.addVm vm names)} :
    (activeInteractions witness.vmPushes)[0]'activeInteractions_vmPushes_length_pos =
      vm.channel.pushedIfValue witness.vmVerifierEnabled witness.vmVerifierPush := by
  rw [witness.vmVerifierEnabled_eq_one]
  simp [activeInteractions, vmPushes, vmInteractionPairs, vmVerifierPair,
    Channel.pushedValue, Channel.pushedIfValue]

/-- Translation of the VM soundness theorem to VmTables -/
theorem vmVerifierGuarantees
  [Fact (ringChar F ≠ 2)] (witness : EnsembleWitness (ens.addVm vm names)) :
  -- if the vm interactions with the vm channel are balanced
  BalancedInteractions (witness.vmInteractionsWith vm.channel.toRaw) →
  witness.VmConstraints →
  -- and for every row, vm channel guarantees imply vm channel requirements
  -- (this will come from constraints + soundness of the existing ensemble)
  (∀ table ∈ witness.vmTables, ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees vm.channel.toRaw
      (Environment.fromArray row witness.data) →
    table.component.operations.ChannelRequirements vm.channel.toRaw
      (Environment.fromArray row witness.data)) →
  -- vm channel verifier requirements imply vm channel verifier guarantees
  (ens.addVm vm names).VerifierChannelRequirements witness.publicInput witness.data
      vm.channel.toRaw →
    (ens.addVm vm names).VerifierChannelGuarantees witness.publicInput witness.data
      vm.channel.toRaw := by
  intro balance witness_constraints constraints verifier_requirements
  have row_enabled_boolean := witness.vmRowEnabled_isBool_of_constraints witness_constraints
  -- prove balance of vmPulls + vmPushes
  replace balance : BalancedInteractions (witness.vmPulls ++ witness.vmPushes) := by
    rw [witness.vmInteractions_eq_pulls_pushes] at balance
    apply balancedInteractions_of_perm balance
    apply List.zip_flattenPairs_perm <| witness.vmPushes_length ▸ witness.vmPulls_length.symm
  -- we fill in the conditions on vmPulls and vmPushes in `guarantees_of_requirements_of_requirements_of_guarantees`
  let n := (activeInteractions witness.vmPulls).length
  have same_length : witness.vmPulls.length = witness.vmPushes.length := by
    simp [vmPulls_length, vmPushes_length]
  have : (activeInteractions witness.vmPushes).length = n := by
    simp only [n, activeInteractions_length_eq same_length witness.vmPulls_zero_iff_vmPushes_zero]
  have grts_of_reqs := guarantees_of_requirements_of_requirements_of_guarantees_of_mult_zero_iff
    vm.channel.toRaw witness.vmPulls witness.vmPushes balance witness.data same_length
    witness.vmPulls_channel witness.vmPushes_channel
    (witness.vmPulls_mult witness_constraints) (witness.vmPushes_mult witness_constraints)
    witness.vmPulls_zero_iff_vmPushes_zero
  -- it remains to prove the (grts → reqs) assumption. this is a reformulation of our `constraints`
  have reqs_of_grts : (∀ i (hi : i < n),
      (activeInteractions witness.vmPulls)[i].Guarantees witness.data →
      (activeInteractions witness.vmPushes)[i].Requirements witness.data) := by
    suffices ∀ pair ∈ (witness.vmPulls.zip witness.vmPushes), pair.1.Guarantees witness.data → pair.2.Requirements witness.data by
      intro i hi
      exact this _ (activePair_mem_zip same_length witness.vmPulls_zero_iff_vmPushes_zero _ hi)
    intro (pull, push) pair_mem
    simp only
    have ⟨ mem_pull, mem_push ⟩ := List.of_mem_zip pair_mem
    have push_grts := witness.vmPushGuarantees push mem_push
    have pull_reqs := witness.vmPullRequirementsOfConstraints witness_constraints pull mem_pull
    rw [witness.vmMem_zip_pulls_pushes_iff] at pair_mem
    rcases pair_mem with h_verifier | ⟨table, table_mem, row, row_mem, interactions_eq⟩
    · have verifier_requirements' := verifier_requirements
      rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements'
      have h_pull := congrArg Prod.fst h_verifier
      have h_push := congrArg Prod.snd h_verifier
      simp only at h_pull h_push
      subst pull
      subst push
      intro _
      apply verifier_requirements'
      rw [witness.vmVerifierInteractionValuesWith_eq]
      simp
    · suffices (∀ i ∈ [pull, push], i.Guarantees witness.data) →
          (∀ i ∈ [pull, push], i.Requirements witness.data) by
        simp_all
      rw [← interactions_eq, Operations.interactionValuesWith_eq_map,
        List.forall_mem_map, List.forall_mem_map]
      simp only [Operations.forall_interactionsWith_iff]
      exact constraints table table_mem row row_mem
  -- to get the conclusion about the verifier, we specialize to index 0
  specialize grts_of_reqs reqs_of_grts 0 activeInteractions_vmPulls_length_pos
  rw [witness.activeInteractions_vmPulls_getElem_zero_eq,
    witness.activeInteractions_vmPushes_getElem_zero_eq] at grts_of_reqs
  have verifier_requirements' := verifier_requirements
  rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements'
  have push_requirements :
      (vm.channel.pushedIfValue witness.vmVerifierEnabled witness.vmVerifierPush).Requirements
        witness.data := by
    apply verifier_requirements'
    rw [witness.vmVerifierInteractionValuesWith_eq, witness.vmVerifierEnabled_eq_one]
    simp [vmVerifierPair, Channel.pushedIfValue, Channel.pushedValue]
  specialize grts_of_reqs push_requirements
  rw [witness.vmVerifierEnabled_eq_one] at grts_of_reqs
  rw [witness.verifierChannelGuarantees_iff_forall]
  intro interaction h_interaction
  rw [witness.vmVerifierInteractionValuesWith_eq] at h_interaction
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_interaction
  rcases h_interaction with rfl | rfl
  · simpa [vmVerifierPair, Channel.pulledIfValue, Channel.pulledValue] using grts_of_reqs
  · apply Channel.pushedIfValue_guarantees
end EnsembleWitness

namespace Ensemble

theorem addVm_soundVmChannel_of_soundChannels [Fact (ringChar F ≠ 2)] (ens : Ensemble F PublicIO)
      -- given a sound channels ensemble with a list of finished, consistent channels
    {finished : List (RawChannel F)} (soundChannels : ens.SoundChannels finished)
    (consistent : ∀ channel ∈ finished, channel.Consistent)
    (finished_subset : finished ⊆ ens.channels)
    -- and given a VM channel + tables + verifier
    (vm : VmTables F PublicIO)
    (names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup) :
    -- assuming that none of the existing tables interacted with the VM channel
    (∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) →
    -- assuming that the VM tables' and verifier's channelsWithGuarantees are either finished or the VM channel
    (vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished) →
    -- and assuming the VM tables' channelsWithRequirements contain none of the finished ones
    (∀ channel ∈ finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the VM tables satisfies SoundVmChannel
    (ens.addVm vm names).SoundVmChannel := by
  intro not_mem_vm_channel grts_subset reqs_disjoint witness assumptions constraints balance
  /-
  the high level plan is to apply
  `verifier_guarantees_of_requirements_of_requirements_of_guarantees`.

  1) we need to narrow vm channel balance to just the vm tables
  2) guarantees for finished channels follows from soundChannels + constraints, using
     `spec_and_guarantees_of_soundChannels` and `guarantees_of_requirements_append`
     as the key lemmas.
  3) the combination of guarantees for finished channels + vm constraints gives us the main condition:
     "vm guarantees → vm requirements", by invoking `requirements_of_partial_guarantees_of_constraints`.
  4) finally, `VmTables.verifier_requirements` gives us the unconditional requirements for the verifier,
     from which the conclusion follows.
  -/
  have witness_length : witness.tables.length = vm.tables.length + ens.tables.length := by
    rw [← witness.same_length]
    simp [Ensemble.addVm]
  have old_component_of_mem : ∀ table ∈ witness.tables.drop vm.tables.length,
      table.component ∈ ens.tables := by
    intro table htable
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htable
    have hi_old : i < ens.tables.length := by
      simpa [List.length_drop, witness_length] using hi
    have hi_full : vm.tables.length + i < (ens.addVm vm names).tables.length := by
      simp [Ensemble.addVm]
      omega
    have component_eq := witness.same_circuits (vm.tables.length + i) hi_full
    rw [List.getElem_drop]
    rw [← component_eq]
    simp [Ensemble.addVm]
  have old_components_eq :
      (witness.tables.drop vm.tables.length).map (·.component) = ens.tables := by
    apply List.ext_getElem
    · simp [List.length_drop, witness_length]
    · intro i hi hi'
      have hi_full : vm.tables.length + i < (ens.addVm vm names).tables.length := by
        simp [Ensemble.addVm]
        omega
      rw [List.getElem_map, List.getElem_drop, ← witness.same_circuits _ hi_full]
      simp [Ensemble.addVm]
  let vmContext : TableContext F := {
    tables := witness.vmTables
    data := witness.data
    data_consistent := by
      intro table htable
      exact witness.data_consistent table (List.mem_of_mem_take htable)
  }
  let oldContext : TableContext F := {
    tables := witness.tables.drop vm.tables.length
    data := witness.data
    data_consistent := by
      intro table htable
      exact witness.data_consistent table (List.mem_of_mem_drop htable)
  }
  set vmChannel := vm.channel.toRaw
  -- the vm channel interactions are constrained to vm tables
  have vmInteractions_eq : witness.interactionsWith vmChannel =
      witness.vmInteractionsWith vmChannel := by
    simp only [EnsembleWitness.interactionsWith, EnsembleWitness.vmInteractionsWith,
      EnsembleWitness.tableContext, TableContext.interactionsWith]
    rw [show witness.tables = witness.vmTables ++ witness.tables.drop vm.tables.length by
      exact (List.take_append_drop vm.tables.length witness.tables).symm,
      List.flatMap_append]
    suffices (witness.tables.drop vm.tables.length).flatMap
        (·.interactionsWith witness.data vmChannel) = [] by
      rw [this, List.append_nil]
    simp only [List.flatMap_eq_nil_iff]
    intro table mem_table
    apply RowEnvs.interactionsWith_nil_of_channel_not_mem
    apply not_mem_vm_channel table.component
    exact old_component_of_mem table mem_table
  -- this already lets us supply the balance condition
  have vm_balance := balance vmChannel (by simp [vmChannel, Ensemble.addVm])
  simp only [circuit_norm, vmInteractions_eq] at vm_balance
  -- next, we work on instantiating `requirements_of_partial_guarantees_of_constraints`
  -- which will give us exactly the second hypothesis of `verifier_guarantees`
  -- first, unify channel subset assumptions to all tables
  have grts_subset_all : ∀ table ∈ witness.vmTables,
      RowEnvs.channelsWithGuarantees (F:=F) table ⊆ vmChannel :: finished := by
    intro table h_table
    apply grts_subset.2 table.component
    exact witness.vmMemTablesComponent h_table
  have vm_reqs_disjoint : ∀ channel ∈ finished, ∀ table ∈ witness.vmTables,
      channel ∉ RowEnvs.channelsWithRequirements (F:=F) table := by
    intro channel channel_mem table table_mem
    apply (reqs_disjoint channel channel_mem).2
    exact witness.vmMemTablesComponent table_mem
  -- specialize constraints and assumptions to both old and vm ensemble
  have old_constraints : oldContext.Constraints := by
    intro table table_mem
    exact constraints table (List.mem_of_mem_drop table_mem)
  have vm_constraints : witness.VmConstraints := by
    intro table table_mem
    exact constraints table (List.mem_of_mem_take table_mem)
  have old_assumptions : oldContext.Assumptions := by
    intro table table_mem
    exact assumptions table (List.mem_of_mem_drop table_mem)
  have vm_assumptions : ∀ table ∈ witness.vmTables,
      table.Assumptions witness.data := by
    intro table table_mem
    exact assumptions table (List.mem_of_mem_take table_mem)
  -- establish partial balance + specialize to old ensemble
  have ordered_finished : ∀ channel ∈ finished,
      (ens.addVm vm names).OrderedChannel channel := by
    intro channel channel_mem
    rw [Ensemble.OrderedChannel]
    constructor
    · right
      exact (reqs_disjoint channel channel_mem).1
    constructor
    · rw [Ensemble.addVm_tables, orderedChannel_append]
      exact ⟨
        orderedChannel_of_no_requirements (by
          intro table h_table
          change channel ∉ table.circuit.channelsWithRequirements
          exact (reqs_disjoint channel channel_mem).2 table h_table),
        (soundChannels.right.left channel channel_mem).right.left,
        orderedChannelLt_of_no_requirements (by
          intro table h_table
          change channel ∉ table.circuit.channelsWithRequirements
          exact (reqs_disjoint channel channel_mem).2 table h_table)⟩
    · right
      rw [Ensemble.addVm_verifier, List.flatMap_singleton,
        Air.Flat.verifier_channelInterface_requirements]
      exact (reqs_disjoint channel channel_mem).1
  have partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel witness.tableContext channel := by
    intro channel channel_mem
    apply Ensemble.partialBalancedChannel_of_balancedChannel
    · exact ordered_finished channel channel_mem
    · exact balance channel (by simp [Ensemble.addVm, finished_subset channel_mem])
  have old_partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel oldContext channel := by
    intro channel' channel_mem'
    apply partialBalancedChannel_of_sublist (subtables := oldContext)
      (tables := witness.tableContext) rfl (partial_balance _ channel_mem')
    use vmContext.tables
    constructor
    · simp only [oldContext, vmContext, EnsembleWitness.tableContext]
      have h_split : witness.tables = witness.vmTables ++
          witness.tables.drop vm.tables.length :=
        (List.take_append_drop vm.tables.length witness.tables).symm
      exact (List.Perm.of_eq h_split).trans List.perm_append_comm
    exact ⟨vm_constraints, vm_reqs_disjoint _ channel_mem'⟩
  -- invoke old tables soundness to get reqs for finished channels from constraints
  -- uses `soundChannels`, `old_constraints`, and `old_partial_balance`
  have finished_reqs : ∀ channel ∈ finished, ∀ table ∈ oldContext.tables,
      table.ChannelRequirements witness.data channel := by
    intro channel channel_mem table table_mem
    refine spec_and_guarantees_of_soundChannels (witness := oldContext)
      ?soundChannels old_assumptions old_constraints old_partial_balance table table_mem
      |>.right channel channel_mem |>.right
    have old_sound_channels : _root_.SoundChannels ens.tables finished := ⟨
      ens.channelsWithGuarantees_subset_iff.mp soundChannels.left |>.right,
      fun channel h_channel => (soundChannels.right.left channel h_channel).right.left,
      soundChannels.right.right⟩
    simpa only [oldContext, old_components_eq] using old_sound_channels
  -- invoke `guarantees_of_requirements_append` to get grts for finished channels in vm tables
  have combined_partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel (vmContext.append oldContext rfl) channel := by
    intro channel h_channel
    simpa only [vmContext, oldContext, EnsembleWitness.tableContext,
      TableContext.append, List.take_append_drop] using partial_balance channel h_channel
  have finished_grts : ∀ table ∈ witness.vmTables, ∀ channel ∈ finished,
      table.ChannelGuarantees witness.data channel := by
    intro table table_mem channel channel_mem
    have : channel.Consistent := consistent channel channel_mem
    apply guarantees_of_requirements_append (ts := vmContext)
      (ss := oldContext) rfl vm_constraints (vm_reqs_disjoint _ channel_mem)
      (combined_partial_balance _ channel_mem) (finished_reqs _ channel_mem) _ table_mem
  -- invoke `requirements_of_partial_guarantees_of_constraints` to get per-row grts → reqs for the vm channel,
  -- and use it in `verifier_guarantees`
  have reqs_of_grts' (table) (h_table : table ∈ witness.vmTables) :=
    RowEnvs.requirements_of_partial_guarantees_of_constraints (table:=table)
    (unfinished := vmChannel)
    (Table.circuitAssumptions_envs table (vmContext.data_consistent table h_table)
      (vm_assumptions table h_table))
    (vm_constraints table h_table)
    (grts_subset_all table h_table) (finished_grts table h_table)
  -- specialize the environment-quantified statement back to rows, which is valid because
  -- every VM trace is flat (`vmTables_windowRows_eq_one`)
  have reqs_of_grts (table) (h_table : table ∈ witness.vmTables) (row) (h_row : row ∈ table.table) :=
    reqs_of_grts' table h_table _
      (Table.mem_envs_of_mem_table (witness.vmTables_windowRows_eq_one h_table) h_row)
  have verifier_requirements :
      (ens.addVm vm names).VerifierChannelRequirements witness.publicInput witness.data
        vm.channel.toRaw := by
    exact vm.verifier_requirements (Environment.fromInput witness.publicInput witness.data)
  have vm_verifier_guarantees := witness.vmVerifierGuarantees vm_balance vm_constraints
    reqs_of_grts verifier_requirements
  have finished_verifier_guarantees : ∀ channel ∈ finished,
      (ens.addVm vm names).VerifierChannelGuarantees witness.publicInput witness.data channel := by
    intro channel channel_mem
    letI : channel.Consistent := consistent channel channel_mem
    apply Ensemble.verifierChannelGuarantees_of_tableRequirements
    · right
      exact (reqs_disjoint channel channel_mem).1
    · exact balance channel (by simp [Ensemble.addVm, finished_subset channel_mem])
    intro table h_table
    by_cases h_vm : table ∈ witness.vmTables
    · apply RowEnvs.requirements_of_not_mem_of_constraints (table:=table) witness.data
        (vm_constraints table h_vm)
      exact vm_reqs_disjoint channel channel_mem table h_vm
    · have h_old : table ∈ oldContext.tables := by
        simp only [oldContext]
        have h_split : witness.tables =
            witness.vmTables ++ witness.tables.drop vm.tables.length := by
          exact (List.take_append_drop vm.tables.length witness.tables).symm
        rw [h_split, List.mem_append] at h_table
        exact h_table.resolve_left h_vm
      exact finished_reqs channel channel_mem table h_old
  rw [Ensemble.VerifierGuarantees]
  rw [Operations.guarantees_iff (ens.addVm vm names).verifierOperations
    vm.verifier.channelsWithGuarantees (.fromInput witness.publicInput witness.data)]
  · intro channel h_channel
    rcases List.mem_cons.mp (grts_subset.1 h_channel) with rfl | h_finished
    · exact vm_verifier_guarantees
    · exact finished_verifier_guarantees channel h_finished
  · exact vm.verifier.operations.inChannelsOrGuaranteesFull _
end Ensemble

namespace SoundEnsemble

def addVm [Fact (ringChar F ≠ 2)] (ens : SoundEnsemble F PublicIO) (vm : VmTables F PublicIO)
    (ne_mem_vm_channel : ∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels
      := by simp [circuit_norm])
    (grts_subset_finished : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished
      := by simp [circuit_norm])
    (reqs_disjoint_finished : ∀ channel ∈ ens.finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements
      := by simp [circuit_norm])
    (names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup := by simp [circuit_norm]) :
    SoundVmEnsemble F PublicIO where
  __ := ens.ensemble.addVm vm names
  soundVmChannel := ens.ensemble.addVm_soundVmChannel_of_soundChannels
    ens.soundChannels ens.finished_consistent ens.finished_subset vm names
    ne_mem_vm_channel grts_subset_finished reqs_disjoint_finished

variable {soundEns : SoundEnsemble F PublicIO} {vm : VmTables F PublicIO}
  {nmv : ∀ table ∈ soundEns.ensemble.tables, vm.channel.toRaw ∉ table.circuit.channels}
  {gsf : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished ∧
    ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished}
  {rdf : ∀ channel ∈ soundEns.finished, channel ∉ vm.verifier.channelsWithRequirements ∧
    ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements}
  {names : ((vm.tables ++ soundEns.tables).map (·.circuit.name)).Nodup}

@[circuit_norm] lemma addVm_tables [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf names).tables = vm.tables ++ soundEns.tables := rfl
@[circuit_norm] lemma addVm_channels [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf names).channels = vm.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addVm_verifier [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf names).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_ensemble [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf names).ensemble = soundEns.ensemble.addVm vm names := rfl

end SoundEnsemble
end Air.Flat
