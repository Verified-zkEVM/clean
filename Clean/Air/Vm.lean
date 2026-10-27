module

public import Clean.Air.FlatEnsemble
public import Clean.Air.OrderedChannel

@[expose] public section

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
  unique_names : (tables.map (·.circuit.name)).Nodup := by simp
  verifier : Verifier.Program F PublicIO

  tables_channel : tables.Forall fun table =>
    ∃ enabled : Expression F, ∃ pull push : Var Message F,
      ⟨ channel, [(channel.pulledIf enabled pull).toRaw, (channel.pushedIf enabled push).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      ∀ env, ConstraintsHold.Shallow env table.rowOperations →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1

  -- On the VM channel, the public verifier pulls the final state and pushes the initial state.
  -- Its interactions on other channels are unconstrained.
  verifier_channel : ∃ m1 m2, verifier.circuitOperations.interactionsWith channel.toRaw =
    [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw]

  -- verifier requirements hold unconditionally (without relying on channel guarantees)
  verifier_requirements :
    ∀ env,
      Operations.ChannelRequirements channel env verifier.circuitOperations

instance (vm : VmTables F PublicIO) : ProvableType vm.Message := vm.provableMessage

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

/-- Declare the prover's private input: its type, and the hint tables viewing it. -/
def withProverInput (ens : SoundVmEnsemble F PublicIO) (ProverInput : TypeMap)
    [ProvableType ProverInput] (hintTables : List HintTable) : SoundVmEnsemble F PublicIO where
  ensemble := ens.ensemble.withProverInput ProverInput hintTables
  -- the witnesses of both ensembles have the same tables
  soundVmChannel witness := ens.soundVmChannel { witness with }

@[circuit_norm] lemma withProverInput_ensemble (ens : SoundVmEnsemble F PublicIO)
    (ProverInput : TypeMap) [ProvableType ProverInput] (hintTables : List HintTable) :
    (ens.withProverInput ProverInput hintTables).ensemble =
      ens.ensemble.withProverInput ProverInput hintTables := rfl
/--
Bundle a sound VM ensemble with its public statement. `Assumptions` and `Spec` only refer to the
public input. The verifier spec is evaluated on prover data derived from the witness, so the bridge
from it to `Spec` quantifies over witnesses.
-/
def toFormal (ens : SoundVmEnsemble F PublicIO) (balance : Balance F)
    (Assumptions Spec : PublicIO F → Prop)
    (assumptionsConsistency : ens.ensemble.AssumptionsConsistency Assumptions)
    (spec_of_verifierSpec : ∀ witness : EnsembleWitness ens.ensemble,
      Assumptions witness.publicInput →
      ens.VerifierSpec witness.publicInput witness.data → Spec witness.publicInput)
    (ProverAssumptions : PublicIO F → ens.ensemble.ProverInput F → Prop := fun _ _ => True) :
    FormalEnsemble F PublicIO balance where
  ensemble := ens.ensemble
  Assumptions
  Spec
  ProverAssumptions
  soundness := by
    intro publicInput assumptions ⟨witness, input_eq, constraints, balanced⟩
    subst input_eq
    apply spec_of_verifierSpec witness assumptions
    apply ens.ensemble.verifierSpec_of_verifierGuarantees
    exact ens.soundVmChannel witness
      (Ensemble.assumptions_of_assumptionsConsistency assumptionsConsistency witness assumptions)
      constraints (EnsembleWitness.balancedChannels_of_balanced balanced)
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
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.left

theorem step_enabled_isBool (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
    ∀ env, table.operations.ConstraintsHold env →
      IsBool (Expression.eval env (vm.step table_mem).enabled) :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.right

noncomputable def verifierPull (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose

noncomputable def verifierPush (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose_spec.choose

/-- Concrete version of VmTables.verifier_channel -/
theorem verifier_channel' (vm : VmTables F PublicIO) :
  vm.verifier.circuitOperations.interactionsWith vm.channel.toRaw =
    [(vm.channel.pulled vm.verifierPull).toRaw,
      (vm.channel.pushed vm.verifierPush).toRaw] :=
  vm.verifier_channel.choose_spec.choose_spec

noncomputable def verifierStep (vm : VmTables F PublicIO) : VmStep vm.Message F where
  enabled := 1
  pull := vm.verifierPull
  push := vm.verifierPush

lemma interactionsWith_eq {vm : VmTables F PublicIO} {table} (h : table ∈ vm.tables) :
  table.operations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf (vm.step h).enabled (vm.step h).pull).toRaw,
    (vm.channel.pushedIf (vm.step h).enabled (vm.step h).push).toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  apply vm.tables_channel'

lemma verifierInteractionsWith_eq {vm : VmTables F PublicIO} :
  vm.verifier.circuitOperations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf vm.verifierStep.enabled vm.verifierStep.pull).toRaw,
    (vm.channel.pushedIf vm.verifierStep.enabled vm.verifierStep.push).toRaw ] := by
  rw [vm.verifier_channel']
  simp only [verifierStep, Channel.pulledIf, Channel.pushedIf, pulledIf_one_eq_pulled,
    pushedIf_one_eq_pushed]
  rfl
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

noncomputable def verifierEnabled (witness : VmWitness ens vm fits) : F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.enabled

lemma verifierEnabled_eq_one (witness : VmWitness ens vm fits) : witness.verifierEnabled = 1 := by
  simp only [verifierEnabled, VmTables.verifierStep, circuit_norm]

noncomputable def verifierPull (witness : VmWitness ens vm fits) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.pull

noncomputable def verifierPush (witness : VmWitness ens vm fits) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.push

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
    exact vm.verifierInteractionsWith_eq
  rw [EnsembleWitness.verifierInteractionsWith, Operations.interactionValuesWith_eq_map, h]
  simp only [List.map_cons, List.map_nil, verifierPair, verifierPull, verifierPush,
    VmTables.verifierStep, Channel.eval_pulled, Channel.eval_pushed]

lemma interactionValuesWith_eq (witness : VmWitness ens vm fits)
    {table} (h : table ∈ witness.vmTables) (row : Array F) :
  table.component.operations.interactionValuesWith vm.channel.toRaw
      (table.environment row) = [
    vm.channel.pulledIfValue (witness.rowEnabled h row) (witness.rowPull h row),
    vm.channel.pushedIfValue (witness.rowEnabled h row) (witness.rowPush h row) ] := by
  simp only [circuit_norm, vm.interactionsWith_eq (witness.component_mem_tables_of_mem_vmTables h),
    rowEnabled, rowPull, rowPush, AbstractInteraction.eval, ProvableType.toElements_eval]

lemma interactionValuesWith_length (witness : VmWitness ens vm fits)
    {table} (h : table ∈ witness.vmTables) (row : Array F) :
  (table.component.operations.interactionValuesWith vm.channel.toRaw
    (table.environment row)).length = 2 := by
  simp [witness.interactionValuesWith_eq h row]

noncomputable def interactionPairs (witness : VmWitness ens vm fits) :
    List (Interaction F × Interaction F) :=
  witness.verifierPair ::
  (witness.vmTables.attach.flatMap fun ⟨ table, h ⟩ =>
    table.table.map fun row =>
      (vm.channel.pulledIfValue (witness.rowEnabled h row) (witness.rowPull h row),
        vm.channel.pushedIfValue (witness.rowEnabled h row) (witness.rowPush h row)))

lemma mem_interactionPairs_iff {witness : VmWitness ens vm fits}
    {pair : Interaction F × Interaction F} :
  pair ∈ witness.interactionPairs ↔
    pair = witness.verifierPair ∨
      ∃ (table : Table F) (h : table ∈ witness.vmTables), ∃ row ∈ table.table,
      pair = (vm.channel.pulledIfValue (witness.rowEnabled h row) (witness.rowPull h row),
        vm.channel.pushedIfValue (witness.rowEnabled h row) (witness.rowPush h row)) := by
  simp [interactionPairs]
  tauto

noncomputable def pulls (witness : VmWitness ens vm fits) : List (Interaction F) :=
  witness.interactionPairs.map Prod.fst

noncomputable def pushes (witness : VmWitness ens vm fits) : List (Interaction F) :=
  witness.interactionPairs.map Prod.snd

lemma zip_pulls_pushes_eq_interactionPairs {witness : VmWitness ens vm fits} :
    List.zip witness.pulls witness.pushes = witness.interactionPairs := by
  simp only [pulls, pushes, List.zip_map_fst_snd]

lemma mem_pulls_iff {witness : VmWitness ens vm fits} {pull : Interaction F} :
  pull ∈ witness.pulls ↔
    pull = witness.verifierPair.1 ∨
      ∃ (table : Table F) (h : table ∈ witness.vmTables), ∃ row ∈ table.table,
      pull = vm.channel.pulledIfValue (witness.rowEnabled h row) (witness.rowPull h row) := by
  simp [pulls, interactionPairs]
  tauto

lemma mem_pushes_iff {witness : VmWitness ens vm fits} {push : Interaction F} :
  push ∈ witness.pushes ↔
    push = witness.verifierPair.2 ∨
      ∃ (table : Table F) (h : table ∈ witness.vmTables), ∃ row ∈ table.table,
      push = vm.channel.pushedIfValue (witness.rowEnabled h row) (witness.rowPush h row) := by
  simp [pushes, interactionPairs]
  tauto

def steps (witness : VmWitness ens vm fits) : ℕ :=
  witness.vmTables.map (·.length) |>.sum

@[circuit_norm]
lemma pulls_length {witness : VmWitness ens vm fits} :
    witness.pulls.length = witness.steps + 1 := by
  simp [steps, pulls, interactionPairs, vmTables, circuit_norm]

@[circuit_norm]
lemma pushes_length {witness : VmWitness ens vm fits} :
    witness.pushes.length = witness.steps + 1 := by
  simp [steps, pushes, interactionPairs, vmTables, circuit_norm]

lemma rowEnabled_isBool_of_vmConstraints {witness : VmWitness ens vm fits} :
    witness.VmConstraints →
    ∀ table (h : table ∈ witness.vmTables), ∀ row ∈ table.table,
      IsBool (witness.rowEnabled h row) := by
  intro constraints table table_mem row row_mem
  exact vm.step_enabled_isBool (witness.component_mem_tables_of_mem_vmTables table_mem) _
    (constraints table table_mem row row_mem)

lemma pulls_direction {witness : VmWitness ens vm fits} :
  witness.VmConstraints →
    ∀ pull ∈ witness.pulls, pull.direction = .pull ∧ IsBool pull.mult := by
  intro constraints pull h_pull
  rw [witness.mem_pulls_iff] at h_pull
  rcases h_pull with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [verifierPair, Channel.pulledValue, IsBool]
  · simp only [circuit_norm, true_and]
    apply witness.rowEnabled_isBool_of_vmConstraints constraints _ ‹_› _ ‹_›

lemma pushes_direction {witness : VmWitness ens vm fits} :
  witness.VmConstraints →
    ∀ push ∈ witness.pushes, push.direction = .push ∧ IsBool push.mult := by
  intro constraints push h_push
  rw [witness.mem_pushes_iff] at h_push
  rcases h_push with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [verifierPair, Channel.pushedValue, IsBool]
  · simp only [circuit_norm, true_and]
    apply witness.rowEnabled_isBool_of_vmConstraints constraints _ ‹_› _ ‹_›

lemma pulls_zero_iff_pushes_zero {witness : VmWitness ens vm fits} :
    ∀ i (hi : i < witness.pulls.length) (hi' : i < witness.pushes.length),
      witness.pulls[i].mult = 0 ↔ witness.pushes[i].mult = 0 := by
  intro i hi_p hi_q
  simp only [pulls, pushes, List.getElem_map]
  have hi : i < witness.interactionPairs.length := by
    simpa [pulls, interactionPairs] using hi_p
  have pair_mem : witness.interactionPairs[i]'hi ∈ witness.interactionPairs := List.getElem_mem _
  rw [mem_interactionPairs_iff] at pair_mem
  rcases pair_mem with hpair | ⟨table, table_mem, row, row_mem, hpair⟩
  · rw [hpair]
    simp [verifierPair, Channel.pulledValue, Channel.pushedValue]
  · rw [hpair]
    simp only [circuit_norm]

@[circuit_norm]
lemma pulls_channel {witness : VmWitness ens vm fits} :
    ∀ pull ∈ witness.pulls, pull.channel = vm.channel.toRaw := by
  intro pull h_pull
  rw [mem_pulls_iff] at h_pull
  rcases h_pull with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [verifierPair, Channel.pulledValue]
  · simp only [circuit_norm]

@[circuit_norm]
lemma pushes_channel {witness : VmWitness ens vm fits} :
    ∀ push ∈ witness.pushes, push.channel = vm.channel.toRaw := by
  intro push h_push
  rw [mem_pushes_iff] at h_push
  rcases h_push with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · simp [verifierPair, Channel.pushedValue]
  · simp only [circuit_norm]

lemma interactionss_eq_interactionPairs (witness : VmWitness ens vm fits) :
  [witness.verifierInteractionsWith vm.channel.toRaw] ++
      witness.vmTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    witness.interactionPairs.map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [witness.verifierInteractionsWith_eq]
  simp only [interactionPairs, List.flatMap_def, List.map_flatten, List.map_cons,
    List.singleton_append]
  congr 1
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ⟨ table, table_mem ⟩ _
  simp [Table.interactionssWith, witness.interactionValuesWith_eq table_mem]

lemma interactionss_eq_zip_pulls_pushes (witness : VmWitness ens vm fits) :
  [witness.verifierInteractionsWith vm.channel.toRaw] ++
      witness.vmTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [interactionss_eq_interactionPairs]
  simp [pulls, pushes, List.zip_map_fst_snd]

lemma vmInteractionsWith_eq_pulls_pushes (witness : VmWitness ens vm fits) :
  witness.vmInteractionsWith vm.channel.toRaw =
    (List.zip witness.pulls witness.pushes).flattenPairs := by
  have unfold_interactions : witness.vmInteractionsWith vm.channel.toRaw =
      ([witness.verifierInteractionsWith vm.channel.toRaw] ++
        witness.vmTables.flatMap
          (·.interactionssWith vm.channel.toRaw)).flatten := by
    simp only [vmInteractionsWith, Table.interactionsWith, Table.interactionssWith,
      List.singleton_append, List.flatten_cons]
    rw [List.flatMap_flatMap, List.flatMap_def]
  rw [unfold_interactions, interactionss_eq_zip_pulls_pushes, List.flattenPairs]

lemma mem_zip_pulls_pushes_iff (witness : VmWitness ens vm fits) (pull push : Interaction F) :
  (pull, push) ∈ List.zip witness.pulls witness.pushes ↔
    (pull, push) = witness.verifierPair ∨
      ∃ table ∈ witness.vmTables, ∃ row ∈ table.table,
        table.component.operations.interactionValuesWith vm.channel.toRaw
          (table.environment row) = [pull, push] := by
  rw [witness.zip_pulls_pushes_eq_interactionPairs,
    witness.mem_interactionPairs_iff]
  constructor
  · rintro (h_verifier | ⟨table, h_table, row, h_row, h_pair⟩)
    · exact Or.inl h_verifier
    · right
      refine ⟨table, h_table, row, h_row, ?_⟩
      rw [witness.interactionValuesWith_eq h_table]
      exact congrArg (fun pair => [pair.1, pair.2]) h_pair.symm
  · rintro (h_verifier | ⟨table, h_table, row, h_row, h_interactions⟩)
    · exact Or.inl h_verifier
    · right
      refine ⟨table, h_table, row, h_row, ?_⟩
      rw [witness.interactionValuesWith_eq h_table] at h_interactions
      simp only [List.cons.injEq, and_true] at h_interactions
      exact Prod.ext h_interactions.left.symm h_interactions.right.symm

lemma pulls_requirements_of_vmConstraints {witness : VmWitness ens vm fits} :
  witness.VmConstraints →
    ∀ pull ∈ witness.pulls, pull.Requirements witness.data := by
  intro constraints pull h_pull
  rw [witness.mem_pulls_iff] at h_pull
  rcases h_pull with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  · have verifier_requirements := vm.verifier_requirements
      (Environment.fromInput witness.publicInput witness.data)
    change (ens.addVm vm fits).VerifierChannelRequirements witness.publicInput witness.data
      vm.channel.toRaw at verifier_requirements
    rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements
    apply verifier_requirements
    rw [witness.verifierInteractionsWith_eq]
    simp
  · apply Channel.pulledIfValue_requirements_of_isBool_enabled
    apply witness.rowEnabled_isBool_of_vmConstraints constraints _ ‹_› _ ‹_›

lemma pushes_guarantees {witness : VmWitness ens vm fits} :
  ∀ push ∈ witness.pushes, push.Guarantees witness.data := by
  intro push h_push
  rw [witness.mem_pushes_iff] at h_push
  rcases h_push with rfl | ⟨table, table_mem, row, row_mem, rfl⟩
  <;> apply Channel.pushedIfValue_guarantees

lemma pulls_length_pos {witness : VmWitness ens vm fits} : witness.pulls.length > 0 := by
  simp [pulls_length]
lemma pushes_length_pos {witness : VmWitness ens vm fits} : witness.pushes.length > 0 := by
  simp [pushes_length]

lemma pulls_getElem_zero_eq (witness : VmWitness ens vm fits) :
    witness.pulls[0]'pulls_length_pos =
      vm.channel.pulledIfValue witness.verifierEnabled witness.verifierPull := by
  rw [witness.verifierEnabled_eq_one]
  rfl

lemma pushes_getElem_zero_eq (witness : VmWitness ens vm fits) :
    witness.pushes[0]'pushes_length_pos =
      vm.channel.pushedIfValue witness.verifierEnabled witness.verifierPush := by
  rw [witness.verifierEnabled_eq_one]
  rfl

lemma activeInteractions_pulls_length_pos {witness : VmWitness ens vm fits} :
    (activeInteractions witness.pulls).length > 0 := by
  simp_rw [activeInteractions, ←List.countP_eq_length_filter, List.countP_pos_iff]
  use witness.pulls[0]'pulls_length_pos, List.getElem_mem pulls_length_pos
  rw [witness.pulls_getElem_zero_eq]
  simp [circuit_norm, verifierEnabled_eq_one]

lemma activeInteractions_pushes_length_pos {witness : VmWitness ens vm fits} :
    (activeInteractions witness.pushes).length > 0 := by
  simp_rw [activeInteractions, ←List.countP_eq_length_filter, List.countP_pos_iff]
  use witness.pushes[0]'pushes_length_pos, List.getElem_mem pushes_length_pos
  rw [witness.pushes_getElem_zero_eq]
  simp [circuit_norm, verifierEnabled_eq_one]

lemma activeInteractions_pulls_getElem_zero_eq {witness : VmWitness ens vm fits} :
    (activeInteractions witness.pulls)[0]'activeInteractions_pulls_length_pos =
      vm.channel.pulledIfValue witness.verifierEnabled witness.verifierPull := by
  rw [witness.verifierEnabled_eq_one]
  simp [activeInteractions, pulls, interactionPairs, verifierPair,
    Channel.pulledValue, Channel.pulledIfValue]

lemma activeInteractions_pushes_getElem_zero_eq {witness : VmWitness ens vm fits} :
    (activeInteractions witness.pushes)[0]'activeInteractions_pushes_length_pos =
      vm.channel.pushedIfValue witness.verifierEnabled witness.verifierPush := by
  rw [witness.verifierEnabled_eq_one]
  simp [activeInteractions, pushes, interactionPairs, verifierPair,
    Channel.pushedValue, Channel.pushedIfValue]

/-- Translation of the VM soundness theorem to VmTables -/
theorem verifierChannelGuarantees_of_verifierChannelRequirements
  (witness : VmWitness ens vm fits) :
  -- if the vm interactions with the vm channel are balanced
  BalancedInteractions (witness.vmInteractionsWith vm.channel.toRaw) →
  witness.VmConstraints →
  -- and for every row, vm channel guarantees imply vm channel requirements
  -- (this will come from constraints + soundness of the existing ensemble)
  (∀ table ∈ witness.vmTables, ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees vm.channel.toRaw
      (table.environment row) →
    table.component.operations.ChannelRequirements vm.channel.toRaw
      (table.environment row)) →
  -- vm channel verifier requirements imply vm channel verifier guarantees
  (ens.addVm vm fits).VerifierChannelRequirements witness.publicInput witness.data
      vm.channel.toRaw →
    (ens.addVm vm fits).VerifierChannelGuarantees witness.publicInput witness.data
      vm.channel.toRaw := by
  intro balance witness_constraints constraints verifier_requirements
  have row_enabled_boolean := witness.rowEnabled_isBool_of_vmConstraints witness_constraints
  -- prove balance of pulls + pushes
  replace balance : BalancedInteractions (witness.pulls ++ witness.pushes) := by
    rw [witness.vmInteractionsWith_eq_pulls_pushes] at balance
    apply BalancedInteractions.of_perm balance
    apply List.zip_flattenPairs_perm <| witness.pushes_length ▸ witness.pulls_length.symm
  -- we fill in the conditions on pulls and pushes in `guarantees_of_requirements_of_requirements_of_guarantees`
  let n := (activeInteractions witness.pulls).length
  have same_length : witness.pulls.length = witness.pushes.length := by
    simp [pulls_length, pushes_length]
  have : (activeInteractions witness.pushes).length = n := by
    simp only [n, activeInteractions_length_eq same_length witness.pulls_zero_iff_pushes_zero]
  have grts_of_reqs := guarantees_of_requirements_of_requirements_of_guarantees_of_mult_zero_iff
    vm.channel.toRaw witness.pulls witness.pushes balance witness.data same_length
    witness.pulls_channel witness.pushes_channel
    (witness.pulls_direction witness_constraints) (witness.pushes_direction witness_constraints)
    witness.pulls_zero_iff_pushes_zero
  -- it remains to prove the (grts → reqs) assumption. this is a reformulation of our `constraints`
  have reqs_of_grts : (∀ i (hi : i < n),
      (activeInteractions witness.pulls)[i].Guarantees witness.data →
      (activeInteractions witness.pushes)[i].Requirements witness.data) := by
    suffices ∀ pair ∈ (witness.pulls.zip witness.pushes), pair.1.Guarantees witness.data → pair.2.Requirements witness.data by
      intro i hi
      exact this _ (activePair_mem_zip same_length witness.pulls_zero_iff_pushes_zero _ hi)
    intro (pull, push) pair_mem
    simp only
    have ⟨ mem_pull, mem_push ⟩ := List.of_mem_zip pair_mem
    have push_grts := witness.pushes_guarantees push mem_push
    have pull_reqs := witness.pulls_requirements_of_vmConstraints witness_constraints pull mem_pull
    rw [witness.mem_zip_pulls_pushes_iff] at pair_mem
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
      rw [witness.verifierInteractionsWith_eq]
      simp
    · suffices (∀ i ∈ [pull, push], i.Guarantees witness.data) →
          (∀ i ∈ [pull, push], i.Requirements witness.data) by
        simp_all
      rw [← interactions_eq, Operations.interactionValuesWith_eq_map,
        List.forall_mem_map, List.forall_mem_map]
      simp only [Operations.forall_interactionsWith_iff]
      rw [show witness.data = table.data from
        (witness.same_data table (List.mem_of_mem_take table_mem)).symm]
      exact constraints table table_mem row row_mem
  -- to get the conclusion about the verifier, we specialize to index 0
  specialize grts_of_reqs reqs_of_grts 0 activeInteractions_pulls_length_pos
  rw [witness.activeInteractions_pulls_getElem_zero_eq,
    witness.activeInteractions_pushes_getElem_zero_eq] at grts_of_reqs
  have verifier_requirements' := verifier_requirements
  rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements'
  have push_requirements :
      (vm.channel.pushedIfValue witness.verifierEnabled witness.verifierPush).Requirements
        witness.data := by
    apply verifier_requirements'
    rw [witness.verifierInteractionsWith_eq, witness.verifierEnabled_eq_one]
    simp [verifierPair, Channel.pushedIfValue, Channel.pushedValue]
  specialize grts_of_reqs push_requirements
  rw [witness.verifierEnabled_eq_one] at grts_of_reqs
  rw [witness.verifierChannelGuarantees_iff_forall]
  intro interaction h_interaction
  rw [witness.verifierInteractionsWith_eq] at h_interaction
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_interaction
  rcases h_interaction with rfl | rfl
  · simpa [verifierPair, Channel.pulledIfValue, Channel.pulledValue] using grts_of_reqs
  · apply Channel.pushedIfValue_guarantees
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

theorem addVm_soundVmChannel_of_soundChannels (ens : Ensemble F PublicIO)
      -- given a sound channels ensemble with a list of finished, consistent channels
    {finished : List (RawChannel F)} (soundChannels : ens.SoundChannels finished)
    (consistent : ∀ channel ∈ finished, channel.Consistent)
    (finished_subset : finished ⊆ ens.channels)
    -- and given a VM channel + tables + verifier
    (vm : VmTables F PublicIO)
    (fits : vm.FitsInto ens) :
    -- assuming that none of the existing tables interacted with the VM channel
    (∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) →
    -- assuming that the VM tables' and verifier's channelsWithGuarantees are either finished or the VM channel
    (vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished) →
    -- and assuming the VM tables' channelsWithRequirements contain none of the finished ones
    (∀ channel ∈ finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the VM tables satisfies SoundVmChannel
    (ens.addVm vm fits).SoundVmChannel := by
  intro not_mem_vm_channel grts_subset reqs_disjoint (witness : VmWitness ens vm fits) assumptions
    constraints balance
  /-
  the high level plan is to apply
  `verifier_guarantees_of_requirements_of_requirements_of_guarantees`.

  1) we need to narrow vm channel balance to just the vm tables
  2) guarantees for finished channels follows from soundChannels + constraints, using
     `spec_and_guarantees_of_soundChannels` and `guarantees_of_requirements_append`
     as the key lemmas.
  3) the combination of guarantees for finished channels + vm constraints gives us the main condition:
     "vm guarantees → vm requirements", by invoking `requirements_of_partial_guarantees_of_constraints`.
  4) finally, `VmTables.verifier_requirements` gives us the unconditional requirements for the
     verifier, from which the conclusion follows.
  -/
  -- the vm channel interactions are constrained to vm tables, which lets us supply the balance
  -- condition
  have vm_balance := balance vm.channel.toRaw (by simp [Ensemble.addVm])
  simp only [circuit_norm] at vm_balance
  rw [witness.interactionsWith_eq_vmInteractionsWith not_mem_vm_channel] at vm_balance
  set vmChannel := vm.channel.toRaw
  -- next, we work on instantiating `requirements_of_partial_guarantees_of_constraints`
  -- which will give us exactly the second hypothesis of `verifier_guarantees`
  -- first, unify channel subset assumptions to all tables
  have grts_subset_all : ∀ table ∈ witness.vmTables,
      table.channelsWithGuarantees ⊆ vmChannel :: finished := by
    intro table h_table
    exact grts_subset.2 table.component (witness.component_mem_tables_of_mem_vmTables h_table)
  have vm_reqs_disjoint : ∀ channel ∈ finished, ∀ table ∈ witness.vmTables,
      channel ∉ table.channelsWithRequirements := by
    intro channel channel_mem table table_mem
    exact (reqs_disjoint channel channel_mem).2 _
      (witness.component_mem_tables_of_mem_vmTables table_mem)
  have vm_constraints := witness.vmConstraints_of_constraints constraints
  -- establish partial balance + specialize to old ensemble
  have ordered_finished : ∀ channel ∈ finished,
      (ens.addVm vm fits).OrderedChannel channel := by
    intro channel channel_mem
    have ordered := (soundChannels.right.left channel channel_mem).right.left
    have no_requirements := reqs_disjoint channel channel_mem
    clear * - ordered no_requirements
    simp_all [circuit_norm, orderedChannel_of_no_requirements, orderedChannelLt_of_no_requirements]
  have partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel witness.toTables channel := by
    intro channel channel_mem
    apply Ensemble.partialBalancedChannel_of_balancedChannel
    · exact ordered_finished channel channel_mem
    · exact balance channel (by simp [Ensemble.addVm, finished_subset channel_mem])
  have old_partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel witness.oldContext channel := by
    intro channel channel_mem
    apply partialBalancedChannel_of_sublist (partial_balance _ channel_mem)
    exact ⟨witness.vmContext.tables, witness.toTables_perm, vm_constraints,
      vm_reqs_disjoint _ channel_mem⟩
  -- invoke old tables soundness to get reqs for finished channels from constraints
  have finished_reqs : ∀ channel ∈ finished, ∀ table ∈ witness.oldContext.tables,
      table.ChannelRequirements channel := by
    intro channel channel_mem table table_mem
    refine spec_and_guarantees_of_soundChannels (witness := witness.oldContext) ?_
      (witness.oldContext_assumptions_of_assumptions assumptions)
      (witness.oldContext_constraints_of_constraints constraints) old_partial_balance
      table table_mem
      |>.right channel channel_mem |>.right
    have old_sound_channels : _root_.SoundChannels ens.tables finished := ⟨
      ens.channelsWithGuarantees_subset_iff.mp soundChannels.left |>.right,
      fun channel h_channel => (soundChannels.right.left channel h_channel).right.left,
      soundChannels.right.right⟩
    simpa only [VmWitness.oldContext, witness.oldTables_map_component] using old_sound_channels
  -- invoke `guarantees_of_requirements_append` to get grts for finished channels in vm tables
  have finished_grts : ∀ table ∈ witness.vmTables, ∀ channel ∈ finished,
      table.ChannelGuarantees channel := by
    intro table table_mem channel channel_mem
    have : channel.Consistent := consistent channel channel_mem
    apply guarantees_of_requirements_append (ts := witness.vmContext) (ss := witness.oldContext) rfl
      vm_constraints (vm_reqs_disjoint _ channel_mem)
      (witness.vmContext_append_oldContext ▸ partial_balance _ channel_mem)
      (finished_reqs _ channel_mem)
      _ table_mem
  -- invoke `requirements_of_partial_guarantees_of_constraints` to get per-row grts → reqs for the vm channel,
  -- and use it in `verifier_guarantees`
  have reqs_of_grts (table) (h_table : table ∈ witness.vmTables) :=
    table.requirements_of_partial_guarantees_of_constraints (unfinished := vmChannel)
    (witness.vmContext_assumptions_of_assumptions assumptions table h_table)
    (vm_constraints table h_table)
    (grts_subset_all table h_table) (finished_grts table h_table)
  have vm_verifier_guarantees :=
    witness.verifierChannelGuarantees_of_verifierChannelRequirements vm_balance vm_constraints
      reqs_of_grts
      (vm.verifier_requirements (Environment.fromInput witness.publicInput witness.data))
  have finished_verifier_guarantees : ∀ channel ∈ finished,
      (ens.addVm vm fits).VerifierChannelGuarantees witness.publicInput witness.data channel := by
    intro channel channel_mem
    let : channel.Consistent := consistent channel channel_mem
    apply Ensemble.verifierChannelGuarantees_of_tableRequirements
    · exact .inr (reqs_disjoint channel channel_mem).1
    · exact balance channel (by simp [Ensemble.addVm, finished_subset channel_mem])
    intro table h_table
    by_cases h_vm : table ∈ witness.vmTables
    · exact table.requirements_of_not_mem_of_constraints (vm_constraints table h_vm)
        (vm_reqs_disjoint channel channel_mem table h_vm)
    · exact finished_reqs channel channel_mem table
        (witness.mem_oldTables_of_not_mem_vmTables h_table h_vm)
  rw [Ensemble.verifierGuarantees_iff]
  intro channel h_channel
  rcases List.mem_cons.mp (grts_subset.1 h_channel) with rfl | h_finished
  · exact vm_verifier_guarantees
  · exact finished_verifier_guarantees channel h_finished
end Ensemble

namespace SoundEnsemble

/-- A VM's tables and verifier fit into a sound ensemble whose channels they use: their guarantees
come from finished channels or the VM channel, and their requirements go to the VM channel or to
channels of the ensemble that aren't finished. -/
theorem vmFitsInto (ens : SoundEnsemble F PublicIO) (vm : VmTables F PublicIO)
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

/-- Add a VM on top of a sound ensemble, see `vmFitsInto` for the conditions on its channels. -/
def addVm (ens : SoundEnsemble F PublicIO) (vm : VmTables F PublicIO)
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
    SoundVmEnsemble F PublicIO where
  __ := ens.ensemble.addVm vm
    (ens.vmFitsInto vm fresh_channel grts_subset_finished reqs_unfinished names)
  soundVmChannel := ens.ensemble.addVm_soundVmChannel_of_soundChannels
    ens.soundChannels ens.finished_consistent ens.finished_subset vm
    (ens.vmFitsInto vm fresh_channel grts_subset_finished reqs_unfinished names)
    (fun table h_table h_mem =>
      fresh_channel (List.mem_map.mpr ⟨_, ens.tables_channels table h_table h_mem, rfl⟩))
    grts_subset_finished
    (fun channel h_finished =>
      ⟨fun h => (reqs_unfinished.1 channel h).2 h_finished,
        fun table h_table h => (reqs_unfinished.2 table h_table channel h).2 h_finished⟩)

variable {soundEns : SoundEnsemble F PublicIO} {vm : VmTables F PublicIO}
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
@[circuit_norm] lemma addVm_ensemble :
  (soundEns.addVm vm fresh gsf reqs names).ensemble = soundEns.ensemble.addVm vm
    (soundEns.vmFitsInto vm fresh gsf reqs names) := rfl

end SoundEnsemble
end Air.Flat
