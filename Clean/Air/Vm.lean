import Clean.Air.FlatEnsemble
import Clean.Air.OrderedChannel

variable {F : Type} [FiniteField F] [DecidableEq F]
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

structure VmTables (F : Type) [FiniteField F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : Channel F Message

  tables : List (Component F)
  unique_names : (tables.map (·.circuit.name)).Nodup
  verifier : GeneralFormalCircuit F PublicIO unit
  verifier_length_zero : ∀ pi, (verifier pi).localLength 0 = 0 := by
    simp only [circuit_norm]

  tables_channel : tables.Forall fun table =>
    ∃ enabled : Expression F, ∃ pull push : Var Message F,
      ⟨ channel, [(channel.pulledIf enabled pull).toRaw, (channel.pushedIf enabled push).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      ∀ env, ConstraintsHold.Shallow env table.rowOperations →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1

  -- the verifier pulls and pushes to the channel, and doesn't push anything else
  verifier_channel : ∃ m1 m2, ⟨ channel, [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw] ⟩ ∈
    verifier.exposedChannels (varFromOffset PublicIO 0) (size PublicIO)

  -- verifier requirements follow _unconditionally_ from constraints (without relying on guarantees)
  -- essentially a modified soundness theorem for the verifier
  verifier_requirements :
    let offset := size PublicIO;
    let input_var := varFromOffset PublicIO 0;
    ∀ env,
      Operations.ConstraintsHold env (verifier.main input_var |>.operations offset) →
      Operations.ChannelRequirements channel env (verifier.main input_var |>.operations offset)

instance (vm : VmTables F PublicIO) : ProvableType vm.Message := vm.provableMessage

def VmTables.toEnsemble (vm : VmTables F PublicIO) : Ensemble F PublicIO where
  channels := [vm.channel.toRaw]
  tables := vm.tables
  unique_names := vm.unique_names
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

/--
Soundness for a VM ensemble is simple:
- the ensemble spec is just the verifier spec
- the verifier spec can be proven from constraints + balance for all tables/channels
-/
def Ensemble.SoundVmChannel (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.BalancedChannels →
      ens.VerifierGuarantees witness.publicInput witness.data

structure SoundVmEnsemble (F : Type) [FiniteField F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO]
    extends ensemble : Ensemble F PublicIO where
  soundVmChannel : ensemble.SoundVmChannel

namespace SoundVmEnsemble
def toFormal (F : Type) [FiniteField F] [DecidableEq F] (ens : SoundVmEnsemble F PublicIO)
  -- TODO is this useful in practice? Right now, tables don't have access to public input so that's weird
  (ExtraAssumptions : PublicIO F → ProverData F → Prop)
  (extraAssumptionsConsistency : ∀ publicInput data, ExtraAssumptions publicInput data →
    ∀ table ∈ ens.ensemble.tables, ∀ input, table.Assumptions input data) :
    FormalEnsemble F PublicIO where
  ensemble := ens.ensemble
  Assumptions publicInput := ∀ data,
    ens.verifier.Assumptions publicInput data ∧
    ExtraAssumptions publicInput data
  Spec publicInput := ∃ data, ens.VerifierSpec publicInput data
  soundness := by
    simp only [Ensemble.Soundness, Ensemble.Statement]
    intro input assumptions ⟨witness, input_eq, constraints, balance⟩
    use witness.data
    obtain ⟨verifier_assumptions, extra_assumptions⟩ := assumptions witness.data
    simp only [← input_eq, circuit_norm] at *
    have soundVm := ens.soundVmChannel witness ?assumptions constraints balance
    convert (ens.verifier.original_full_soundness _ _ _ ?_ ?_ soundVm).1
    · rw [ProvableType.eval_fromInput_varFromOffset_zero]
    · rw [ProvableType.eval_fromInput_varFromOffset_zero]
      exact verifier_assumptions
    · exact EnsembleWitness.verifierConstraints_of_constraints constraints
    simp only [EnsembleWitness.Assumptions]
    rw [EnsembleWitness.forall_mem_allTables_iff,
      ← EnsembleWitness.verifierAssumptions_iff_verifierTable_assumptions]
    use verifier_assumptions
    intro table h_table row h_row
    simp only [Component.RowAssumptions]
    have hcomponent := EnsembleWitness.mem_tables_component_of_mem_tables h_table
    have hresidual := extraAssumptionsConsistency witness.publicInput witness.data
      extra_assumptions table.component hcomponent
        (table.component.rowInput (Environment.fromArray row witness.data))
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
    ∀ data, ens.ensemble.verifier.Assumptions publicInput data ∧ ExtraAssumptions publicInput data := by
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
omit [DecidableEq F] in
/-- Ensemble interactions preserving the per-row structure until the final flatten. -/
lemma EnsembleWitness.flatMap_interactionsWith_eq_flatten {ens : Ensemble F PublicIO}
  (witness : EnsembleWitness ens) {channel : RawChannel F} :
  witness.interactionsWith channel =
    (witness.allTables.flatMap (·.interactionssWith witness.data channel)).flatten := by
  simp only [EnsembleWitness.interactionsWith, Table.interactionsWith, Table.interactionssWith]
  rw [List.flatMap_flatMap, List.flatMap_def]

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

@[circuit_norm] abbrev allTables (vm : VmTables F PublicIO) : List (Component F) :=
  vm.toEnsemble.allTables

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
  ⟨ vm.channel,
    [(vm.channel.pulled vm.verifierPull).toRaw,
      (vm.channel.pushed vm.verifierPush).toRaw] ⟩ ∈
    vm.verifier.exposedChannels (varFromOffset PublicIO 0) (size PublicIO) :=
  vm.verifier_channel.choose_spec.choose_spec

noncomputable def verifierStep (vm : VmTables F PublicIO) : VmStep vm.Message F where
  enabled := 1
  pull := vm.verifierPull
  push := vm.verifierPush

open Classical in noncomputable
def step (vm : VmTables F PublicIO) {table : Component F}
    (h_mem : table ∈ vm.allTables) : VmStep vm.Message F :=
  if h : table = vm.toEnsemble.verifierTable
  then vm.verifierStep
  else vm.tableStep (List.mem_of_ne_of_mem h h_mem)

theorem allTables_channel (vm : VmTables F PublicIO) : ∀ (table) (table_mem : table ∈ vm.allTables),
  let step := vm.step table_mem
  ⟨ vm.channel,
    [(vm.channel.pulledIf step.enabled step.pull).toRaw,
      (vm.channel.pushedIf step.enabled step.push).toRaw] ⟩ ∈ table.exposedChannels := by
  intro table table_mem
  simp only [circuit_norm, Ensemble.allTables] at table_mem ⊢
  by_cases h : table = vm.toEnsemble.verifierTable
  · subst table
    simp only [circuit_norm, step, reduceDIte]
    exact vm.verifier_channel'
  · simp only [circuit_norm, step, h, reduceDIte] at ⊢ table_mem
    exact vm.tables_channel' table_mem

lemma interactionsWith_eq {vm : VmTables F PublicIO} {table} (_ : table ∈ vm.allTables) :
  table.operations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf (vm.step ‹_›).enabled (vm.step ‹_›).pull).toRaw,
    (vm.channel.pushedIf (vm.step ‹_›).enabled (vm.step ‹_›).push).toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  apply vm.allTables_channel

lemma verifierInteractionsWith_eq {vm : VmTables F PublicIO} :
  vm.toEnsemble.verifierTable.operations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf vm.verifierStep.enabled vm.verifierStep.pull).toRaw,
    (vm.channel.pushedIf vm.verifierStep.enabled vm.verifierStep.push).toRaw ] := by
  simpa only [step, reduceDIte] using interactionsWith_eq Ensemble.mem_allTables_verifierTable
end VmTables

namespace Ensemble

def addVm (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
    (unique_names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup) : Ensemble F PublicIO where
  channels := vm.channel :: ens.channels
  tables := vm.tables ++ ens.tables
  unique_names
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

@[circuit_norm] lemma addVm_channels (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (names) :
  (ens.addVm vm names).channels = vm.channel.toRaw :: ens.channels := rfl
@[circuit_norm] lemma addVm_tables (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (names) :
  (ens.addVm vm names).tables = vm.tables ++ ens.tables := rfl
@[circuit_norm] lemma addVm_verifier (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (names) :
  (ens.addVm vm names).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_verifierTable (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) (names) :
  (ens.addVm vm names).verifierTable = vm.toEnsemble.verifierTable := rfl

end Ensemble

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO} {vm : VmTables F PublicIO}
  {names : ((vm.tables ++ ens.tables).map (·.circuit.name)).Nodup}

abbrev vmTables (witness : EnsembleWitness (ens.addVm vm names)) : List (Table F) :=
  witness.tables.take vm.tables.length

def vmAllTables (witness : EnsembleWitness (ens.addVm vm names)) : List (Table F) :=
  vm.toEnsemble.verifierWitnessTable witness.publicInput ::
    witness.tables.take vm.tables.length

lemma vmVerifierTable_eq (witness : EnsembleWitness (ens.addVm vm names)) :
    witness.verifierTable = vm.toEnsemble.verifierWitnessTable witness.publicInput := by
  simp [EnsembleWitness.verifierTable, Ensemble.verifierWitnessTable,
    Ensemble.addVm, VmTables.toEnsemble]

def VmConstraints (witness : EnsembleWitness (ens.addVm vm names)) : Prop :=
  ∀ table ∈ witness.vmAllTables, table.Constraints witness.data

noncomputable def vmInteractionsWith (witness : EnsembleWitness (ens.addVm vm names))
    (channel : RawChannel F) : List (Interaction F) :=
  witness.vmAllTables.flatMap (·.interactionsWith witness.data channel)

lemma vmMemAllTablesComponent
    {witness : EnsembleWitness (ens.addVm vm names)} {table : Table F} :
    table ∈ witness.vmAllTables → table.component ∈ vm.allTables := by
  intro htable
  simp only [vmAllTables, List.mem_cons] at htable
  rcases htable with rfl | htable
  · change vm.toEnsemble.verifierTable ∈ vm.allTables
    exact Ensemble.mem_allTables_verifierTable
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htable
  have hi_vm : i < vm.tables.length := by
    have := hi
    simp [List.length_take] at this
    omega
  have hi_full : i < (ens.addVm vm names).tables.length := by
    simp [Ensemble.addVm]
    omega
  have component_eq := witness.same_circuits i hi_full
  rw [List.getElem_take]
  rw [← component_eq]
  apply Ensemble.mem_allTables_of_mem_tables
  convert List.getElem_mem hi_vm using 1 <;>
    simp [Ensemble.addVm, VmTables.toEnsemble, hi_vm]

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

noncomputable def vmRowEnabled (witness : EnsembleWitness (ens.addVm vm names)) {table} (_ : table ∈ witness.vmAllTables) (row : Array F) : F :=
  (Environment.fromArray row witness.data)
    (vm.step (witness.vmMemAllTablesComponent ‹_›)).enabled

noncomputable def vmRowPull (witness : EnsembleWitness (ens.addVm vm names)) {table} (_ : table ∈ witness.vmAllTables) (row : Array F) : vm.Message F :=
  eval (Environment.fromArray row witness.data)
    (vm.step (witness.vmMemAllTablesComponent ‹_›)).pull

noncomputable def vmRowPush (witness : EnsembleWitness (ens.addVm vm names)) {table} (_ : table ∈ witness.vmAllTables) (row : Array F) : vm.Message F :=
  eval (Environment.fromArray row witness.data)
    (vm.step (witness.vmMemAllTablesComponent ‹_›)).push

noncomputable def vmVerifierEnabled (witness : EnsembleWitness (ens.addVm vm names)) : F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.enabled

lemma vmVerifierEnabled_eq_one (witness : EnsembleWitness (ens.addVm vm names)) : witness.vmVerifierEnabled = 1 := by
  simp only [vmVerifierEnabled, VmTables.verifierStep, circuit_norm]

noncomputable def vmVerifierPull (witness : EnsembleWitness (ens.addVm vm names)) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.pull

noncomputable def vmVerifierPush (witness : EnsembleWitness (ens.addVm vm names)) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.push

lemma vmInteractionValuesWith_eq (witness : EnsembleWitness (ens.addVm vm names))
    {table} (_ : table ∈ witness.vmAllTables) (row : Array F) :
  table.component.operations.interactionValuesWith vm.channel.toRaw
      (Environment.fromArray row witness.data) = [
    vm.channel.pulledIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPull ‹_› row),
    vm.channel.pushedIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPush ‹_› row) ] := by
  simp only [circuit_norm, vm.interactionsWith_eq (witness.vmMemAllTablesComponent ‹_›),
    vmRowEnabled, vmRowPull, vmRowPush, AbstractInteraction.eval, ProvableType.toElements_eval]

lemma vmInteractionValuesWith_length (witness : EnsembleWitness (ens.addVm vm names))
    {table} (_ : table ∈ witness.vmAllTables) (row : Array F) :
  (table.component.operations.interactionValuesWith vm.channel.toRaw
    (Environment.fromArray row witness.data)).length = 2 := by
  simp [witness.vmInteractionValuesWith_eq ‹_› row]

noncomputable def vmInteractionPairs (witness : EnsembleWitness (ens.addVm vm names)) : List (Interaction F × Interaction F) :=
  witness.vmAllTables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row =>
      (vm.channel.pulledIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPull ‹_› row),
        vm.channel.pushedIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPush ‹_› row))

lemma mem_vmInteractionPairs_iff {witness : EnsembleWitness (ens.addVm vm names)} {pair : Interaction F × Interaction F} :
  pair ∈ witness.vmInteractionPairs ↔
    ∃ (table : Table F) (_ : table ∈ witness.vmAllTables), ∃ row ∈ table.table,
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
    ∃ (table : Table F) (_ : table ∈ witness.vmAllTables), ∃ row ∈ table.table,
    pull = vm.channel.pulledIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPull ‹_› row) := by
  simp [vmPulls, vmInteractionPairs]
  tauto

lemma mem_vmPushes_iff {witness : EnsembleWitness (ens.addVm vm names)} {push : Interaction F} :
  push ∈ witness.vmPushes ↔
    ∃ (table : Table F) (_ : table ∈ witness.vmAllTables), ∃ row ∈ table.table,
    push = vm.channel.pushedIfValue (witness.vmRowEnabled ‹_› row) (witness.vmRowPush ‹_› row) := by
  simp [vmPushes, vmInteractionPairs]
  tauto

def vmSteps (witness : EnsembleWitness (ens.addVm vm names)) : ℕ :=
  witness.vmTables.map (·.length) |>.sum

@[circuit_norm]
lemma vmPulls_length {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPulls.length = witness.vmSteps + 1 := by
  simp [vmSteps, vmPulls, vmInteractionPairs, vmAllTables, vmTables,
    VmTables.toEnsemble, circuit_norm]

@[circuit_norm]
lemma vmPushes_length {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPushes.length = witness.vmSteps + 1 := by
  simp [vmSteps, vmPushes, vmInteractionPairs, vmAllTables, vmTables,
    VmTables.toEnsemble, circuit_norm]

lemma vmRowEnabled_isBool_of_constraints {witness : EnsembleWitness (ens.addVm vm names)} :
    witness.VmConstraints →
    ∀ table (_ : table ∈ witness.vmAllTables), ∀ row ∈ table.table,
      IsBool (witness.vmRowEnabled ‹_› row) := by
  intro constraints table table_mem row row_mem
  simp only [circuit_norm, vmRowEnabled, VmTables.step, VmTables.verifierStep]
  by_cases h_verifier : table.component = vm.toEnsemble.verifierTable
  · simp [circuit_norm, h_verifier]
  have component_mem : table.component ∈ vm.tables := by
    have h_mem := witness.vmMemAllTablesComponent table_mem
    simp only [circuit_norm, Ensemble.allTables, List.mem_cons] at h_mem
    exact h_mem.resolve_left h_verifier
  have h_constraints := constraints table table_mem row row_mem
  simp only [h_verifier, reduceDIte]
  exact vm.tableStep_enabled_isBool component_mem _ h_constraints

lemma vmPulls_mult {witness : EnsembleWitness (ens.addVm vm names)} :
  witness.VmConstraints →
    ∀ pull ∈ witness.vmPulls, pull.mult = 0 ∨ pull.mult = -1 := by
  simp_rw [witness.mem_vmPulls_iff]
  rintro constraints pull ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm, neg_inj]
  apply witness.vmRowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›

lemma vmPushes_mult {witness : EnsembleWitness (ens.addVm vm names)} :
  witness.VmConstraints →
    ∀ push ∈ witness.vmPushes, push.mult = 0 ∨ push.mult = 1 := by
  simp_rw [witness.mem_vmPushes_iff]
  rintro constraints push ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm]
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
  rcases pair_mem with ⟨ pair, pair_mem, table, table_mem, hpair ⟩
  rw [hpair]
  simp only [circuit_norm]

@[circuit_norm]
lemma vmPulls_channel {witness : EnsembleWitness (ens.addVm vm names)} : ∀ pull ∈ witness.vmPulls, pull.channel = vm.channel.toRaw := by
  simp_rw [mem_vmPulls_iff]
  rintro pull ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm]

@[circuit_norm]
lemma vmPushes_channel {witness : EnsembleWitness (ens.addVm vm names)} : ∀ push ∈ witness.vmPushes, push.channel = vm.channel.toRaw := by
  simp_rw [mem_vmPushes_iff]
  rintro push ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm]

lemma vmInteractionss_eq_interactionPairs (witness : EnsembleWitness (ens.addVm vm names)) :
  witness.vmAllTables.flatMap (·.interactionssWith witness.data vm.channel.toRaw) =
    witness.vmInteractionPairs.map (fun ⟨pull, push⟩ => [pull, push]) := by
  simp only [vmInteractionPairs, List.flatMap_def, List.map_flatten]
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ⟨ table, table_mem ⟩ _
  simp [Table.interactionssWith, witness.vmInteractionValuesWith_eq table_mem]

lemma vmInteractionss_eq_pulls_pushes (witness : EnsembleWitness (ens.addVm vm names)) :
  witness.vmAllTables.flatMap (·.interactionssWith witness.data vm.channel.toRaw) =
    (List.zip witness.vmPulls witness.vmPushes).map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [vmInteractionss_eq_interactionPairs]
  simp [vmPulls, vmPushes, List.zip_map_fst_snd]

lemma vmInteractions_eq_pulls_pushes (witness : EnsembleWitness (ens.addVm vm names)) :
  witness.vmInteractionsWith vm.channel.toRaw =
    (List.zip witness.vmPulls witness.vmPushes).flattenPairs := by
  have unfold_interactions : witness.vmInteractionsWith vm.channel.toRaw =
      (witness.vmAllTables.flatMap
        (·.interactionssWith witness.data vm.channel.toRaw)).flatten := by
    simp only [vmInteractionsWith, Table.interactionsWith, Table.interactionssWith]
    rw [List.flatMap_flatMap, List.flatMap_def]
  rw [unfold_interactions, vmInteractionss_eq_pulls_pushes, List.flattenPairs]

lemma vmMem_zip_pulls_pushes_iff (witness : EnsembleWitness (ens.addVm vm names)) (pull push : Interaction F) :
  (pull, push) ∈ List.zip witness.vmPulls witness.vmPushes ↔
    ∃ table ∈ witness.vmAllTables, ∃ row ∈ table.table,
      table.component.operations.interactionValuesWith vm.channel.toRaw
        (Environment.fromArray row witness.data) = [pull, push] := by
  trans [pull, push] ∈ (List.zip witness.vmPulls witness.vmPushes).map (fun ⟨pull, push⟩ => [pull, push])
  · simp
  simp [← vmInteractionss_eq_pulls_pushes, Table.interactionssWith]

lemma vmPullRequirementsOfConstraints {witness : EnsembleWitness (ens.addVm vm names)} :
  witness.VmConstraints →
    ∀ pull ∈ witness.vmPulls, pull.Requirements witness.data := by
  intro constraints
  simp_rw [witness.mem_vmPulls_iff]
  rintro pull ⟨ table, table_mem, row, row_mem, rfl ⟩
  apply Channel.pulledIfValue_requirements_of_isBool_enabled
  apply witness.vmRowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›

lemma vmPushGuarantees {witness : EnsembleWitness (ens.addVm vm names)} :
  ∀ push ∈ witness.vmPushes, push.Guarantees witness.data := by
  simp_rw [witness.mem_vmPushes_iff]
  rintro push ⟨ table, table_mem, row, row_mem, rfl ⟩
  apply Channel.pushedIfValue_guarantees

lemma vmPulls_length_pos {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPulls.length > 0 := by
  simp [vmPulls_length]
lemma vmPushes_length_pos {witness : EnsembleWitness (ens.addVm vm names)} : witness.vmPushes.length > 0 := by
  simp [vmPushes_length]

lemma vmPulls_getElem_zero_eq (witness : EnsembleWitness (ens.addVm vm names)) :
    witness.vmPulls[0]'vmPulls_length_pos =
      vm.channel.pulledIfValue witness.vmVerifierEnabled witness.vmVerifierPull := by
  simp [vmPulls, vmInteractionPairs, vmAllTables, circuit_norm, vmRowEnabled, vmRowPull,
    vmVerifierPull, vmVerifierEnabled, VmTables.step, VmTables.verifierStep,
    VmTables.toEnsemble,
    Environment.fromInput, Environment.fromArray]

lemma vmPushes_getElem_zero_eq (witness : EnsembleWitness (ens.addVm vm names)) :
    witness.vmPushes[0]'vmPushes_length_pos =
      vm.channel.pushedIfValue witness.vmVerifierEnabled witness.vmVerifierPush := by
  simp [vmPushes, vmInteractionPairs, vmAllTables, circuit_norm, vmRowEnabled, vmRowPush,
    vmVerifierPush, vmVerifierEnabled, VmTables.step, VmTables.verifierStep,
    VmTables.toEnsemble,
    Environment.fromInput, Environment.fromArray]

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
  simp [activeInteractions, vmPulls, vmInteractionPairs, vmAllTables, circuit_norm, vmRowEnabled, vmRowPull,
    vmVerifierPull, vmVerifierEnabled, VmTables.step, VmTables.verifierStep,
    VmTables.toEnsemble,
    Environment.fromInput, Environment.fromArray]

lemma activeInteractions_vmPushes_getElem_zero_eq {witness : EnsembleWitness (ens.addVm vm names)} :
    (activeInteractions witness.vmPushes)[0]'activeInteractions_vmPushes_length_pos =
      vm.channel.pushedIfValue witness.vmVerifierEnabled witness.vmVerifierPush := by
  simp [activeInteractions, vmPushes, vmInteractionPairs, vmAllTables, circuit_norm, vmRowEnabled, vmRowPush,
    vmVerifierPush, vmVerifierEnabled, VmTables.step, VmTables.verifierStep,
    VmTables.toEnsemble,
    Environment.fromInput, Environment.fromArray]

/-- Translation of the VM soundness theorem to VmTables -/
theorem vmVerifierGuarantees
  [Fact (ringChar F ≠ 2)] (witness : EnsembleWitness (ens.addVm vm names)) :
  -- if the vm interactions with the vm channel are balanced
  BalancedInteractions (witness.vmInteractionsWith vm.channel.toRaw) →
  witness.VmConstraints →
  -- and for every row, vm channel guarantees imply vm channel requirements
  -- (this will come from constraints + soundness of the existing ensemble)
  (∀ table ∈ witness.vmAllTables, ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees vm.channel.toRaw
      (Environment.fromArray row witness.data) →
    table.component.operations.ChannelRequirements vm.channel.toRaw
      (Environment.fromArray row witness.data)) →
  -- vm channel verifier requirements imply vm channel verifier guarantees
  witness.verifierTable.ChannelRequirements witness.data vm.channel.toRaw →
    witness.verifierTable.ChannelGuarantees witness.data vm.channel.toRaw := by
  intro balance witness_constraints constraints
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
    obtain ⟨ table, table_mem, row, row_mem, interactions_eq ⟩ := pair_mem
    suffices (∀ i ∈ [pull, push], i.Guarantees witness.data) → (∀ i ∈ [pull, push], i.Requirements witness.data) by
      simp_all
    rw [← interactions_eq, Operations.interactionValuesWith_eq_map, List.forall_mem_map, List.forall_mem_map]
    simp only [Operations.forall_interactionsWith_iff]
    exact constraints table table_mem row row_mem
  -- to get the conclusion about the verifier, we specialize to index 0
  specialize grts_of_reqs reqs_of_grts 0 activeInteractions_vmPulls_length_pos
  rw [witness.activeInteractions_vmPulls_getElem_zero_eq,
    witness.activeInteractions_vmPushes_getElem_zero_eq] at grts_of_reqs
  simp only [EnsembleWitness.vmVerifierPush, EnsembleWitness.vmVerifierPull,
    EnsembleWitness.vmVerifierEnabled] at grts_of_reqs
  rw [← Channel.eval_pulledIf, AbstractInteraction.eval_guarantees] at grts_of_reqs
  rw [← Channel.eval_pushedIf, AbstractInteraction.eval_requirements] at grts_of_reqs
  simp only [Table.ChannelGuarantees, Table.ChannelRequirements, circuit_norm]
  simp only [← Operations.forall_interactionsWith_iff, vm.verifierInteractionsWith_eq]
  simp_all only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
  tauto
end EnsembleWitness

namespace Ensemble

theorem addVm_soundVmChannel_of_soundChannels [Fact (ringChar F ≠ 2)] (ens : Ensemble F PublicIO)
      -- given a sound channels ensemble with a list of finished, consistent channels
    {finished : List (RawChannel F)} (soundChannels : ens.SoundChannels finished)
    (consistent : ∀ channel ∈ finished, channel.Consistent)
    (finished_subset : finished ⊆ ens.channels)
    (verifier_empty : ens.verifier = .empty F PublicIO)
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
  4) finally, `VmTables.verifier_requirements` gives us the requirements for the verifier,
     from which the conclusion follows.
  -/
  have witness_length : witness.tables.length = vm.tables.length + ens.tables.length := by
    rw [← witness.same_length]
    simp [Ensemble.addVm]
  have allTables_split : witness.allTables =
      witness.vmAllTables ++ witness.tables.drop vm.tables.length := by
    rw [EnsembleWitness.allTables, EnsembleWitness.vmAllTables,
      ← witness.vmVerifierTable_eq]
    simp [List.take_append_drop]
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
    tables := witness.vmAllTables
    data := witness.data
    assumptions_sufficient := by
      intro table htable
      simp only [EnsembleWitness.vmAllTables, List.mem_cons] at htable
      rcases htable with rfl | htable
      · simp [Table.AssumptionsSufficient, Table.Assumptions, Table.CircuitAssumptions,
          Ensemble.verifierWitnessTable, Component.RowAssumptions,
          Component.CircuitAssumptions]
      · exact table.assumptionsSufficient
          (witness.data_consistent table (List.mem_of_mem_take htable))
  }
  let oldContext : TableContext F := {
    tables := ens.verifierWitnessTable witness.publicInput ::
      witness.tables.drop vm.tables.length
    data := witness.data
    assumptions_sufficient := by
      intro table htable
      simp only [List.mem_cons] at htable
      rcases htable with rfl | htable
      · simp [Table.AssumptionsSufficient, Table.Assumptions, Table.CircuitAssumptions,
          Ensemble.verifierWitnessTable, Component.RowAssumptions,
          Component.CircuitAssumptions]
      · exact table.assumptionsSufficient
          (witness.data_consistent table (List.mem_of_mem_drop htable))
  }
  set vmChannel := vm.channel.toRaw
  -- the vm channel interactions are constrained to vm tables
  have vmInteractions_eq : witness.interactionsWith vmChannel =
      witness.vmInteractionsWith vmChannel := by
    simp only [EnsembleWitness.interactionsWith, EnsembleWitness.vmInteractionsWith,
      allTables_split, List.flatMap_append]
    suffices (witness.tables.drop vm.tables.length).flatMap
        (·.interactionsWith witness.data vmChannel) = [] by
      rw [this, List.append_nil]
    simp only [List.flatMap_eq_nil_iff]
    intro table mem_table
    apply Table.interactionsWith_nil_of_channel_not_mem
    apply not_mem_vm_channel table.component
    exact old_component_of_mem table mem_table
  -- this already lets us supply the balance condition
  have vm_balance := balance vmChannel (by simp [vmChannel, Ensemble.addVm])
  simp only [circuit_norm, vmInteractions_eq] at vm_balance
  -- next, we work on instantiating `requirements_of_partial_guarantees_of_constraints`
  -- which will give us exactly the second hypothesis of `verifier_guarantees`
  -- first, unify channel subset assumptions to all tables
  have grts_subset_all : ∀ table ∈ witness.vmAllTables,
      table.channelsWithGuarantees ⊆ vmChannel :: finished := by
    simp only [EnsembleWitness.vmAllTables, List.forall_mem_cons]
    constructor
    · change vm.verifier.channelsWithGuarantees ⊆ vmChannel :: finished
      exact grts_subset.1
    intro table h_table
    apply grts_subset.2 table.component
    exact witness.vmMemTablesComponent h_table
  replace reqs_disjoint : ∀ channel ∈ finished, ∀ table ∈ witness.vmAllTables,
      channel ∉ table.channelsWithRequirements := by
    intro channel channel_mem
    simp only [EnsembleWitness.vmAllTables, List.forall_mem_cons]
    constructor
    · change channel ∉ vm.verifier.channelsWithRequirements
      exact (reqs_disjoint channel channel_mem).1
    intro table table_mem
    apply (reqs_disjoint channel channel_mem).2
    exact witness.vmMemTablesComponent table_mem
  -- specialize constraints and assumptions to both old and vm ensemble
  have old_constraints : oldContext.Constraints := by
    simp only [EnsembleWitness.Constraints, allTables_split, List.mem_append] at constraints ⊢
    simp only [TableContext.Constraints, oldContext, List.mem_cons]
    intro table table_mem
    rcases table_mem with rfl | table_mem
    · exact ens.verifierWitnessTable_constraints_of_verifier_empty
        witness.publicInput witness.data verifier_empty
    · exact constraints table (.inr table_mem)
  have vm_constraints : witness.VmConstraints := by
    simp only [EnsembleWitness.Constraints, allTables_split, List.mem_append] at constraints ⊢
    intro table table_mem
    exact constraints table (.inl table_mem)
  have verifier_guarantees := witness.vmVerifierGuarantees vm_balance vm_constraints
  have old_assumptions : oldContext.Assumptions := by
    simp only [EnsembleWitness.Assumptions, allTables_split, List.mem_append] at assumptions ⊢
    simp only [TableContext.Assumptions, oldContext, List.mem_cons]
    intro table table_mem
    rcases table_mem with rfl | table_mem
    · exact ens.verifierWitnessTable_assumptions_of_verifier_empty
        witness.publicInput witness.data verifier_empty
    · exact assumptions table (.inr table_mem)
  have vm_assumptions : ∀ table ∈ witness.vmAllTables,
      table.Assumptions witness.data := by
    simp only [EnsembleWitness.Assumptions, allTables_split, List.mem_append] at assumptions ⊢
    intro table table_mem
    exact assumptions table (.inl table_mem)
  -- establish partial balance + specialize to old ensemble
  have partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel (vmContext.append oldContext rfl) channel := by
    intro channel channel_mem
    apply partialBalancedChannel_of_balancedInteractions
    · convert balance channel (by simp [Ensemble.addVm, finished_subset channel_mem]) using 1
      simp only [TableContext.interactionsWith_append, vmContext, oldContext,
        TableContext.interactionsWith, List.flatMap_cons,
        EnsembleWitness.tableContext, allTables_split, List.flatMap_append]
      have empty_verifier_interactions :
          (ens.verifierWitnessTable witness.publicInput).interactionsWith
            witness.data channel = [] := by
        apply Table.interactionsWith_nil_of_channel_not_mem
        change channel ∉ ens.verifier.channels
        rw [verifier_empty]
        simp [GeneralFormalCircuit.empty, circuit_norm]
      rw [empty_verifier_interactions, List.nil_append]
  have old_partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel oldContext channel := by
    intro channel' channel_mem'
    apply partialBalancedChannel_of_sublist (subtables := oldContext)
      (tables := vmContext.append oldContext rfl)
      rfl (partial_balance _ channel_mem')
    use vmContext.tables
    simp only [circuit_norm, List.perm_append_comm]
    exact ⟨vm_constraints, reqs_disjoint _ channel_mem'⟩
  -- invoke old tables soundness to get reqs for finished channels from constraints
  -- uses `soundChannels`, `old_constraints`, and `old_partial_balance`
  have finished_reqs : ∀ channel ∈ finished, ∀ table ∈ oldContext.tables,
      table.ChannelRequirements witness.data channel := by
    intro channel channel_mem table table_mem
    refine spec_and_guarantees_of_soundChannels (witness := oldContext)
      ?soundChannels old_assumptions old_constraints old_partial_balance table table_mem
      |>.right channel channel_mem |>.right
    simpa only [oldContext, TableContext.components, List.map_cons, circuit_norm,
      old_components_eq, Ensemble.allTables] using soundChannels
  -- invoke `guarantees_of_requirements_append` to get grts for finished channels in vm tables
  have finished_grts : ∀ table ∈ witness.vmAllTables, ∀ channel ∈ finished,
      table.ChannelGuarantees witness.data channel := by
    intro table table_mem channel channel_mem
    have : channel.Consistent := consistent channel channel_mem
    apply guarantees_of_requirements_append (ts := vmContext)
      (ss := oldContext) rfl vm_constraints (reqs_disjoint _ channel_mem)
      (partial_balance _ channel_mem) (finished_reqs _ channel_mem) _ table_mem
  -- invoke `requirements_of_partial_guarantees_of_constraints` to get per-row grts → reqs for the vm channel,
  -- and use it in `verifier_guarantees`
  have reqs_of_grts (table) (h_table : table ∈ witness.vmAllTables) :=
    table.requirements_of_partial_guarantees_of_constraints (unfinished := vmChannel)
    (vmContext.assumptions_sufficient table h_table)
    (vm_assumptions table h_table) (vm_constraints table h_table)
    (grts_subset_all table h_table) (finished_grts table h_table)
  specialize verifier_guarantees reqs_of_grts
  -- massage the conclusion so it matches that of `verifier_guarantees`.
  -- mainly, we need to use (again) that all guarantees apart from the VM channel are satisfied
  rw [EnsembleWitness.verifierGuarantees_iff_verifierTable_guarantees,
    Table.guarantees_iff_channelGuarantees]
  simp only [circuit_norm]
  suffices witness.verifierTable.ChannelRequirements witness.data vm.channel.toRaw by
    intro channel channel_mem
    replace channel_mem := grts_subset.1 channel_mem
    rcases List.mem_cons.mp channel_mem with rfl | channel_mem
    · exact verifier_guarantees this
    · apply finished_grts witness.verifierTable
        (List.mem_cons.mpr (Or.inl witness.vmVerifierTable_eq)) channel channel_mem
  -- finally, we prove the verifier requirements using `VmTables.verifier_requirements`
  rw [← EnsembleWitness.verifierChannelRequirements_iff]
  apply vm.verifier_requirements
  change (ens.addVm vm names).VerifierConstraints witness.publicInput witness.data
  rw [EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
  exact vm_constraints witness.verifierTable
    (List.mem_cons.mpr (Or.inl witness.vmVerifierTable_eq))
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
    ens.soundChannels ens.finished_consistent ens.finished_subset ens.verifier_empty vm names
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
