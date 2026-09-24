module

public import Clean.Air.OrderedChannelWith
public import Clean.Air.Vm

/-!
# VM ensembles over directed channels

The counterpart of `Clean.Air.Vm` for a VM whose state channel is a `DirectedChannel` and whose
ensemble is balanced under the multiset model; `Clean.Air.Vm` reads direction off the sign of
the multiplicity and says nothing useful over a binary field. `DirectedVmTables` mirrors
`VmTables`: every table receives and provides on the state channel under one `enabled` gate
that its constraints make boolean, and the verifier receives the final state and provides the
initial one.

`SoundEnsembleWith.addVm` adds a directed VM on top of a sound ensemble under the multiset
model, using `DirectedChannel.guarantees_of_requirements_of_requirements_of_guarantees` for the
state channel. Lookup channels the VM relies on are added and finished before `addVm`; all
channels of the ensemble are balanced under the same model.
-/

@[expose] public section

namespace Air.Flat
variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A VM over a directed state channel: the counterpart of `VmTables`. -/
structure DirectedVmTables (F : Type) [FiniteField F] [DecidableEq F] (PublicIO : TypeMap)
    [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : DirectedChannel F Message

  tables : List (Component F)
  verifier : GeneralFormalCircuit F PublicIO unit
  verifier_length_zero : ∀ pi, (verifier pi).localLength 0 = 0 := by
    simp only [circuit_norm]

  /-- Every table receives the current state and provides the next one, gated by one `enabled`
  that its constraints make boolean. -/
  tables_channel : tables.Forall fun table =>
    ∃ enabled : Expression F, ∃ pull push : Var Message F,
      ⟨ channel.toRaw,
        [(channel.pulledIf enabled pull).toRaw, (channel.pushedIf enabled push).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      ∀ env, ConstraintsHold.Shallow env table.rowOperations →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1

  /-- The verifier receives the final state and provides the initial one. -/
  verifier_channel : ∃ m1 m2,
    ⟨ channel.toRaw, [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw] ⟩ ∈
      verifier.exposedChannels (varFromOffset PublicIO 0) (size PublicIO)

  /-- The verifier's requirements on the state channel follow from its constraints alone. -/
  verifier_requirements :
    let offset := size PublicIO;
    let input_var := varFromOffset PublicIO 0;
    ∀ env,
      Operations.ConstraintsHold env (verifier.main input_var |>.operations offset) →
      Operations.ChannelRequirements channel.toRaw env
        (verifier.main input_var |>.operations offset)

instance (vm : DirectedVmTables F PublicIO) : ProvableType vm.Message := vm.provableMessage

def DirectedVmTables.toEnsemble (vm : DirectedVmTables F PublicIO) : Ensemble F PublicIO where
  channels := [vm.channel.toRaw]
  tables := vm.tables
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

abbrev DirectedVmWitness (vm : DirectedVmTables F PublicIO) := EnsembleWitness vm.toEnsemble

/-- `SoundVmChannel` under an explicit balance model: constraints and balance under the model
give the verifier's guarantees. -/
def Ensemble.SoundVmChannelWith (model : BalanceModel F) (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.BalancedChannelsWith model →
      ens.VerifierGuarantees witness.publicInput witness.data

/-- The legacy notion is its LogUp instance, by definition. -/
theorem Ensemble.soundVmChannel_iff_soundVmChannelWith_logUp (ens : Ensemble F PublicIO) :
    ens.SoundVmChannel ↔ ens.SoundVmChannelWith (.logUp F) := Iff.rfl

/-- A sound VM ensemble under an explicit balance model: the counterpart of `SoundVmEnsemble`,
carrying the consistency of every channel for the bundle `toFormal` produces. -/
structure SoundVmEnsembleWith (F : Type) [FiniteField F] [DecidableEq F] (model : BalanceModel F)
    (PublicIO : TypeMap) [ProvableType PublicIO] extends ensemble : Ensemble F PublicIO where
  channels_consistent : ∀ channel ∈ channels, channel.ConsistentWith model
  soundVmChannel : ensemble.SoundVmChannelWith model

namespace SoundVmEnsembleWith
variable {model : BalanceModel F}

def toFormal (ens : SoundVmEnsembleWith F model PublicIO)
    (ExtraAssumptions : PublicIO F → ProverData F → Prop)
    (extraAssumptionsConsistency : ∀ publicInput data, ExtraAssumptions publicInput data →
      ∀ table ∈ ens.ensemble.tables, ∀ input data, table.circuit.Assumptions input data) :
    FormalEnsembleWith F model PublicIO where
  ensemble := ens.ensemble
  Assumptions publicInput := ∀ data,
    ens.verifier.Assumptions publicInput data ∧
    ExtraAssumptions publicInput data
  Spec publicInput := ∃ data, ens.VerifierSpec publicInput data
  consistent := ens.channels_consistent
  soundness := by
    simp only [Ensemble.SoundnessWith, Ensemble.StatementWith]
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
    apply extraAssumptionsConsistency witness.publicInput witness.data extra_assumptions
    exact EnsembleWitness.mem_tables_component_of_mem_tables h_table

variable {ens : SoundVmEnsembleWith F model PublicIO}
  {ExtraAssumptions : PublicIO F → ProverData F → Prop}
  {eac : ∀ publicInput data, ExtraAssumptions publicInput data →
    ∀ table ∈ ens.tables, ∀ input data, table.circuit.Assumptions input data}

@[circuit_norm] lemma toFormal_ensemble :
  (ens.toFormal ExtraAssumptions eac).ensemble = ens.ensemble := rfl

@[circuit_norm] lemma toFormal_spec publicInput :
  (ens.toFormal ExtraAssumptions eac).Spec publicInput ↔
    ∃ data, ens.ensemble.VerifierSpec publicInput data := by
  simp only [toFormal]

@[circuit_norm] lemma toFormal_assumptions publicInput :
  (ens.toFormal ExtraAssumptions eac).Assumptions publicInput ↔
    ∀ data, ens.ensemble.verifier.Assumptions publicInput data ∧
      ExtraAssumptions publicInput data := by
  simp only [toFormal, circuit_norm]
end SoundVmEnsembleWith

namespace DirectedVmTables
variable {vm : DirectedVmTables F PublicIO}

@[circuit_norm] lemma toEnsemble_tables (vm : DirectedVmTables F PublicIO) :
  vm.toEnsemble.tables = vm.tables := rfl
@[circuit_norm] lemma toEnsemble_channels (vm : DirectedVmTables F PublicIO) :
  vm.toEnsemble.channels = [vm.channel.toRaw] := rfl
@[circuit_norm] lemma toEnsemble_verifier (vm : DirectedVmTables F PublicIO) :
  vm.toEnsemble.verifier = vm.verifier := rfl

theorem tables_channel_of_mem (vm : DirectedVmTables F PublicIO) {table}
    (table_mem : table ∈ vm.tables) :
  ∃ enabled : Expression F, ∃ pull push : Var vm.Message F,
    ⟨ vm.channel.toRaw,
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

@[circuit_norm] abbrev allTables (vm : DirectedVmTables F PublicIO) : List (Component F) :=
  vm.toEnsemble.allTables

noncomputable def tableStep (vm : DirectedVmTables F PublicIO) {table : Component F}
    (table_mem : table ∈ vm.tables) : VmStep vm.Message F where
  enabled := (vm.tables_channel_of_mem table_mem).choose
  pull := (vm.tables_channel_of_mem table_mem).choose_spec.choose
  push := (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose

/-- Concrete version of `DirectedVmTables.tables_channel`. -/
theorem tables_channel' (vm : DirectedVmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
  let step := vm.tableStep table_mem
  ⟨ vm.channel.toRaw,
    [(vm.channel.pulledIf step.enabled step.pull).toRaw,
      (vm.channel.pushedIf step.enabled step.push).toRaw] ⟩ ∈ table.exposedChannels :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.left

theorem tableStep_enabled_isBool (vm : DirectedVmTables F PublicIO) {table}
    (table_mem : table ∈ vm.tables) :
    ∀ env, table.operations.ConstraintsHold env →
      IsBool (Expression.eval env (vm.tableStep table_mem).enabled) :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.right

noncomputable def verifierPull (vm : DirectedVmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose

noncomputable def verifierPush (vm : DirectedVmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose_spec.choose

/-- Concrete version of `DirectedVmTables.verifier_channel`. -/
theorem verifier_channel' (vm : DirectedVmTables F PublicIO) :
  ⟨ vm.channel.toRaw,
    [(vm.channel.pulled vm.verifierPull).toRaw,
      (vm.channel.pushed vm.verifierPush).toRaw] ⟩ ∈
    vm.verifier.exposedChannels (varFromOffset PublicIO 0) (size PublicIO) :=
  vm.verifier_channel.choose_spec.choose_spec

noncomputable def verifierStep (vm : DirectedVmTables F PublicIO) : VmStep vm.Message F where
  enabled := 1
  pull := vm.verifierPull
  push := vm.verifierPush

open Classical in noncomputable
def step (vm : DirectedVmTables F PublicIO) {table : Component F}
    (h_mem : table ∈ vm.allTables) : VmStep vm.Message F :=
  if h : table = vm.toEnsemble.verifierTable
  then vm.verifierStep
  else vm.tableStep (List.mem_of_ne_of_mem h h_mem)

theorem allTables_channel (vm : DirectedVmTables F PublicIO) :
  ∀ (table) (table_mem : table ∈ vm.allTables),
  let step := vm.step table_mem
  ⟨ vm.channel.toRaw,
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

lemma interactionsWith_eq {vm : DirectedVmTables F PublicIO} {table} (h : table ∈ vm.allTables) :
  table.operations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf (vm.step h).enabled (vm.step h).pull).toRaw,
    (vm.channel.pushedIf (vm.step h).enabled (vm.step h).push).toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  apply vm.allTables_channel

lemma verifierInteractionsWith_eq {vm : DirectedVmTables F PublicIO} :
  vm.toEnsemble.verifierTable.operations.interactionsWith vm.channel.toRaw = [
    (vm.channel.pulledIf vm.verifierStep.enabled vm.verifierStep.pull).toRaw,
    (vm.channel.pushedIf vm.verifierStep.enabled vm.verifierStep.push).toRaw ] := by
  simpa only [step, reduceDIte] using interactionsWith_eq Ensemble.mem_allTables_verifierTable
end DirectedVmTables

namespace DirectedVmWitness
variable {vm : DirectedVmTables F PublicIO}
open EnsembleWitness

noncomputable def rowEnabled (witness : DirectedVmWitness vm) {table}
    (h : table ∈ witness.allTables) (row : Array F) : F :=
  (table.environment row)
    (vm.step (witness.mem_allTables_component_of_mem_allTables h)).enabled

noncomputable def rowPull (witness : DirectedVmWitness vm) {table} (h : table ∈ witness.allTables)
    (row : Array F) : vm.Message F :=
  eval (table.environment row)
    (vm.step (witness.mem_allTables_component_of_mem_allTables h)).pull

noncomputable def rowPush (witness : DirectedVmWitness vm) {table} (h : table ∈ witness.allTables)
    (row : Array F) : vm.Message F :=
  eval (table.environment row)
    (vm.step (witness.mem_allTables_component_of_mem_allTables h)).push

noncomputable def verifierEnabled (witness : DirectedVmWitness vm) : F :=
  Expression.eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.enabled

lemma verifierEnabled_eq_one (witness : DirectedVmWitness vm) : witness.verifierEnabled = 1 := by
  simp only [verifierEnabled, DirectedVmTables.verifierStep, circuit_norm]

noncomputable def verifierPull (witness : DirectedVmWitness vm) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.pull

noncomputable def verifierPush (witness : DirectedVmWitness vm) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.push

/-- The evaluated state-channel interactions of a row: a receive that assumes the guarantee
and a provide, both gated by the row's `enabled`. -/
lemma interactionValuesWith_eq (witness : DirectedVmWitness vm)
    {table} (h : table ∈ witness.allTables) (row : Array F) :
  table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row) = [
    vm.channel.emittedValue .receive (witness.rowEnabled h row) (witness.rowPull h row) true,
    vm.channel.emittedValue .provide (witness.rowEnabled h row) (witness.rowPush h row)
      false ] := by
  simp only [circuit_norm,
    vm.interactionsWith_eq (witness.mem_allTables_component_of_mem_allTables h),
    rowEnabled, rowPull, rowPush, DirectedChannel.eval_toRaw]

noncomputable def interactionPairs (witness : DirectedVmWitness vm) :
    List (Interaction F × Interaction F) :=
  witness.allTables.attach.flatMap fun ⟨ table, h ⟩ =>
    table.table.map fun row =>
      (vm.channel.emittedValue .receive (witness.rowEnabled h row) (witness.rowPull h row) true,
        vm.channel.emittedValue .provide (witness.rowEnabled h row) (witness.rowPush h row)
          false)

lemma mem_interactionPairs_iff {witness : DirectedVmWitness vm}
    {pair : Interaction F × Interaction F} :
  pair ∈ witness.interactionPairs ↔
    ∃ (table : Table F) (h : table ∈ witness.allTables), ∃ row ∈ table.table,
    pair = (vm.channel.emittedValue .receive (witness.rowEnabled h row) (witness.rowPull h row)
        true,
      vm.channel.emittedValue .provide (witness.rowEnabled h row) (witness.rowPush h row)
        false) := by
  simp [interactionPairs]
  tauto

noncomputable def pulls (witness : DirectedVmWitness vm) : List (Interaction F) :=
  witness.interactionPairs.map Prod.fst

noncomputable def pushes (witness : DirectedVmWitness vm) : List (Interaction F) :=
  witness.interactionPairs.map Prod.snd

lemma zip_pulls_pushes_eq_interactionPairs {witness : DirectedVmWitness vm} :
    List.zip witness.pulls witness.pushes = witness.interactionPairs := by
  simp only [pulls, pushes, List.zip_map_fst_snd]

lemma mem_pulls_iff {witness : DirectedVmWitness vm} {pull : Interaction F} :
  pull ∈ witness.pulls ↔
    ∃ (table : Table F) (h : table ∈ witness.allTables), ∃ row ∈ table.table,
    pull = vm.channel.emittedValue .receive (witness.rowEnabled h row) (witness.rowPull h row)
      true := by
  simp [pulls, interactionPairs]
  tauto

lemma mem_pushes_iff {witness : DirectedVmWitness vm} {push : Interaction F} :
  push ∈ witness.pushes ↔
    ∃ (table : Table F) (h : table ∈ witness.allTables), ∃ row ∈ table.table,
    push = vm.channel.emittedValue .provide (witness.rowEnabled h row) (witness.rowPush h row)
      false := by
  simp [pushes, interactionPairs]
  tauto

def steps (witness : DirectedVmWitness vm) : ℕ := witness.tables.map (·.length) |>.sum

@[circuit_norm]
lemma pulls_length {witness : DirectedVmWitness vm} : witness.pulls.length = witness.steps + 1 := by
  simp [steps, pulls, interactionPairs, allTables, circuit_norm]

@[circuit_norm]
lemma pushes_length {witness : DirectedVmWitness vm} :
    witness.pushes.length = witness.steps + 1 := by
  simp [steps, pushes, interactionPairs, allTables, circuit_norm]

lemma rowEnabled_isBool_of_constraints {witness : DirectedVmWitness vm} :
    witness.Constraints →
    ∀ table (h : table ∈ witness.allTables), ∀ row ∈ table.table,
      IsBool (witness.rowEnabled h row) := by
  intro constraints table table_mem row row_mem
  simp only [circuit_norm, rowEnabled, DirectedVmTables.step, DirectedVmTables.verifierStep]
  by_cases h_verifier : table.component = vm.toEnsemble.verifierTable
  · simp [circuit_norm, h_verifier]
  have component_mem : table.component ∈ vm.tables := by
    have h_mem := witness.mem_allTables_component_of_mem_allTables table_mem
    simp only [circuit_norm, Ensemble.allTables, List.mem_cons] at h_mem
    exact h_mem.resolve_left h_verifier
  have h_constraints := constraints table table_mem row row_mem
  simp only [h_verifier, reduceDIte]
  exact vm.tableStep_enabled_isBool component_mem _ h_constraints

/-- The gates are boolean: the `UnitEvent` discipline of the multiset model. -/
lemma pulls_mult {witness : DirectedVmWitness vm} :
  witness.Constraints →
    ∀ pull ∈ witness.pulls, pull.mult = 0 ∨ pull.mult = 1 := by
  simp_rw [witness.mem_pulls_iff]
  rintro constraints pull ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm]
  apply witness.rowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›

lemma pushes_mult {witness : DirectedVmWitness vm} :
  witness.Constraints →
    ∀ push ∈ witness.pushes, push.mult = 0 ∨ push.mult = 1 := by
  simp_rw [witness.mem_pushes_iff]
  rintro constraints push ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm]
  apply witness.rowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›

@[circuit_norm]
lemma pulls_channel {witness : DirectedVmWitness vm} :
    ∀ pull ∈ witness.pulls, pull.channel = vm.channel.toRaw := by
  simp_rw [mem_pulls_iff]
  rintro pull ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm]

@[circuit_norm]
lemma pushes_channel {witness : DirectedVmWitness vm} :
    ∀ push ∈ witness.pushes, push.channel = vm.channel.toRaw := by
  simp_rw [mem_pushes_iff]
  rintro push ⟨ table, table_mem, row, row_mem, rfl ⟩
  simp only [circuit_norm]

/-- In the directed reading, every pull is a receive ... -/
lemma pulls_receive {witness : DirectedVmWitness vm} :
    ∀ pull ∈ witness.pulls, pull.directedEvent.direction = .receive := by
  simp_rw [mem_pulls_iff]
  rintro pull ⟨ table, table_mem, row, row_mem, rfl ⟩
  rw [DirectedChannel.directedEvent_emittedValue]

/-- ... and every push a provide. -/
lemma pushes_provide {witness : DirectedVmWitness vm} :
    ∀ push ∈ witness.pushes, push.directedEvent.direction = .provide := by
  simp_rw [mem_pushes_iff]
  rintro push ⟨ table, table_mem, row, row_mem, rfl ⟩
  rw [DirectedChannel.directedEvent_emittedValue]

lemma interactionss_eq_interactionPairs (witness : DirectedVmWitness vm) :
  witness.allTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    witness.interactionPairs.map (fun ⟨pull, push⟩ => [pull, push]) := by
  simp only [interactionPairs, List.flatMap_def, List.map_flatten]
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ⟨ table, table_mem ⟩ _
  simp [Table.interactionssWith, witness.interactionValuesWith_eq table_mem]

lemma interactionss_eq_pulls_pushes (witness : DirectedVmWitness vm) :
  witness.allTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [interactionss_eq_interactionPairs]
  simp [pulls, pushes, List.zip_map_fst_snd]

lemma interactions_eq_pulls_pushes (witness : DirectedVmWitness vm) :
  witness.interactionsWith vm.channel.toRaw =
    (List.zip witness.pulls witness.pushes).flattenPairs := by
  rw [witness.flatMap_interactionsWith_eq_flatten,
    interactionss_eq_pulls_pushes, List.flattenPairs]

lemma mem_zip_pulls_pushes_iff (witness : DirectedVmWitness vm) (pull push : Interaction F) :
  (pull, push) ∈ List.zip witness.pulls witness.pushes ↔
    ∃ table ∈ witness.allTables, ∃ row ∈ table.table,
      table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row) =
        [pull, push] := by
  trans [pull, push] ∈
    (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push])
  · simp
  simp [← interactionss_eq_pulls_pushes, Table.interactionssWith]

/-- A receive owes only its boolean gate, which the constraints supply. -/
lemma pull_requirements_of_constraints {witness : DirectedVmWitness vm} :
  witness.Constraints →
    ∀ pull ∈ witness.pulls, pull.Requirements witness.data := by
  intro constraints
  simp_rw [witness.mem_pulls_iff]
  rintro pull ⟨ table, table_mem, row, row_mem, rfl ⟩
  rw [DirectedChannel.emittedValue_requirements_iff]
  exact ⟨ witness.rowEnabled_isBool_of_constraints constraints _ ‹_› _ ‹_›, by simp ⟩

/-- A provide assumes nothing. -/
lemma push_guarantees {witness : DirectedVmWitness vm} :
  ∀ push ∈ witness.pushes, push.Guarantees witness.data := by
  simp_rw [witness.mem_pushes_iff]
  rintro push ⟨ table, table_mem, row, row_mem, rfl ⟩
  rw [DirectedChannel.emittedValue_guarantees_iff]
  simp

lemma pulls_length_pos {witness : DirectedVmWitness vm} : witness.pulls.length > 0 := by
  simp [pulls_length]
lemma pushes_length_pos {witness : DirectedVmWitness vm} : witness.pushes.length > 0 := by
  simp [pushes_length]

lemma pulls_getElem_zero_eq (witness : DirectedVmWitness vm) :
    witness.pulls[0]'pulls_length_pos =
      vm.channel.emittedValue .receive witness.verifierEnabled witness.verifierPull true := by
  simp [pulls, interactionPairs, allTables, circuit_norm, rowEnabled, rowPull,
    verifierPull, verifierEnabled, DirectedVmTables.step, DirectedVmTables.verifierStep]

lemma pushes_getElem_zero_eq (witness : DirectedVmWitness vm) :
    witness.pushes[0]'pushes_length_pos =
      vm.channel.emittedValue .provide witness.verifierEnabled witness.verifierPush false := by
  simp [pushes, interactionPairs, allTables, circuit_norm, rowEnabled, rowPush,
    verifierPush, verifierEnabled, DirectedVmTables.step, DirectedVmTables.verifierStep]

/--
The VM theorem for `DirectedVmTables` under the multiset model: the counterpart of
`VmWitness.verifier_guarantees_of_requirements_of_requirements_of_guarantees`, with count
balance derived from the model's relation and the boolean gates.
-/
theorem verifier_guarantees_of_requirements_of_requirements_of_guarantees
    (witness : DirectedVmWitness vm) :
  -- if the vm interactions with the vm channel are balanced under the multiset model
  (BalanceModel.multiset F).Balanced (witness.interactionsWith vm.channel.toRaw) →
  witness.Constraints →
  -- and for every row, vm channel guarantees imply vm channel requirements
  (∀ table ∈ witness.allTables, ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees vm.channel.toRaw (table.environment row) →
    table.component.operations.ChannelRequirements vm.channel.toRaw (table.environment row)) →
  -- vm channel verifier requirements imply vm channel verifier guarantees
  witness.verifierTable.ChannelRequirements vm.channel.toRaw →
    witness.verifierTable.ChannelGuarantees vm.channel.toRaw := by
  intro balance witness_constraints constraints
  -- balance of pulls ++ pushes under the model
  replace balance : (BalanceModel.multiset F).Balanced (witness.pulls ++ witness.pushes) := by
    rw [witness.interactions_eq_pulls_pushes] at balance
    apply (BalanceModel.multiset F).balanced_of_perm balance
    apply List.zip_flattenPairs_perm <| witness.pushes_length ▸ witness.pulls_length.symm
  -- hence count balance, under the boolean-gate discipline
  have count_balance :
      CountBalanced Interaction.directedEvent (witness.pulls ++ witness.pushes) := by
    have unit : ∀ i ∈ witness.pulls ++ witness.pushes, (BalanceModel.multiset F).UnitEvent i := by
      intro i hi
      rw [BalanceModel.multiset_unitEvent_iff]
      rcases List.mem_append.mp hi with hi | hi
      · exact witness.pulls_mult witness_constraints i hi
      · exact witness.pushes_mult witness_constraints i hi
    exact (BalanceModel.multiset F).countBalanced_of_balanced balance unit
  -- the directed VM theorem, on the lists of pulls and pushes
  have grts_of_reqs := vm.channel.guarantees_of_requirements_of_requirements_of_guarantees
    witness.pulls witness.pushes count_balance witness.data (witness.steps + 1)
    pulls_length pushes_length witness.pulls_channel witness.pushes_channel
    witness.pulls_receive witness.pushes_provide
  -- its (grts → reqs) assumption is a reformulation of our `constraints`
  have len_pulls : witness.pulls.length = witness.steps + 1 := pulls_length
  have len_pushes : witness.pushes.length = witness.steps + 1 := pushes_length
  have reqs_of_grts : ∀ i (hi : i < witness.steps + 1),
      witness.pulls[i].Guarantees witness.data → witness.pushes[i].Requirements witness.data := by
    suffices ∀ pair ∈ (witness.pulls.zip witness.pushes),
        pair.1.Guarantees witness.data → pair.2.Requirements witness.data by
      intro i hi
      have hi_z : i < (witness.pulls.zip witness.pushes).length := by
        rw [List.length_zip, len_pulls, len_pushes]
        omega
      exact this _ (List.mem_iff_getElem.mpr ⟨i, hi_z, List.getElem_zip⟩)
    intro (pull, push) pair_mem
    simp only
    have ⟨ mem_pull, mem_push ⟩ := List.of_mem_zip pair_mem
    have push_grts := witness.push_guarantees push mem_push
    have pull_reqs := witness.pull_requirements_of_constraints witness_constraints pull mem_pull
    rw [witness.mem_zip_pulls_pushes_iff] at pair_mem
    obtain ⟨ table, table_mem, row, row_mem, interactions_eq ⟩ := pair_mem
    suffices (∀ i ∈ [pull, push], i.Guarantees witness.data) →
        (∀ i ∈ [pull, push], i.Requirements witness.data) by
      simp_all
    rw [← interactions_eq, Operations.interactionValuesWith_eq_map, List.forall_mem_map,
      List.forall_mem_map]
    have env_data_eq : (table.environment row).data = witness.data :=
      witness.data_eq_of_mem_allTables _ table_mem
    simp only [← env_data_eq, AbstractInteraction.eval_guarantees,
      AbstractInteraction.eval_requirements, Operations.forall_interactionsWith_iff]
    exact constraints table table_mem row row_mem
  -- to get the conclusion about the verifier, we specialize to index 0
  specialize grts_of_reqs reqs_of_grts 0 (by omega)
  rw [witness.pulls_getElem_zero_eq, witness.pushes_getElem_zero_eq] at grts_of_reqs
  simp only [verifierPush, verifierPull, verifierEnabled] at grts_of_reqs
  set env := Environment.fromInput witness.publicInput witness.data with h_env
  have e_pull : vm.channel.emittedValue .receive (Expression.eval env vm.verifierStep.enabled)
      (eval env vm.verifierStep.pull) true =
        (vm.channel.pulledIf vm.verifierStep.enabled vm.verifierStep.pull).toRaw.eval env :=
    (DirectedChannel.eval_toRaw
      (i := vm.channel.pulledIf vm.verifierStep.enabled vm.verifierStep.pull) (env := env)).symm
  have e_push : vm.channel.emittedValue .provide (Expression.eval env vm.verifierStep.enabled)
      (eval env vm.verifierStep.push) false =
        (vm.channel.pushedIf vm.verifierStep.enabled vm.verifierStep.push).toRaw.eval env :=
    (DirectedChannel.eval_toRaw
      (i := vm.channel.pushedIf vm.verifierStep.enabled vm.verifierStep.push) (env := env)).symm
  rw [e_pull, e_push, AbstractInteraction.eval_guarantees, AbstractInteraction.eval_requirements]
    at grts_of_reqs
  simp only [Table.ChannelGuarantees, Table.ChannelRequirements, circuit_norm]
  simp only [← Operations.forall_interactionsWith_iff, vm.verifierInteractionsWith_eq]
  simp_all only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
  tauto
end DirectedVmWitness

namespace Ensemble
/-- Add a directed VM to an ensemble: its state channel is added, its tables are put first,
and its verifier replaces the ensemble's. -/
def addDirectedVm (ens : Ensemble F PublicIO) (vm : DirectedVmTables F PublicIO) :
    Ensemble F PublicIO :=
  ens.merge vm.toEnsemble

@[circuit_norm] lemma addDirectedVm_channels (ens : Ensemble F PublicIO)
    (vm : DirectedVmTables F PublicIO) :
  (ens.addDirectedVm vm).channels = vm.channel.toRaw :: ens.channels := rfl
@[circuit_norm] lemma addDirectedVm_tables (ens : Ensemble F PublicIO)
    (vm : DirectedVmTables F PublicIO) :
  (ens.addDirectedVm vm).tables = vm.tables ++ ens.tables := rfl
@[circuit_norm] lemma addDirectedVm_verifier (ens : Ensemble F PublicIO)
    (vm : DirectedVmTables F PublicIO) :
  (ens.addDirectedVm vm).verifier = vm.verifier := rfl

/-- Split up the witness of `Ensemble.addDirectedVm _ _`. -/
lemma addDirectedVm_witness (ens : Ensemble F PublicIO) (vm : DirectedVmTables F PublicIO)
  (witness : EnsembleWitness (ens.addDirectedVm vm)) :
    ∃ (vmWitness : DirectedVmWitness vm) (witness' : EnsembleWitness ens),
      witness.tables = vmWitness.tables ++ witness'.tables ∧
      witness.allTables = vmWitness.allTables ++ witness'.tables ∧
      vmWitness.publicInput = witness.publicInput ∧
      witness'.publicInput = witness.publicInput ∧
      vmWitness.data = witness.data ∧
      witness'.data = witness.data := by
  obtain ⟨ witness', vmWitness, tables_eq, -, -, publicInput', publicInput_vm, data', data_vm ⟩ :=
    Ensemble.mergeEnsemble_witness ens vm.toEnsemble witness
  refine ⟨ vmWitness, witness', tables_eq, ?_, publicInput_vm, publicInput', data_vm, data' ⟩
  simp only [EnsembleWitness.allTables, tables_eq, List.cons_append]
  congr 1
  exact Ensemble.verifierTable_ext rfl publicInput_vm.symm data_vm.symm

/--
Soundness of a directed VM on top of a sound ensemble under the multiset model: the
counterpart of `addVm_soundVmChannel_of_soundChannels`. The consistency of the finished
channels is the third conjunct of `soundChannels`.
-/
theorem addDirectedVm_soundVmChannelWith_of_soundChannelsWith (ens : Ensemble F PublicIO)
    {finished : List (RawChannel F)} (soundChannels : ens.SoundChannelsWith (.multiset F) finished)
    (finished_subset : finished ⊆ ens.channels)
    (verifier_empty : ens.verifier = .empty F PublicIO)
    (vm : DirectedVmTables F PublicIO) :
    -- assuming that none of the existing tables interacted with the VM channel
    (∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) →
    -- assuming that the VM tables' and verifier's channelsWithGuarantees are either finished
    -- or the VM channel
    (vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished) →
    -- and assuming the VM tables' channelsWithRequirements contain none of the finished ones
    (∀ channel ∈ finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements) →
    (ens.addDirectedVm vm).SoundVmChannelWith (.multiset F) := by
  intro not_mem_vm_channel grts_subset reqs_disjoint witness assumptions constraints balance
  obtain ⟨ vmWitness, witness', _, allTables_split, publicInput_eq_vm, _, data_eq_vm,
    data_eq_old ⟩ :=
    addDirectedVm_witness ens vm witness
  have data_eq : vmWitness.data = witness'.data := by rw [data_eq_vm, data_eq_old]
  have verifierTable_eq : vmWitness.verifierTable = witness.verifierTable :=
    Ensemble.verifierTable_ext rfl publicInput_eq_vm data_eq_vm
  set vmTables := vmWitness.tables
  set vmChannel := vm.channel.toRaw
  -- the vm channel interactions are constrained to vm tables
  have vmInteractions_eq :
      witness.interactionsWith vmChannel = vmWitness.interactionsWith vmChannel := by
    simp only [EnsembleWitness.interactionsWith, allTables_split, List.flatMap_append]
    suffices witness'.tables.flatMap (·.interactionsWith vmChannel) = [] by
      rw [this, List.append_nil]
    simp only [List.flatMap_eq_nil_iff]
    intro table mem_table
    apply Table.interactionsWith_nil_of_channel_not_mem
    apply not_mem_vm_channel table.component
    exact EnsembleWitness.mem_tables_component_of_mem_tables mem_table
  -- this already lets us supply the balance condition
  have vm_balance := balance vmChannel (by simp [vmChannel, circuit_norm])
  simp only [circuit_norm, vmInteractions_eq] at vm_balance
  have grts_subset_all : ∀ table ∈ vmWitness.allTables,
      table.channelsWithGuarantees ⊆ vmChannel :: finished := by
    simp only [circuit_norm, EnsembleWitness.allTables]
    use grts_subset.1
    intro table h_table
    apply grts_subset.2 table.component
    apply EnsembleWitness.mem_tables_component_of_mem_tables h_table
  replace reqs_disjoint : ∀ channel ∈ finished, ∀ table ∈ vmWitness.allTables,
      channel ∉ table.channelsWithRequirements := by
    intro channel channel_mem
    simp only [circuit_norm, DirectedVmTables.toEnsemble, EnsembleWitness.allTables]
    use (reqs_disjoint channel channel_mem).1
    intro table table_mem
    apply (reqs_disjoint channel channel_mem).2
    apply EnsembleWitness.mem_tables_component_of_mem_tables table_mem
  -- specialize constraints and assumptions to both old and vm ensemble
  have constraints' : witness'.Constraints := by
    simp only [EnsembleWitness.Constraints, allTables_split, List.mem_append] at constraints ⊢
    simp only [EnsembleWitness.forall_mem_allTables_iff]
    use witness'.verifierTable_constraints_of_verifier_empty verifier_empty
    intro table table_mem
    exact constraints table (.inr table_mem)
  have vm_constraints : vmWitness.Constraints := by
    simp only [EnsembleWitness.Constraints, allTables_split, List.mem_append] at constraints ⊢
    intro table table_mem
    exact constraints table (.inl table_mem)
  have verifier_guarantees := vmWitness
    |>.verifier_guarantees_of_requirements_of_requirements_of_guarantees vm_balance vm_constraints
  have assumptions' : witness'.Assumptions := by
    simp only [EnsembleWitness.Assumptions, allTables_split, List.mem_append] at assumptions ⊢
    simp only [EnsembleWitness.forall_mem_allTables_iff]
    use witness'.verifierTable_assumptions_of_verifier_empty verifier_empty
    intro table table_mem
    exact assumptions table (.inr table_mem)
  have vm_assumptions : vmWitness.Assumptions := by
    simp only [EnsembleWitness.Assumptions, allTables_split, List.mem_append] at assumptions ⊢
    intro table table_mem
    exact assumptions table (.inl table_mem)
  -- establish partial balance + specialize to old ensemble
  have partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannelWith (.multiset F) (.append vmWitness witness' data_eq) channel := by
    intro channel channel_mem
    apply partialBalancedChannelWith_of_balanced
    · convert balance channel (by simp [circuit_norm, finished_subset channel_mem]) using 1
      simp only [circuit_norm]
      rw [EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty]
      simp only [EnsembleWitness.interactionsWith, allTables_split, circuit_norm]
  have partial_balance' : ∀ channel ∈ finished,
      PartialBalancedChannelWith (.multiset F) witness' channel := by
    intro channel' channel_mem'
    apply partialBalancedChannelWith_of_sublist (partial_balance _ channel_mem')
    use vmWitness.allTables
    simp only [circuit_norm, List.perm_append_comm]
    exact ⟨vm_constraints, reqs_disjoint _ channel_mem'⟩
  -- invoke old tables soundness to get reqs for finished channels from constraints
  have finished_reqs : ∀ channel ∈ finished, ∀ table ∈ witness'.allTables,
      table.ChannelRequirements channel := by
    intro channel channel_mem table table_mem
    refine spec_and_guarantees_of_soundChannelsWith (witness := witness'.allTablesWitness)
      ?soundChannels assumptions' constraints' partial_balance' table table_mem
      |>.right channel channel_mem |>.right
    convert soundChannels
    simp [circuit_norm]
  -- invoke `guarantees_of_requirements_append_with` to get grts for finished channels in vm tables
  have finished_grts : ∀ table ∈ vmWitness.allTables, ∀ channel ∈ finished,
      table.ChannelGuarantees channel := by
    intro table table_mem channel channel_mem
    have : channel.ConsistentWith (.multiset F) := soundChannels.2.2 channel channel_mem
    apply guarantees_of_requirements_append_with (ts := vmWitness.allTablesWitness)
      (ss := witness'.allTablesWitness) data_eq vm_constraints (reqs_disjoint _ channel_mem)
      (partial_balance _ channel_mem) (finished_reqs _ channel_mem) _ table_mem
  -- per-row grts → reqs for the vm channel, and use it in `verifier_guarantees`
  have reqs_of_grts (table) (h_table : table ∈ vmWitness.allTables) :=
    table.requirements_of_partial_guarantees_of_constraints (unfinished := vmChannel)
    (vm_assumptions table h_table) (vm_constraints table h_table)
    (grts_subset_all table h_table) (finished_grts table h_table)
  specialize verifier_guarantees reqs_of_grts
  -- massage the conclusion so it matches that of `verifier_guarantees`
  rw [EnsembleWitness.verifierGuarantees_iff_verifierTable_guarantees, ← verifierTable_eq,
    Table.guarantees_iff_channelGuarantees]
  simp only [circuit_norm]
  suffices vmWitness.verifierTable.ChannelRequirements vm.channel.toRaw by
    intro channel channel_mem
    replace channel_mem := grts_subset.1 channel_mem
    rcases List.mem_cons.mp channel_mem with rfl | channel_mem
    · exact verifier_guarantees this
    · exact finished_grts _ vmWitness.mem_allTables_verifierTable _ channel_mem
  -- finally, we prove the verifier requirements using `DirectedVmTables.verifier_requirements`
  rw [← EnsembleWitness.verifierChannelRequirements_iff]
  apply vm.verifier_requirements
  show vm.toEnsemble.VerifierConstraints vmWitness.publicInput vmWitness.data
  rw [EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
  exact vm_constraints _ vmWitness.mem_allTables_verifierTable
end Ensemble

namespace SoundEnsembleWith

/-- Add a directed VM on top of a sound ensemble under the multiset model. As for the legacy
`addVm`, the side conditions are decided by `simp [circuit_norm]` with the VM's definitions
added; the guarantee-channel condition needs `simp +instances` to see through the circuits'
explicit metadata. The definition is in `circuit_norm` as explained at
`SoundEnsembleWith.addTable`. -/
@[circuit_norm]
def addVm (ens : SoundEnsembleWith F (.multiset F) PublicIO) (vm : DirectedVmTables F PublicIO)
    (ne_mem_vm_channel : ∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels
      := by simp [circuit_norm])
    (grts_subset_finished : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished
      := by simp +instances [circuit_norm])
    (reqs_disjoint_finished :
      ∀ channel ∈ ens.finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements
      := by simp [circuit_norm]) :
    SoundVmEnsembleWith F (.multiset F) PublicIO where
  __ := ens.ensemble.addDirectedVm vm
  channels_consistent := by
    intro channel h_mem
    rw [Ensemble.addDirectedVm_channels, List.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · infer_instance
    · exact ens.channels_consistent channel h_mem
  soundVmChannel := ens.ensemble.addDirectedVm_soundVmChannelWith_of_soundChannelsWith
    ens.soundChannelsWith ens.finished_subset ens.verifier_empty vm
    ne_mem_vm_channel grts_subset_finished reqs_disjoint_finished

variable {soundEns : SoundEnsembleWith F (.multiset F) PublicIO} {vm : DirectedVmTables F PublicIO}
  {nmv : ∀ table ∈ soundEns.ensemble.tables, vm.channel.toRaw ∉ table.circuit.channels}
  {gsf : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished ∧
    ∀ table ∈ vm.tables,
      table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished}
  {rdf : ∀ channel ∈ soundEns.finished, channel ∉ vm.verifier.channelsWithRequirements ∧
    ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements}

@[circuit_norm] lemma addVm_tables :
  (soundEns.addVm vm nmv gsf rdf).tables = vm.tables ++ soundEns.tables := rfl
@[circuit_norm] lemma addVm_channels :
  (soundEns.addVm vm nmv gsf rdf).channels = vm.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addVm_verifier :
  (soundEns.addVm vm nmv gsf rdf).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_ensemble :
  (soundEns.addVm vm nmv gsf rdf).ensemble = soundEns.ensemble.addDirectedVm vm := rfl
end SoundEnsembleWith
end Air.Flat
