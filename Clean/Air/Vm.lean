import Clean.Air.FlatEnsemble
import Clean.Air.OrderedChannel

variable {F : Type} [Field F] [DecidableEq F]
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

structure VmTables (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : Channel F Message

  tables : List (Component F)
  verifier : GeneralFormalCircuit F PublicIO unit
  verifier_length_zero : ∀ pi, (verifier pi).localLength 0 = 0 := by
    simp only [circuit_norm]

  tables_channel : tables.Forall fun table =>
    ∃ enabled : Expression F, ∃ pull push : Var Message F,
      ⟨ channel,
        [(pullIf (channel:=channel) enabled pull).toRaw,
          (pushIf (channel:=channel) enabled push).toRaw] ⟩ ∈ table.exposedChannels ∧
      ∀ env, table.operations.ConstraintsHold env →
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
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

abbrev VmWitness (vm : VmTables F PublicIO) := EnsembleWitness vm.toEnsemble

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

structure SoundVmEnsemble (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO]
    extends ensemble : Ensemble F PublicIO where
  soundVmChannel : ensemble.SoundVmChannel

namespace SoundVmEnsemble
def toFormal (F : Type) [Field F] [DecidableEq F] (ens : SoundVmEnsemble F PublicIO)
  -- TODO is this useful in practice? Right now, tables don't have access to public input so that's weird
  (ExtraAssumptions : PublicIO F → ProverData F → Prop)
  (extraAssumptionsConsistency : ∀ publicInput data, ExtraAssumptions publicInput data →
    ∀ table ∈ ens.ensemble.tables, ∀ input data, table.circuit.Assumptions input data) :
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
    apply extraAssumptionsConsistency witness.publicInput witness.data extra_assumptions
    exact EnsembleWitness.mem_tables_component_of_mem_tables h_table

variable {ens : SoundVmEnsemble F PublicIO} {ExtraAssumptions : PublicIO F → ProverData F → Prop}
  {eac : ∀ publicInput data, ExtraAssumptions publicInput data →
    ∀ table ∈ ens.tables, ∀ input data, table.circuit.Assumptions input data}

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
    (witness.allTables.flatMap (·.interactionssWith channel)).flatten := by
  simp only [EnsembleWitness.interactionsWith, Table.interactionsWith, Table.interactionssWith]
  rw [List.flatMap_flatMap, List.flatMap_def]

namespace VmTables
variable {vm : VmTables F PublicIO}

@[circuit_norm] lemma toEnsemble_tables (vm : VmTables F PublicIO) :
  vm.toEnsemble.tables = vm.tables := rfl
@[circuit_norm] lemma toEnsemble_verifier (vm : VmTables F PublicIO) :
  vm.toEnsemble.verifier = vm.verifier := rfl

@[circuit_norm] abbrev allTables (vm : VmTables F PublicIO) : List (Component F) :=
  vm.toEnsemble.allTables

private theorem list_forall_mem {α : Type*} {P : α → Prop} :
    ∀ {xs : List α}, xs.Forall P → ∀ {x}, x ∈ xs → P x
  | [], _, _, h => by cases h
  | head :: [], h_forall, _, h_mem => by
      simp only [List.mem_singleton] at h_mem
      subst h_mem
      simpa [List.Forall] using h_forall
  | head :: next :: tail, h_forall, _, h_mem => by
      change P head ∧ (next :: tail).Forall P at h_forall
      simp only [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_mem
      · exact h_forall.1
      · exact list_forall_mem h_forall.2 (by simpa [List.mem_cons] using h_mem)

theorem tables_channel_of_mem (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
    ∃ enabled : Expression F, ∃ pull push : Var vm.Message F,
      ⟨ vm.channel,
        [(pullIf (channel:=vm.channel) enabled pull).toRaw,
          (pushIf (channel:=vm.channel) enabled push).toRaw] ⟩ ∈ table.exposedChannels ∧
      ∀ env, table.operations.ConstraintsHold env →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1 := by
  exact list_forall_mem vm.tables_channel table_mem

noncomputable def step (vm : VmTables F PublicIO) (table : Component F)
    (table_mem : table ∈ vm.tables) : VmStep vm.Message F where
  enabled := (vm.tables_channel_of_mem table_mem).choose
  pull := (vm.tables_channel_of_mem table_mem).choose_spec.choose
  push := (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose

theorem tables_channel' (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
  let step := vm.step table table_mem
  ⟨ vm.channel,
    [(pullIf (channel:=vm.channel) step.enabled step.pull).toRaw,
      (pushIf (channel:=vm.channel) step.enabled step.push).toRaw] ⟩ ∈ table.exposedChannels :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.left

theorem tables_enabled_boolean (vm : VmTables F PublicIO) {table} (table_mem : table ∈ vm.tables) :
    ∀ env, table.operations.ConstraintsHold env →
      Expression.eval env (vm.step table table_mem).enabled = 0 ∨
        Expression.eval env (vm.step table table_mem).enabled = 1 :=
  (vm.tables_channel_of_mem table_mem).choose_spec.choose_spec.choose_spec.right

noncomputable def verifierPull (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose

noncomputable def verifierPush (vm : VmTables F PublicIO) : Var vm.Message F :=
  vm.verifier_channel.choose_spec.choose

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

noncomputable def stepOfAllTables (vm : VmTables F PublicIO) (table : Component F)
    (_ : table ∈ vm.allTables) : VmStep vm.Message F := by
  classical
  exact if h : table = vm.toEnsemble.verifierTable then vm.verifierStep else
    vm.step table (by
      have h_mem := ‹table ∈ vm.allTables›
      simp only [allTables, toEnsemble, Ensemble.allTables, List.mem_cons] at h_mem
      exact h_mem.resolve_left h)

theorem allTables_channel (vm : VmTables F PublicIO) : ∀ (table) (table_mem : table ∈ vm.allTables),
  let step := vm.stepOfAllTables table table_mem
  ⟨ vm.channel,
    [(pullIf (channel:=vm.channel) step.enabled step.pull).toRaw,
      (pushIf (channel:=vm.channel) step.enabled step.push).toRaw] ⟩ ∈ table.exposedChannels := by
  intro table table_mem
  classical
  simp only [circuit_norm, Ensemble.allTables] at table_mem ⊢
  rcases table_mem with rfl | table_mem
  · simp only [circuit_norm, stepOfAllTables]
    exact vm.verifier_channel'
  · by_cases h : table = vm.toEnsemble.verifierTable
    · subst table
      simp only [circuit_norm, stepOfAllTables]
      exact vm.verifier_channel'
    · simp only [circuit_norm, stepOfAllTables, h]
      exact vm.tables_channel' table_mem

/-- Concrete version of VmTables.allTables_channel -/
lemma allTables_channel' (vm : VmTables F PublicIO) {table} (_ : table ∈ vm.allTables) :
  let step := vm.stepOfAllTables table ‹_›
  ⟨ vm.channel.toRaw,
    [(pullIf (channel:=vm.channel) step.enabled step.pull).toRaw,
      (pushIf (channel:=vm.channel) step.enabled step.push).toRaw]
  ⟩ ∈ table.exposedChannels := by
  exact vm.allTables_channel table ‹_›

lemma interactionsWith_eq {vm : VmTables F PublicIO} {table} (_ : table ∈ vm.allTables) :
  let step := vm.stepOfAllTables table ‹_›
  table.operations.interactionsWith vm.channel.toRaw = [
    (pullIf (channel:=vm.channel) step.enabled step.pull).toRaw,
    (pushIf (channel:=vm.channel) step.enabled step.push).toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  apply vm.allTables_channel'

lemma verifierInteractionsWith_eq {vm : VmTables F PublicIO} :
  vm.toEnsemble.verifierTable.operations.interactionsWith vm.channel.toRaw = [
    (pullIf (channel:=vm.channel) vm.verifierStep.enabled vm.verifierStep.pull).toRaw,
    (pushIf (channel:=vm.channel) vm.verifierStep.enabled vm.verifierStep.push).toRaw ] := by
  simpa [stepOfAllTables] using
    interactionsWith_eq (vm:=vm) (table:=vm.toEnsemble.verifierTable)
      Ensemble.mem_allTables_verifierTable
end VmTables

namespace VmWitness
variable {vm : VmTables F PublicIO}
open EnsembleWitness

noncomputable def rowEnabled (witness : VmWitness vm) {table} (_ : table ∈ witness.allTables) (row : Array F) : F :=
  (table.environment row)
    (vm.stepOfAllTables table.component (witness.mem_allTables_component_of_mem_allTables ‹_›)).enabled

noncomputable def rowPull (witness : VmWitness vm) {table} (_ : table ∈ witness.allTables) (row : Array F) : vm.Message F :=
  eval (table.environment row)
    (vm.stepOfAllTables table.component (witness.mem_allTables_component_of_mem_allTables ‹_›)).pull

noncomputable def rowPush (witness : VmWitness vm) {table} (_ : table ∈ witness.allTables) (row : Array F) : vm.Message F :=
  eval (table.environment row)
    (vm.stepOfAllTables table.component (witness.mem_allTables_component_of_mem_allTables ‹_›)).push

noncomputable def verifierEnabled (witness : VmWitness vm) : F :=
  (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.enabled

noncomputable def verifierPull (witness : VmWitness vm) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.pull

noncomputable def verifierPush (witness : VmWitness vm) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.push

lemma interactionValuesWith_eq (witness : VmWitness vm)
    {table} (_ : table ∈ witness.allTables) (row : Array F) :
  table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row) = [
    vm.channel.pullIfValue (witness.rowEnabled ‹_› row) (witness.rowPull ‹_› row),
    vm.channel.pushIfValue (witness.rowEnabled ‹_› row) (witness.rowPush ‹_› row) ] := by
  simp only [circuit_norm, vm.interactionsWith_eq (witness.mem_allTables_component_of_mem_allTables ‹_›),
    rowEnabled, rowPull, rowPush, AbstractInteraction.eval, ProvableType.toElements_eval]

lemma interactionValuesWith_length (witness : VmWitness vm)
    {table} (_ : table ∈ witness.allTables) (row : Array F) :
  (table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row)).length = 2 := by
  simp [witness.interactionValuesWith_eq ‹_› row]

noncomputable def interactionPairs (witness : VmWitness vm) : List (Interaction F × Interaction F) :=
  witness.allTables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row =>
      (vm.channel.pullIfValue (witness.rowEnabled ‹_› row) (witness.rowPull ‹_› row),
        vm.channel.pushIfValue (witness.rowEnabled ‹_› row) (witness.rowPush ‹_› row))

noncomputable def pulls (witness : VmWitness vm) : List (Interaction F) :=
  witness.interactionPairs.map Prod.fst

noncomputable def pushes (witness : VmWitness vm) : List (Interaction F) :=
  witness.interactionPairs.map Prod.snd

def steps (witness : VmWitness vm) : ℕ := witness.tables.map (·.length) |>.sum

@[circuit_norm]
lemma pulls_length {witness : VmWitness vm} : witness.pulls.length = witness.steps + 1 := by
  simp [steps, pulls, interactionPairs, allTables, circuit_norm]

@[circuit_norm]
lemma pushes_length {witness : VmWitness vm} : witness.pushes.length = witness.steps + 1 := by
  simp [steps, pushes, interactionPairs, allTables, circuit_norm]

lemma pulls_mult {witness : VmWitness vm}
    (row_enabled_boolean : ∀ (table) (table_mem : table ∈ witness.allTables), ∀ row ∈ table.table,
      witness.rowEnabled table_mem row = 0 ∨ witness.rowEnabled table_mem row = 1) :
    ∀ pull ∈ witness.pulls, pull.mult = -1 ∨ pull.mult = 0 := by
  simp only [pulls, interactionPairs, List.mem_map, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro pull pair table table_mem row row_mem hpair hpull
  subst pair
  subst pull
  rcases row_enabled_boolean table table_mem row row_mem with h0 | h1
  · right
    change -witness.rowEnabled table_mem row = 0
    rw [h0]
    simp
  · left
    change -witness.rowEnabled table_mem row = -1
    rw [h1]

lemma pushes_mult {witness : VmWitness vm}
    (row_enabled_boolean : ∀ (table) (table_mem : table ∈ witness.allTables), ∀ row ∈ table.table,
      witness.rowEnabled table_mem row = 0 ∨ witness.rowEnabled table_mem row = 1) :
    ∀ push ∈ witness.pushes, push.mult = 1 ∨ push.mult = 0 := by
  simp only [pushes, interactionPairs, List.mem_map, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro push pair table table_mem row row_mem hpair hpush
  subst pair
  subst push
  rcases row_enabled_boolean table table_mem row row_mem with h0 | h1
  · right
    change witness.rowEnabled table_mem row = 0
    exact h0
  · left
    change witness.rowEnabled table_mem row = 1
    exact h1

lemma pushes_assumeRequirements {witness : VmWitness vm} :
    ∀ push ∈ witness.pushes, push.assumeGuarantees = false := by
  simp only [pushes, interactionPairs, List.mem_map, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro push pair table table_mem row row_mem hpair hpush
  subst pair
  subst push
  simp only [circuit_norm]

lemma pair_zero {witness : VmWitness vm} :
    ∀ i (hi_p : i < witness.pulls.length) (hi_q : i < witness.pushes.length),
      witness.pulls[i].mult = 0 ↔ witness.pushes[i].mult = 0 := by
  intro i hi_p hi_q
  have pair_mem : witness.interactionPairs[i]'(by simpa [pulls] using hi_p) ∈ witness.interactionPairs :=
    List.getElem_mem _
  simp only [pulls, pushes, List.getElem_map]
  revert pair_mem
  simp only [interactionPairs, List.mem_flatMap, List.mem_attach, List.mem_map, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro table table_mem row row_mem hpair
  rw [← hpair]
  simp [circuit_norm]

@[circuit_norm]
lemma pulls_channel {witness : VmWitness vm} : ∀ pull ∈ witness.pulls, pull.channel = vm.channel.toRaw := by
  simp only [pulls, interactionPairs, List.mem_map, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro pull pair table table_mem row row_mem hpair hpull
  subst pair
  subst pull
  simp only [circuit_norm]

@[circuit_norm]
lemma pushes_channel {witness : VmWitness vm} : ∀ push ∈ witness.pushes, push.channel = vm.channel.toRaw := by
  simp only [pushes, interactionPairs, List.mem_map, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro push pair table table_mem row row_mem hpair hpush
  subst pair
  subst push
  simp only [circuit_norm]

lemma interactionss_eq_pairs (witness : VmWitness vm) :
  witness.allTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    witness.interactionPairs.map (fun ⟨pull, push⟩ => [pull, push]) := by
  simp only [interactionPairs, List.flatMap_def, List.map_flatten]
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  rw [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro ⟨ table, table_mem ⟩ _
  simp [Table.interactionssWith, witness.interactionValuesWith_eq table_mem]

lemma interactionss_eq_pulls_pushes (witness : VmWitness vm) :
  witness.allTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push]) := by
  rw [interactionss_eq_pairs]
  simp [pulls, pushes, List.zip_map_fst_snd]

lemma interactions_eq_pulls_pushes (witness : VmWitness vm) :
  witness.interactionsWith vm.channel.toRaw =
    (List.zip witness.pulls witness.pushes).flattenPairs := by
  rw [witness.flatMap_interactionsWith_eq_flatten,
    interactionss_eq_pulls_pushes, List.flattenPairs]

lemma mem_zip_pulls_pushes_iff (witness : VmWitness vm) (pull push : Interaction F) :
  (pull, push) ∈ List.zip witness.pulls witness.pushes ↔
    ∃ table ∈ witness.allTables, ∃ row ∈ table.table,
      table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row) = [pull, push] := by
  trans [pull, push] ∈ (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push])
  · simp
  simp [← interactionss_eq_pulls_pushes, Table.interactionssWith]

lemma rowEnabled_boolean_of_constraints {witness : VmWitness vm}
    (constraints : witness.Constraints) :
    ∀ (table : Table F) (table_mem : table ∈ witness.allTables), ∀ row ∈ table.table,
      witness.rowEnabled table_mem row = 0 ∨ witness.rowEnabled table_mem row = 1 := by
  intro table table_mem row row_mem
  classical
  by_cases h_verifier : table.component = vm.toEnsemble.verifierTable
  · right
    simp [rowEnabled, VmTables.stepOfAllTables, h_verifier, VmTables.verifierStep]
    rfl
  · have table_mem_components : table.component ∈ vm.tables := by
      have h_mem := witness.mem_allTables_component_of_mem_allTables table_mem
      simp only [VmTables.toEnsemble, Ensemble.allTables, List.mem_cons] at h_mem
      exact h_mem.resolve_left h_verifier
    have h_constraints := constraints table table_mem row row_mem
    simpa [rowEnabled, VmTables.stepOfAllTables, h_verifier] using
      vm.tables_enabled_boolean table_mem_components (table.environment row) h_constraints

lemma pull_requirements (witness : VmWitness vm)
    (row_enabled_boolean : ∀ (table) (table_mem : table ∈ witness.allTables), ∀ row ∈ table.table,
      witness.rowEnabled table_mem row = 0 ∨ witness.rowEnabled table_mem row = 1) :
    ∀ pull ∈ witness.pulls, pull.Requirements witness.data := by
  simp only [pulls, interactionPairs, List.mem_map, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro pull pair table table_mem row row_mem hpair hpull
  subst pair
  subst pull
  rcases row_enabled_boolean table table_mem row row_mem with h0 | h1
  · simp [circuit_norm, Interaction.Requirements, Channel.toRaw, h0]
  · simp [circuit_norm, Interaction.Requirements, Channel.toRaw, h1]

lemma push_guarantees (witness : VmWitness vm) : ∀ push ∈ witness.pushes, push.Guarantees witness.data := by
  simp only [pushes, interactionPairs, List.mem_map, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro push pair table table_mem row row_mem hpair hpush
  subst pair
  subst push
  simp only [circuit_norm, Interaction.Guarantees]

lemma pulls_length_pos {witness : VmWitness vm} : witness.pulls.length > 0 := by
  simp [pulls_length]
lemma pushes_length_pos {witness : VmWitness vm} : witness.pushes.length > 0 := by
  simp [pushes_length]

lemma pulls_getElem_zero_eq (witness : VmWitness vm) :
    witness.pulls[0]'pulls_length_pos =
      vm.channel.pullIfValue witness.verifierEnabled witness.verifierPull := by
  classical
  simp [pulls, interactionPairs, allTables, circuit_norm, rowEnabled, rowPull,
    verifierEnabled, verifierPull, VmTables.stepOfAllTables]

lemma pushes_getElem_zero_eq (witness : VmWitness vm) :
    witness.pushes[0]'pushes_length_pos =
      vm.channel.pushIfValue witness.verifierEnabled witness.verifierPush := by
  classical
  simp [pushes, interactionPairs, allTables, circuit_norm, rowEnabled, rowPush,
    verifierEnabled, verifierPush, VmTables.stepOfAllTables]

/-- Translation of the VM soundness theorem to VmTables -/
theorem verifier_guarantees_of_requirements_of_requirements_of_guarantees
  [Fact (ringChar F ≠ 2)] (witness : VmWitness vm) :
  -- if the vm interactions with the vm channel are balanced
  BalancedInteractions (witness.interactionsWith vm.channel.toRaw) →
  witness.Constraints →
  -- and for every row, vm channel guarantees imply vm channel requirements
  -- (this will come from constraints + soundness of the existing ensemble)
  (∀ table ∈ witness.allTables, ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees vm.channel.toRaw (table.environment row) →
    table.component.operations.ChannelRequirements vm.channel.toRaw (table.environment row)) →
  -- vm channel verifier requirements imply vm channel verifier guarantees
  witness.verifierTable.ChannelRequirements vm.channel.toRaw →
    witness.verifierTable.ChannelGuarantees vm.channel.toRaw := by
  intro balance witness_constraints constraints
  have row_enabled_boolean := witness.rowEnabled_boolean_of_constraints witness_constraints
  -- prove balance of pulls + pushes
  replace balance : BalancedInteractions (witness.pulls ++ witness.pushes) := by
    rw [witness.interactions_eq_pulls_pushes] at balance
    apply balancedInteractions_of_perm balance
    apply List.zip_flattenPairs_perm <| witness.pushes_length ▸ witness.pulls_length.symm
  -- we fill in the conditions on pulls and pushes in `guarantees_of_requirements_of_requirements_of_guarantees`
  have grts_of_reqs := guarantees_of_requirements_of_requirements_of_guarantees_gated
    vm.channel.toRaw witness.pulls witness.pushes balance witness.data
    (by simp [witness.pulls_length, witness.pushes_length])
    witness.pulls_channel witness.pushes_channel
    (witness.pulls_mult row_enabled_boolean) (witness.pushes_mult row_enabled_boolean)
    witness.pushes_assumeRequirements
    witness.pair_zero
  -- it remains to prove the (grts → reqs) assumption. this is a reformulation of our `constraints`
  have reqs_of_grts : (∀ i (hi : i < (activeInteractions witness.pulls).length),
      (activeInteractions witness.pulls)[i].Guarantees witness.data →
        ((activeInteractions witness.pushes)[i]'(
          activeInteractions_length_eq
            ((witness.pulls_length).trans witness.pushes_length.symm) witness.pair_zero ▸ hi)).Requirements witness.data) := by
    suffices ∀ pair ∈ (witness.pulls.zip witness.pushes), pair.1.Guarantees witness.data → pair.2.Requirements witness.data by
      intro i hi
      exact this _ (activePair_mem_zip
        ((witness.pulls_length).trans witness.pushes_length.symm) witness.pair_zero i hi)
    intro (pull, push) pair_mem
    simp only
    have ⟨ mem_pull, mem_push ⟩ := List.of_mem_zip pair_mem
    have push_grts := witness.push_guarantees push mem_push
    have pull_reqs := witness.pull_requirements row_enabled_boolean pull mem_pull
    rw [witness.mem_zip_pulls_pushes_iff] at pair_mem
    obtain ⟨ table, table_mem, row, row_mem, interactions_eq ⟩ := pair_mem
    suffices (∀ i ∈ [pull, push], i.Guarantees witness.data) → (∀ i ∈ [pull, push], i.Requirements witness.data) by
      simp_all
    rw [← interactions_eq, Operations.interactionValuesWith_eq_map, List.forall_mem_map, List.forall_mem_map]
    have env_data_eq : (table.environment row).data = witness.data := witness.data_eq_of_mem_allTables _ table_mem
    simp only [← env_data_eq, AbstractInteraction.eval_guarantees, AbstractInteraction.eval_requirements,
      Operations.forall_interactionsWith_iff]
    convert constraints table table_mem row row_mem
  -- to get the conclusion about the verifier, we specialize to index 0
  have verifier_enabled_one' :
      Expression.eval (Environment.fromInput witness.publicInput witness.data) vm.verifierStep.enabled = 1 := by
    change Expression.eval (Environment.fromInput witness.publicInput witness.data) (Expression.const (1 : F)) = 1
    rfl
  have active_length_pos : 0 < (activeInteractions witness.pulls).length := by
    simp [activeInteractions, pulls, interactionPairs, allTables, circuit_norm,
      rowEnabled, VmTables.stepOfAllTables, verifier_enabled_one']
  specialize grts_of_reqs reqs_of_grts 0 active_length_pos
  simp [activeInteractions, pulls, pushes, interactionPairs, allTables, circuit_norm,
    rowEnabled, VmTables.stepOfAllTables,
    verifier_enabled_one'] at grts_of_reqs
  have active_push_length_pos : 0 < (activeInteractions witness.pushes).length := by
    rwa [← activeInteractions_length_eq
      ((witness.pulls_length).trans witness.pushes_length.symm) witness.pair_zero]
  simp only [Table.ChannelGuarantees, Table.ChannelRequirements, circuit_norm]
  simp only [← Operations.forall_interactionsWith_iff, vm.verifierInteractionsWith_eq]
  intro hreqs
  simp only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp] at hreqs ⊢
  refine ⟨?_, ?_, ?_⟩
  · let env := Environment.fromInput witness.publicInput witness.data
    have hpush_eval :
        ((pushIf (channel:=vm.channel) vm.verifierStep.enabled vm.verifierStep.push).toRaw.eval env).Requirements env.data :=
        (AbstractInteraction.eval_requirements
          (i:=(pushIf (channel:=vm.channel) vm.verifierStep.enabled vm.verifierStep.push).toRaw)
          (env:=env)).mpr hreqs.2.1
    have hpull_grt := grts_of_reqs (by
      simpa [activeInteractions, pulls, pushes, interactionPairs, allTables, circuit_norm,
        rowEnabled, rowPush, VmTables.stepOfAllTables, verifier_enabled_one', env,
        Channel.eval_pushIf] using hpush_eval)
    have hpull_eval :
        ((pullIf (channel:=vm.channel) vm.verifierStep.enabled vm.verifierStep.pull).toRaw.eval env).Guarantees env.data := by
      simpa [activeInteractions, pulls, pushes, interactionPairs, allTables, circuit_norm,
        rowEnabled, rowPull, VmTables.stepOfAllTables, verifier_enabled_one', env,
        Channel.eval_pullIf] using hpull_grt
    exact AbstractInteraction.eval_guarantees.mp hpull_eval
  · intro h
    cases h
  · intro a h
    cases h
end VmWitness

namespace Ensemble

def addVm (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) : Ensemble F PublicIO where
  channels := vm.channel :: ens.channels
  tables := vm.tables ++ ens.tables
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

@[circuit_norm] lemma addVm_channels (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).channels = vm.channel.toRaw :: ens.channels := rfl
@[circuit_norm] lemma addVm_tables (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).tables = vm.tables ++ ens.tables := rfl
@[circuit_norm] lemma addVm_verifier (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_verifierTable (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).verifierTable = vm.toEnsemble.verifierTable := rfl

/-- split up the witness of `Ensemble.addVm _ _` -/
lemma addVm_witness (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
  (witness : EnsembleWitness (ens.addVm vm)) :
    ∃ (vmWitness : VmWitness vm) (witness' : EnsembleWitness ens),
      witness.tables = vmWitness.tables ++ witness'.tables ∧
      witness.allTables = vmWitness.allTables ++ witness'.tables ∧
      vmWitness.publicInput = witness.publicInput ∧
      witness'.publicInput = witness.publicInput ∧
      vmWitness.data = witness.data ∧
      witness'.data = witness.data := by
  have h_len : (ens.addVm vm).tables.length = vm.tables.length + ens.tables.length := by
    simp [addVm]
  have h_witlen : witness.tables.length = vm.tables.length + ens.tables.length := by
    simp [← witness.same_length, addVm]
  let vmWitness : VmWitness vm := {
    tables := witness.tables.take vm.tables.length
    publicInput := witness.publicInput
    data := witness.data
    same_length := by
      simp [VmTables.toEnsemble, List.length_take, h_witlen]
    same_circuits := by
      intro i hi
      have hi' : i < vm.tables.length := by
        simpa [VmTables.toEnsemble] using hi
      have : i < (ens.addVm vm).tables.length := by
        omega
      rw [List.getElem_take, ← witness.same_circuits _ this]
      simp [VmTables.toEnsemble, addVm, hi']
    same_data := by
      intro table h_table
      apply witness.same_data
      exact List.mem_of_mem_take h_table
  }
  let witness' : EnsembleWitness ens := {
    tables := witness.tables.drop vm.tables.length
    publicInput := witness.publicInput
    data := witness.data
    same_length := by
      simp [List.length_drop, h_witlen]
    same_circuits := by
      intro i hi
      have : vm.tables.length + i < (ens.addVm vm).tables.length := by
        omega
      rw [List.getElem_drop, ← witness.same_circuits _ this]
      simp [addVm]
    same_data := by
      intro table h_table
      apply witness.same_data
      exact List.mem_of_mem_drop h_table
  }
  refine ⟨vmWitness, witness', ?_, ?_, rfl, rfl, rfl, rfl ⟩
  · simp [vmWitness, witness', List.take_append_drop]
  · simp [EnsembleWitness.allTables, EnsembleWitness.verifierTable,
      Ensemble.addVm, VmTables.toEnsemble, vmWitness, witness', List.take_append_drop]

theorem addVm_soundVmChannel_of_soundChannels [Fact (ringChar F ≠ 2)] (ens : Ensemble F PublicIO)
      -- given a sound channels ensemble with a list of finished, consistent channels
    {finished : List (RawChannel F)} (soundChannels : ens.SoundChannels finished)
    (consistent : ∀ channel ∈ finished, channel.Consistent)
    (finished_subset : finished ⊆ ens.channels)
    (verifier_empty : ens.verifier = .empty F PublicIO)
    -- and given a VM channel + tables + verifier
    (vm : VmTables F PublicIO) :
    -- assuming that none of the existing tables interacted with the VM channel
    (∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) →
    -- assuming that the VM tables' and verifier's channelsWithGuarantees are either finished or the VM channel
    (vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished) →
    -- and assuming the VM tables' channelsWithRequirements contain none of the finished ones
    (∀ channel ∈ finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the VM tables satisfies SoundVmChannel
    (ens.addVm vm).SoundVmChannel := by
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
  obtain ⟨ vmWitness, witness', _, allTables_split, publicInput_eq_vm, _, data_eq_vm, data_eq_old ⟩ :=
    addVm_witness ens vm witness
  have data_eq : vmWitness.data = witness'.data := by rw [data_eq_vm, data_eq_old]
  have verifierTable_eq : vmWitness.verifierTable = witness.verifierTable := by
    simp only [circuit_norm, EnsembleWitness.verifierTable, Ensemble.addVm,
      data_eq_vm, publicInput_eq_vm]
  set vmTables := vmWitness.tables
  set vmChannel := vm.channel.toRaw
  -- the vm channel interactions are constrained to vm tables
  have vmInteractions_eq : witness.interactionsWith vmChannel = vmWitness.interactionsWith vmChannel := by
    simp only [EnsembleWitness.interactionsWith, allTables_split, List.flatMap_append]
    suffices witness'.tables.flatMap (·.interactionsWith vmChannel) = [] by
      rw [this, List.append_nil]
    simp only [List.flatMap_eq_nil_iff]
    intro table mem_table
    apply Table.interactionsWith_nil_of_channel_not_mem
    apply not_mem_vm_channel table.component
    exact EnsembleWitness.mem_tables_component_of_mem_tables mem_table
  -- this already lets us supply the balance condition
  have vm_balance := balance vmChannel (by simp [vmChannel, Ensemble.addVm])
  simp only [circuit_norm, vmInteractions_eq] at vm_balance
  -- next, we work on instantiating `requirements_of_partial_guarantees_of_constraints`
  -- which will give us exactly the second hypothesis of `verifier_guarantees`
  -- first, unify channel subset assumptions to all tables
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
    simp only [circuit_norm, VmTables.toEnsemble, EnsembleWitness.allTables]
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
    |>.verifier_guarantees_of_requirements_of_requirements_of_guarantees vm_balance.1 vm_constraints
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
      PartialBalancedChannel (.append vmWitness witness' data_eq) channel := by
    intro channel channel_mem
    apply partialBalancedChannel_of_balancedInteractions
    · convert (balance channel (by simp [Ensemble.addVm, finished_subset channel_mem])).1 using 1
      simp only [circuit_norm]
      rw [EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty]
      simp only [EnsembleWitness.interactionsWith, allTables_split, circuit_norm]
    · convert (balance channel (by simp [Ensemble.addVm, finished_subset channel_mem])).2 using 1
      simp only [circuit_norm]
      rw [EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty]
      simp only [EnsembleWitness.interactionsWith, allTables_split, circuit_norm]
  have partial_balance' : ∀ channel ∈ finished,
      PartialBalancedChannel witness' channel := by
    intro channel' channel_mem'
    apply partialBalancedChannel_of_sublist (partial_balance _ channel_mem')
    use vmWitness.allTables
    simp only [circuit_norm, List.perm_append_comm]
    exact ⟨vm_constraints, reqs_disjoint _ channel_mem'⟩
  -- invoke old tables soundness to get reqs for finished channels from constraints
  -- uses `soundChannels`, `constraints'`, `partial_balance'`
  have finished_reqs : ∀ channel ∈ finished, ∀ table ∈ witness'.allTables,
      table.ChannelRequirements channel := by
    intro channel channel_mem table table_mem
    refine spec_and_guarantees_of_soundChannels (witness := witness'.allTablesWitness)
      ?soundChannels assumptions' constraints' partial_balance' table table_mem
      |>.right channel channel_mem |>.right
    convert soundChannels
    simp [circuit_norm]
  -- invoke `guarantees_of_requirements_append` to get grts for finished channels in vm tables
  have finished_grts : ∀ table ∈ vmWitness.allTables, ∀ channel ∈ finished,
      table.ChannelGuarantees channel := by
    intro table table_mem channel channel_mem
    have : channel.Consistent := consistent channel channel_mem
    apply guarantees_of_requirements_append (ts := vmWitness.allTablesWitness)
      (ss := witness'.allTablesWitness) data_eq vm_constraints (reqs_disjoint _ channel_mem)
      (partial_balance _ channel_mem) (finished_reqs _ channel_mem) _ table_mem
  -- invoke `requirements_of_partial_guarantees_of_constraints` to get per-row grts → reqs for the vm channel,
  -- and use it in `verifier_guarantees`
  have reqs_of_grts (table) (h_table : table ∈ vmWitness.allTables) :=
    table.requirements_of_partial_guarantees_of_constraints (unfinished := vmChannel)
    (vm_assumptions table h_table) (vm_constraints table h_table)
    (grts_subset_all table h_table) (finished_grts table h_table)
  specialize verifier_guarantees reqs_of_grts
  -- massage the conclusion so it matches that of `verifier_guarantees`.
  -- mainly, we need to use (again) that all guarantees apart from the VM channel are satisfied
  rw [EnsembleWitness.verifierGuarantees_iff_verifierTable_guarantees, ← verifierTable_eq,
    Table.guarantees_iff_channelGuarantees]
  simp only [circuit_norm]
  suffices vmWitness.verifierTable.ChannelRequirements vm.channel.toRaw by
    intro channel channel_mem
    replace channel_mem := grts_subset.1 channel_mem
    rcases List.mem_cons.mp channel_mem with rfl | channel_mem
    · exact verifier_guarantees this
    · exact finished_grts _ vmWitness.mem_allTables_verifierTable _ channel_mem
  -- finally, we prove the verifier requirements using `VmTables.verifier_requirements`
  rw [← EnsembleWitness.verifierChannelRequirements_iff]
  apply vm.verifier_requirements
  show vm.toEnsemble.VerifierConstraints vmWitness.publicInput vmWitness.data
  rw [EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
  exact vm_constraints _ vmWitness.mem_allTables_verifierTable
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
      := by simp [circuit_norm]) :
    SoundVmEnsemble F PublicIO where
  __ := ens.ensemble.addVm vm
  soundVmChannel := ens.ensemble.addVm_soundVmChannel_of_soundChannels
    ens.soundChannels ens.finished_consistent ens.finished_subset ens.verifier_empty vm ne_mem_vm_channel
    grts_subset_finished reqs_disjoint_finished

variable {soundEns : SoundEnsemble F PublicIO} {vm : VmTables F PublicIO}
  {nmv : ∀ table ∈ soundEns.ensemble.tables, vm.channel.toRaw ∉ table.circuit.channels}
  {gsf : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished ∧
    ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished}
  {rdf : ∀ channel ∈ soundEns.finished, channel ∉ vm.verifier.channelsWithRequirements ∧
    ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements}

@[circuit_norm] lemma addVm_tables [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).tables = vm.tables ++ soundEns.tables := rfl
@[circuit_norm] lemma addVm_channels [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).channels = vm.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addVm_verifier [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_ensemble [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).ensemble = soundEns.ensemble.addVm vm := rfl

end SoundEnsemble
end Air.Flat
