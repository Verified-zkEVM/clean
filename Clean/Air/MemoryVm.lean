module

public import Clean.Air.ReadWriteMemory
public import Clean.Air.Vm
public import Clean.Utils.ResourceHistory.Grounding

@[expose] public section

/-!
# VMs with read-write memory

A VM with memory is a VM, see `Clean.Air.Vm`, whose steps may access a read-write memory, see
`Clean.Air.ReadWriteMemory`. Every row of a VM table performs one step: it pulls a state from the
VM channel and pushes the next state, and it accesses the memory at most once, at a time that is the
clock of the pushed state. The VM describes the states it reaches after `k` steps with a memory, and
the spec of every VM table says that an enabled row takes a state reached after `k` steps, with a
memory whose value at the accessed address the access reads, to the state it pushes, reached after
`k + 1` steps with the memory that the access writes.

The theorem of this file is that the final state that the verifier pulls is reached from the initial
state it pushes, with the verifier-known initial memory, where the reasoning about the memory is
global and done here, once:
- The VM channel guarantees nothing. Every enabled step increases a clock, so by balance of the VM
  channel the enabled steps form one walk from the initial to the final state, which uses all of
  them, in the order of their clocks. Unlike for `VmTables`, there are no cycles of steps off this
  walk, whose accesses would change the memory.
- By balance of the memory channel, the accesses, ordered by their times, replay the memory from the
  initial records that the memory table pushes, see `Clean.Utils.ResourceHistory.Replay`. Since the
  access times are the clocks of the steps, this is the order of the walk.
- Along the walk, every step reads the value of its address that the replay has at that point, so by
  induction the final state is reached with the memory of the replay, see
  `Clean.Utils.ResourceHistory.Grounding`.
-/

namespace Air.Flat
variable {p : ℕ} [Fact p.Prime]

/-! ## Memory steps -/

/-- An enabled step of a VM with memory: the states it pulls and pushes, and its memory access, if
any, as the record it pulls and the record it pushes. -/
structure MemoryStep (State : Type) (F : Type) where
  pull : State
  push : State
  access : Option (MemoryRecord F × MemoryRecord F)

namespace MemoryStep
variable {State : Type}

/-- The memory before and after a step: its access reads the value of its address in `mem`, and
`mem'` is `mem` with the value it writes. -/
def Updates (step : MemoryStep State (F p)) (mem mem' : F p → F p) : Prop :=
  match step.access with
  | none => mem' = mem
  | some (previous, next) =>
    previous.value = mem previous.address ∧ mem' = Function.update mem next.address next.value

/-- What an enabled step shows locally: it increases the clock; its access, if any, keeps the
address, happens at the clock of the pushed state, and comes after the record it pulls if that
record's time is less than `timeBound`; and it takes a state reached after `k` steps to one reached
after `k + 1` steps, with the memory that it updates. -/
def Valid (clock : State → ℕ) (Reached : ℕ → State → (F p → F p) → Prop) (timeBound : ℕ)
    (step : MemoryStep State (F p)) : Prop :=
  clock step.pull < clock step.push ∧
  (∀ previous next, step.access = some (previous, next) →
    next.address = previous.address ∧ next.time.val = clock step.push ∧
    next.time.val < timeBound ∧
    (previous.time.val < timeBound → previous.time.val < next.time.val)) ∧
  ∀ k mem mem', Reached k step.pull mem → step.Updates mem mem' → Reached (k + 1) step.push mem'
end MemoryStep

omit [Fact p.Prime] in
/-- Mapping a list is mapping its indices. -/
lemma List.map_getElem_finRange {α β : Type} (l : List α) (f : α → β) :
    (List.finRange l.length).map (fun i => f l[i]) = l.map f := by
  rw [← List.ofFn_eq_map]
  conv_rhs => rw [← List.ofFn_getElem (xs := l), List.map_ofFn]
  rfl

omit [Fact p.Prime] in
/-- The pushed or pulled records of a list of memory cells with distinct addresses, at one address,
are the record of the cell at that address, if any. -/
lemma filter_address_eq_find {cells : List (MemoryRecord (F p) × MemoryRecord (F p))}
    (nodup : (cells.map (·.2.address)).Nodup)
    (same_address : ∀ cell ∈ cells, cell.1.address = cell.2.address)
    (record : MemoryRecord (F p) × MemoryRecord (F p) → MemoryRecord (F p))
    (h_record : record = (·.1) ∨ record = (·.2)) (address : F p) :
    (cells.map record).filter (·.address = address) =
      ((cells.find? (·.2.address = address)).map record).toList := by
  induction cells with
  | nil => simp
  | cons cell cells ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at nodup
    have h_address : (record cell).address = cell.2.address := by
      rcases h_record with rfl | rfl
      · exact same_address cell List.mem_cons_self
      · rfl
    rw [List.map_cons, List.filter_cons, List.find?_cons, h_address,
      ih nodup.2 (fun c hc => same_address c (List.mem_cons_of_mem _ hc))]
    by_cases h : cell.2.address = address
    · subst h
      have : cells.find? (·.2.address = cell.2.address) = none := by
        rw [List.find?_eq_none]
        intro c hc h_eq
        exact nodup.1 c hc (of_decide_eq_true h_eq)
      simp [this]
    · simp [h]

open Utils.ResourceHistory in
/--
The main theorem about VMs with memory, in an abstract setting: a list of enabled steps whose pulled
states, and the final state, are a permutation of their pushed states and the initial state, and
memory cells with distinct addresses, each with an initial record at time `0` and a final record,
such that the records that the cells and accesses pull are a permutation of those they push.

If every step is valid, and the initial state is reached with the initial records' values, the final
state is reached after all steps.
-/
theorem exists_reached_of_memoryBalance {State : Type} (clock : State → ℕ)
    (Reached : ℕ → State → (F p → F p) → Prop) (timeBound : ℕ)
    (steps : List (MemoryStep State (F p)))
    (cells : List (MemoryRecord (F p) × MemoryRecord (F p)))
    (initial final : State) (memory : F p → F p)
    (stateBalance : (final :: steps.map (·.pull)).Perm (initial :: steps.map (·.push)))
    (memoryBalance : (cells.map (·.1) ++ (steps.filterMap (·.access)).map (·.1)).Perm
      (cells.map (·.2) ++ (steps.filterMap (·.access)).map (·.2)))
    (cells_nodup : (cells.map (·.2.address)).Nodup)
    (cells_address : ∀ cell ∈ cells, cell.1.address = cell.2.address)
    (cells_initial : ∀ cell ∈ cells, cell.2.time = 0 ∧ cell.2.value = memory cell.2.address)
    (valid : ∀ step ∈ steps, step.Valid clock Reached timeBound)
    (reached : Reached 0 initial memory) :
    ∃ mem, Reached steps.length final mem := by
  classical
  have clock_lt := fun step h_step => (valid step h_step).1
  have access := fun step h_step => (valid step h_step).2.1
  have reached_step := fun step h_step => (valid step h_step).2.2
  -- the steps form a walk from the initial to the final state, which uses every step, in the order
  -- of their clocks
  let edge (i : Fin steps.length) : State × State := (steps[i].pull, steps[i].push)
  have clock_lt' : ∀ i, clock (edge i).1 < clock (edge i).2 :=
    fun i => clock_lt _ (List.getElem_mem _)
  have endpoints : Ranked.EndpointBalanced (↑(List.finRange steps.length)) edge initial final := by
    simp only [Ranked.EndpointBalanced, Multiset.map_coe, Multiset.cons_coe, Multiset.coe_eq_coe,
      edge, List.map_getElem_finRange]
    exact stateBalance.symm
  obtain ⟨path, walk, exhaustive⟩ := exhaustive_of_acyclic _ edge initial final endpoints
    (acyclic_of_strict _ edge (clock · < clock ·) (fun _ => lt_irrefl _) (fun _ _ _ => lt_trans)
      fun i _ => clock_lt' i)
  have path_perm : path.Perm (List.finRange steps.length) := Multiset.coe_eq_coe.mp exhaustive
  have path_ordered := (targets_ordered_of_walk edge (clock · < clock ·) (fun _ _ _ => lt_trans)
    walk fun i _ => clock_lt' i).2
  -- the memory accesses, in the order of the walk, replay the memory from the initial records of
  -- the cells to their final records
  let accesses := steps.filterMap (·.access)
  let accessesOf (i : Fin steps.length) := steps[i].access.toList
  let rows := path.flatMap accessesOf
  let initialRecords (address : F p) := (cells.find? (·.2.address = address)).map (·.2)
  let finalRecords (address : F p) := (cells.find? (·.2.address = address)).map (·.1)
  have rows_perm : rows.Perm accesses := by
    refine (path_perm.flatMap_right accessesOf).trans (List.Perm.of_eq ?_)
    rw [List.flatMap_def, show List.map accessesOf (List.finRange steps.length) =
      steps.map (·.access.toList) from List.map_getElem_finRange steps (·.access.toList)]
    simp only [accesses, List.filterMap_eq_flatMap_toList, List.flatMap_def]
  have mem_accesses {e} : e ∈ accesses ↔ ∃ step ∈ steps, step.access = some e := by
    simp [accesses]
  have accesses_address : ∀ e ∈ accesses, e.2.address = e.1.address := by
    intro e h_e
    obtain ⟨step, h_step, h_access⟩ := mem_accesses.mp h_e
    exact (access step h_step e.1 e.2 h_access).1
  have replay : ResourceReplay MemoryRecord.address id initialRecords rows finalRecords := by
    apply replay_of_balance MemoryRecord.address id (·.time.val < ·.time.val)
      (fun _ => lt_irrefl _) (fun _ _ _ => lt_trans)
    · intro address
      have h := (memoryBalance.filter (·.address = address)).symm
      simp only [List.filter_append] at h
      rw [filter_address_eq_find cells_nodup cells_address _ (.inl rfl),
        filter_address_eq_find cells_nodup cells_address _ (.inr rfl), List.filter_map,
        List.filter_map] at h
      have h_next : (accesses.filter ((·.address = address) ∘ (·.2))) =
          accesses.filter ((·.address = address) ∘ (·.1)) :=
        List.filter_congr fun e h_e => by simp [accesses_address e h_e]
      rw [h_next] at h
      have h_rows := rows_perm.filter ((·.address = address) ∘ (·.1))
      simp only [optionalRecord, accessesAt, id, Multiset.map_coe, Multiset.coe_add,
        Multiset.coe_eq_coe]
      exact ((h_rows.map _).append_left _).trans (h.trans ((h_rows.map _).symm.append_left _))
    · -- the pulled record of an access was pushed by a cell, at time `0`, or by another access,
      -- so its time is less than `timeBound`, and the access is later
      intro e h_e
      obtain ⟨step, h_step, h_access⟩ := mem_accesses.mp (rows_perm.subset h_e)
      obtain ⟨-, -, h_time, h_later⟩ := access step h_step e.1 e.2 h_access
      apply h_later
      have h_pushed := memoryBalance.subset
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.1)) (rows_perm.subset h_e)))
      rcases List.mem_append.mp h_pushed with h | h
      · obtain ⟨cell, h_cell, h_eq⟩ := List.mem_map.mp h
        rw [← h_eq, (cells_initial cell h_cell).1, ZMod.val_zero]
        omega
      · obtain ⟨e', h_e', h_eq⟩ := List.mem_map.mp h
        obtain ⟨step', h_step', h_access'⟩ := mem_accesses.mp h_e'
        rw [← h_eq]
        exact (access step' h_step' _ _ h_access').2.2.1
    · -- the accesses happen at the clocks of their steps, which increase along the walk
      have h_time (i : Fin steps.length) (e) (h_e : e ∈ accessesOf i) :
          e.2.time.val = clock (edge i).2 := by
        have h_access : steps[i].access = some e := by simpa [accessesOf] using h_e
        exact (access _ (List.getElem_mem _) e.1 e.2 h_access).2.1
      intro address
      apply List.Pairwise.filter
      simp only [id, rows, List.pairwise_flatMap]
      refine ⟨fun i _ => ?_, path_ordered.imp fun h_lt e h_e e' h_e' => ?_⟩
      · cases steps[i].access <;> simp [accessesOf, *]
      · rw [h_time _ e h_e, h_time _ e' h_e']
        exact h_lt
  -- along the walk, the steps reach the final state from the initial state and memory, which the
  -- records of the replay represent
  let Represents (records : F p → Option (MemoryRecord (F p))) (mem : F p → F p) :=
    ∀ address record, records address = some record → record.value = mem address
  have refinement : EventRefinement MemoryRecord.address id edge accessesOf id
      (fun (state : ℕ × (F p → F p)) _ next => next.1 = state.1 + 1) (fun _ => True)
      (fun state (s : ℕ × (F p → F p)) => Reached s.1 state s.2)
      (fun records (s : ℕ × (F p → F p)) => Represents records s.2) := by
    constructor
    rintro i - records records' state h_reached h_records h_replay
    simp only [accessesOf, edge, Fin.getElem_fin] at h_replay h_reached ⊢
    have h_step := reached_step steps[(i : ℕ)] (List.getElem_mem _) state.1 state.2
    cases h_access : steps[(i : ℕ)].access with
    | none =>
      rw [h_access] at h_replay
      subst h_replay
      exact ⟨(state.1 + 1, state.2), rfl,
        h_step _ h_reached (by simp [MemoryStep.Updates, h_access]), h_records⟩
    | some e =>
      obtain ⟨previous, next⟩ := e
      simp only [h_access, Option.toList_some, ResourceReplay, id] at h_replay
      obtain ⟨h_current, rfl⟩ := h_replay
      have h_address := (access _ (List.getElem_mem _) previous next h_access).1
      refine ⟨(state.1 + 1, Function.update state.2 next.address next.value), rfl,
        h_step _ h_reached ?_, ?_⟩
      · simp only [MemoryStep.Updates, h_access, and_true]
        exact h_records _ _ h_current
      · intro address record h_record
        by_cases h : address = previous.address
        · subst h
          simp_all
        · rw [Function.update_of_ne h] at h_record
          simp only [Function.update_of_ne (h_address ▸ h)]
          exact h_records _ _ h_record
  have represents : Represents initialRecords memory := by
    intro address record h_record
    simp only [initialRecords, Option.map_eq_some_iff] at h_record
    obtain ⟨cell, h_find, rfl⟩ := h_record
    have h_cell := List.mem_of_find?_eq_some h_find
    have h_address : cell.2.address = address := by simpa using List.find?_some h_find
    rw [(cells_initial cell h_cell).2, h_address]
  obtain ⟨result, h_length, h_reached, -⟩ := ground MemoryRecord.address id edge accessesOf id
    _ _ _ _ refinement (fun state events result => result.1 = state.1 + events.length)
    (fun _ => rfl) (fun _ _ _ _ _ h_next h_rest => by simp_all; omega)
    path initial final initialRecords finalRecords (0, memory) walk replay (fun _ _ => trivial)
    reached represents
  refine ⟨result.2, ?_⟩
  rwa [h_length, zero_add, List.length_map, path_perm.length_eq, List.length_finRange]
    at h_reached

/-! ## VM tables with memory -/

/-- What an enabled row of a table that accesses memory shows: it increases the clock, its access
keeps the address, happens at the clock of the pushed state and comes after the record it pulls, and
it takes a state reached after `k` steps, with a memory whose value at the address it reads, to the
pushed state, reached after `k + 1` steps with the value it writes. -/
def AccessStep (memory : ReadWriteMemory p) {Message : TypeMap} [ProvableType Message]
    (clock : Message (F p) → ℕ)
    (Reached : ℕ → Message (F p) → (F p → F p) → ProverData (F p) → Prop)
    (pull push : Message (F p)) (previous next : MemoryRecord (F p)) (data : ProverData (F p)) :
    Prop :=
  clock pull < clock push ∧ next.address = previous.address ∧ next.time.val = clock push ∧
    memory.Ordered previous.time next.time ∧
    ∀ k mem, Reached k pull mem data → previous.value = mem previous.address →
      Reached (k + 1) push (Function.update mem previous.address next.value) data

variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A VM whose steps may access a read-write memory, at most once per step. -/
structure MemoryVmTables (p : ℕ) [Fact p.Prime] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : Channel (F p) Message
  /-- The VM channel guarantees nothing: what the VM reaches follows from the global argument. -/
  channel_guarantees : ∀ state data, channel.Guarantees state data
  memory : ReadWriteMemory p
  /-- A clock, which every step increases. Accesses happen at the clock of the pushed state. -/
  clock : Message (F p) → ℕ
  /-- The states that the VM reaches after `k` steps from its initial state, with a memory. -/
  Reached : ℕ → Message (F p) → (F p → F p) → ProverData (F p) → Prop
  /-- The tables whose rows perform a step without memory access. -/
  tables : List (Component (F p))
  /-- The tables whose rows perform a step with one memory access. -/
  accessTables : List (Component (F p))
  unique_names : ((tables ++ accessTables).map (·.circuit.name)).Nodup := by simp
  verifier : Verifier.Program (F p) PublicIO
  /-- The final state, which the verifier pulls, as a function of the public input. -/
  final : PublicIO (F p) → Message (F p)

  -- Each row of a table performs one step: if enabled, it pulls a state and pushes the next state,
  -- doesn't access memory, and the table's spec says that the step increases the clock and that the
  -- next state is reached one step after the pulled one, with the same memory.
  tables_channel : tables.Forall fun table =>
    ∃ enabled : Expression (F p), ∃ pull push : Var Message (F p),
      ⟨ channel, [(channel.pulledIf enabled pull).toRaw, (channel.pushedIf enabled push).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      memory.channel.toRaw ∉ table.circuit.channels ∧
      (∀ env, ConstraintsHold.Shallow env table.rowOperations →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1) ∧
      ∀ env, table.circuit.Spec (eval env table.rowInputVar) (table.rowOutput env) env.data →
        Expression.eval env enabled = 1 →
        clock (eval env pull) < clock (eval env push) ∧
        ∀ k mem, Reached k (eval env pull) mem env.data →
          Reached (k + 1) (eval env push) mem env.data

  -- Each row of an access table performs one step with one access: if enabled, it pulls a state and
  -- pushes the next state, pulls the previous record of an address and pushes the next one, and the
  -- table's spec says that this is an `AccessStep`.
  accessTables_channel : accessTables.Forall fun table =>
    ∃ enabled : Expression (F p), ∃ pull push : Var Message (F p),
    ∃ previous next : Var MemoryRecord (F p),
      ⟨ channel, [(channel.pulledIf enabled pull).toRaw, (channel.pushedIf enabled push).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      ⟨ memory.channel, [(memory.channel.pulledIf enabled previous).toRaw,
        (memory.channel.pushedIf enabled next).toRaw] ⟩ ∈
        table.circuit.exposedChannels table.rowInputVar table.rowOffset ∧
      (∀ env, ConstraintsHold.Shallow env table.rowOperations →
        Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1) ∧
      ∀ env, table.circuit.Spec (eval env table.rowInputVar) (table.rowOutput env) env.data →
        Expression.eval env enabled = 1 →
        AccessStep memory clock Reached (eval env pull) (eval env push) (eval env previous)
          (eval env next) env.data

  -- On the VM channel, the public verifier pulls the final state and pushes the initial state,
  -- which is reached after `0` steps with the initial memory. It doesn't access the memory.
  verifier_channel : ∃ pull push : Var Message (F p),
    verifier.circuitOperations.interactionsWith channel.toRaw =
      [(channel.pulled pull).toRaw, (channel.pushed push).toRaw] ∧
    ∀ data : ProverData (F p),
      eval data.publicEnvironment pull = final (data.getPublicInput PublicIO) ∧
      Reached 0 (eval data.publicEnvironment push) memory.initialMemory data
  verifier_memory : memory.channel.toRaw ∉ verifier.channels

instance (vm : MemoryVmTables p PublicIO) : ProvableType vm.Message := vm.provableMessage

/-- The variables of a VM step: its enabled flag, the states it pulls and pushes, and its memory
access, if any, as the records it pulls and pushes. -/
structure MemoryStepVars (Message : TypeMap) [ProvableType Message] (F : Type) where
  enabled : Expression F
  pull : Var Message F
  push : Var Message F
  access : Option (Var MemoryRecord F × Var MemoryRecord F)

namespace MemoryStepVars
variable {Message : TypeMap} [ProvableType Message]

/-- The interactions of a step with the memory channel. -/
def memoryInteractions (memory : ReadWriteMemory p) (step : MemoryStepVars Message (F p)) :
    List (AbstractInteraction (F p)) :=
  match step.access with
  | none => []
  | some (previous, next) =>
    [(memory.channel.pulledIf step.enabled previous).toRaw,
      (memory.channel.pushedIf step.enabled next).toRaw]

/-- The step in an environment. -/
def toStep (step : MemoryStepVars Message (F p)) (env : Environment (F p)) :
    MemoryStep (Message (F p)) (F p) where
  pull := eval env step.pull
  push := eval env step.push
  access := step.access.map fun (previous, next) => (eval env previous, eval env next)
end MemoryStepVars

/-- The value with the given elements, with `0`s in place of missing ones. -/
def ProvableType.fromArray {F : Type} [Zero F] (M : TypeMap) [ProvableType M] (elements : Array F) :
    M F :=
  fromElements (Vector.ofFn fun i => elements.getD i 0)

lemma ProvableType.fromArray_toElements {F : Type} [Zero F] {M : TypeMap} [ProvableType M]
    (x : M F) :
    ProvableType.fromArray M (toElements x).toArray = x := by
  have h : (Vector.ofFn fun i => (toElements x).toArray.getD i 0) = toElements x := by
    ext i hi
    simp
  rw [ProvableType.fromArray, h, ProvableType.fromElements_toElements]

namespace MemoryVmTables
variable (vm : MemoryVmTables p PublicIO)

/-- What a VM table shows about its step. -/
def StepOf (table : Component (F p)) (step : MemoryStepVars vm.Message (F p)) : Prop :=
  ⟨ vm.channel, [(vm.channel.pulledIf step.enabled step.pull).toRaw,
    (vm.channel.pushedIf step.enabled step.push).toRaw] ⟩ ∈ table.exposedChannels ∧
  table.operations.interactionsWith vm.memory.channel.toRaw =
    step.memoryInteractions vm.memory ∧
  (∀ env, ConstraintsHold.Shallow env table.rowOperations →
    Expression.eval env step.enabled = 0 ∨ Expression.eval env step.enabled = 1) ∧
  ∀ env, table.Spec env → Expression.eval env step.enabled = 1 →
    (step.toStep env).Valid vm.clock (vm.Reached · · · env.data) vm.memory.timeBound.toNat

theorem exists_stepOf {table : Component (F p)} (h_table : table ∈ vm.tables ++ vm.accessTables) :
    ∃ step, vm.StepOf table step := by
  rcases List.mem_append.mp h_table with h_table | h_table
  · have h := vm.tables_channel
    rw [List.forall_iff_forall_mem] at h
    obtain ⟨enabled, pull, push, h_exposed, h_channels, h_enabled, h_step⟩ := h table h_table
    refine ⟨⟨enabled, pull, push, none⟩, h_exposed,
      Component.interactionsWith_nil_of_not_mem h_channels, h_enabled, fun env h_spec h_one => ?_⟩
    simp only [Component.Spec, Component.rowInput, ← eval_varFromOffset_valueFromOffset] at h_spec
    obtain ⟨h_clock, h_reached⟩ := h_step env h_spec h_one
    refine ⟨h_clock, by simp [MemoryStepVars.toStep], fun k mem mem' h_mem h_updates => ?_⟩
    simp only [MemoryStep.Updates, MemoryStepVars.toStep, Option.map_none] at h_updates
    exact h_updates ▸ h_reached k mem h_mem
  · have h := vm.accessTables_channel
    rw [List.forall_iff_forall_mem] at h
    obtain ⟨enabled, pull, push, previous, next, h_exposed, h_memory, h_enabled, h_step⟩ :=
      h table h_table
    refine ⟨⟨enabled, pull, push, some (previous, next)⟩, h_exposed,
      Component.interactionsWith_of_exposedChannels h_memory, h_enabled,
      fun env h_spec h_one => ?_⟩
    simp only [Component.Spec, Component.rowInput, ← eval_varFromOffset_valueFromOffset] at h_spec
    obtain ⟨h_clock, h_address, h_time, h_ordered, h_reached⟩ := h_step env h_spec h_one
    refine ⟨h_clock, ?_, fun k mem mem' h_mem h_updates => ?_⟩
    · simp only [MemoryStepVars.toStep, Option.map_some, Option.some.injEq, Prod.mk.injEq]
      rintro _ _ ⟨rfl, rfl⟩
      exact ⟨h_address, h_time, h_ordered⟩
    · simp only [MemoryStep.Updates, MemoryStepVars.toStep, Option.map_some] at h_updates
      obtain ⟨h_value, rfl⟩ := h_updates
      rw [h_address]
      exact h_reached k mem h_mem h_value

/-- The step of a VM table. -/
noncomputable def stepOf {table : Component (F p)}
    (h_table : table ∈ vm.tables ++ vm.accessTables) :
    MemoryStepVars vm.Message (F p) :=
  (vm.exists_stepOf h_table).choose

lemma stepOf_spec {table : Component (F p)} (h_table : table ∈ vm.tables ++ vm.accessTables) :
    vm.StepOf table (vm.stepOf h_table) :=
  (vm.exists_stepOf h_table).choose_spec

/-- The VM without its memory, whose states are all reached. -/
def toVmTables : VmTables (F p) PublicIO where
  channel := vm.channel
  Reached _ _ _ := True
  guarantees_of_reached _ state data _ := vm.channel_guarantees state data
  tables := vm.tables ++ vm.accessTables
  unique_names := vm.unique_names
  verifier := vm.verifier
  final := vm.final
  tables_channel := by
    rw [List.forall_iff_forall_mem]
    intro table h_table
    obtain ⟨h_exposed, -, h_enabled, -⟩ := vm.stepOf_spec h_table
    exact ⟨_, _, _, h_exposed, h_enabled, fun _ _ _ _ _ => trivial⟩
  verifier_channel := by
    obtain ⟨pull, push, h_interactions, h_data⟩ := vm.verifier_channel
    exact ⟨pull, push, h_interactions, fun data => ⟨(h_data data).1, trivial⟩⟩

@[circuit_norm] lemma toVmTables_channel : vm.toVmTables.channel = vm.channel := rfl
@[circuit_norm] lemma toVmTables_tables : vm.toVmTables.tables = vm.tables ++ vm.accessTables := rfl
@[circuit_norm] lemma toVmTables_verifier : vm.toVmTables.verifier = vm.verifier := rfl

/--
What a VM with memory shows about its public input: the final state is reached after `k` steps, with
some memory, for `k` less than a number of interactions that the balance check is sound for.
-/
def FinalReached (balance : Balance (F p)) (publicInput : PublicIO (F p))
    (data : ProverData (F p)) : Prop :=
  ∃ k count mem, balance.fits count ∧ k < count ∧ vm.Reached k (vm.final publicInput) mem data
end MemoryVmTables

/-! ## Adding a VM with memory to an ensemble -/

lemma ReadWriteMemory.name_ne_range_name (memory : ReadWriteMemory p) :
    memory.name ≠ memory.range.name := by
  intro h
  have h := congrArg String.length h
  simp [ReadWriteMemory.range] at h

namespace SoundEnsemble
variable {balance : Balance (F p)}

/-- Add a read-write memory: its range lookup, its channel, which is finished since it guarantees
nothing, and its memory table. -/
def addMemory (ens : SoundEnsemble (F p) PublicIO balance) (memory : ReadWriteMemory p)
    (fresh : memory.name ∉ ens.tables.map (·.circuit.name) ∧
      memory.range.name ∉ ens.tables.map (·.circuit.name) := by simp [circuit_norm])
    (fresh_channels : memory.name ∉ ens.channels.map (·.name) ∧
      memory.range.name ∉ ens.channels.map (·.name) := by simp [circuit_norm]) :
    SoundEnsemble (F p) PublicIO balance :=
  ens.addLookup memory.range fresh.2 fresh_channels.2
  |>.addFinishedChannel memory.channel.toRaw
    (by simp [circuit_norm, memory.name_ne_range_name, fresh_channels.1])
  |>.addTable memory.component (by simp [circuit_norm]) (by simp [circuit_norm])
    (by simp [circuit_norm, memory.name_ne_range_name, fresh.1])

section
variable {ens : SoundEnsemble (F p) PublicIO balance} {memory : ReadWriteMemory p}
  {fresh fresh_channels}

@[circuit_norm] lemma addMemory_tables : (ens.addMemory memory fresh fresh_channels).tables =
    memory.component :: memory.range.component :: ens.tables := rfl
@[circuit_norm] lemma addMemory_channels : (ens.addMemory memory fresh fresh_channels).channels =
    memory.channel.toRaw :: memory.range.channel.toRaw :: ens.channels := rfl
@[circuit_norm] lemma addMemory_finished : (ens.addMemory memory fresh fresh_channels).finished =
    memory.channel.toRaw :: memory.range.channel.toRaw :: ens.finished := rfl
@[circuit_norm] lemma addMemory_verifier :
    (ens.addMemory memory fresh fresh_channels).verifier = ens.verifier := rfl
end

/--
The VM soundness theorem for `MemoryVmTables`, added to a sound ensemble whose first table is the
memory table: the final state is reached after fewer steps than the number of interactions with the
VM channel, with some memory.
-/
theorem addMemoryVm_soundVmChannel (ens : SoundEnsemble (F p) PublicIO balance)
    (vm : MemoryVmTables p PublicIO)
    (fresh_channel : vm.channel.name ∉ ens.channels.map (·.name))
    (grts_subset_finished : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished ∧
      ∀ table ∈ vm.tables ++ vm.accessTables,
        table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished)
    (reqs_unfinished : (∀ channel ∈ vm.verifier.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished) ∧
      ∀ table ∈ vm.tables ++ vm.accessTables, ∀ channel ∈ table.circuit.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: ens.channels ∧ channel ∉ ens.finished)
    (names : ((vm.tables ++ vm.accessTables ++ ens.tables).map (·.circuit.name)).Nodup)
    (memory_table : ∃ rest, ens.tables = vm.memory.component :: rest ∧
      ∀ table ∈ rest, vm.memory.channel.toRaw ∉ table.circuit.channels)
    (memory_channel : vm.memory.channel.toRaw ∈ ens.channels) :
    (ens.ensemble.addVm vm.toVmTables (ens.vmFitsInto vm.toVmTables fresh_channel
      grts_subset_finished reqs_unfinished names)).SoundVmChannel balance
      (vm.FinalReached balance) := by
  intro (witness : VmWitness _ _ _) assumptions constraints fit balanced
  classical
  -- the facts about the VM rows that the sound ensemble gives
  obtain ⟨vm_balance, spec, finished_verifier_guarantees⟩ :=
    ens.ensemble.addVm_vmRows_of_soundChannels ens.soundChannels ens.finished_consistent
      ens.finished_subset vm.toVmTables _
      (fun table h_table h_mem =>
        fresh_channel (List.mem_map.mpr ⟨_, ens.tables_channels table h_table h_mem, rfl⟩))
      grts_subset_finished
      (fun channel h_finished =>
        ⟨fun h => (reqs_unfinished.1 channel h).2 h_finished,
          fun table h_table h => (reqs_unfinished.2 table h_table channel h).2 h_finished⟩)
      witness assumptions constraints fit balanced
  -- the VM channel guarantees nothing, so every VM row satisfies its spec
  have vm_guarantees (ops : Operations (F p)) (env : Environment (F p)) :
      ops.ChannelGuarantees vm.channel.toRaw env := by
    rintro ⟨channel, direction, mult, msg⟩ - h_channel
    simp only at h_channel
    subst h_channel
    exact fun _ _ => vm.channel_guarantees _ _
  refine ⟨?_, ?_⟩
  · rw [Ensemble.verifierGuarantees_iff]
    intro channel h_channel
    rcases List.mem_cons.mp (grts_subset_finished.1 h_channel) with rfl | h_finished
    · exact vm_guarantees _ _
    · exact finished_verifier_guarantees channel h_finished
  -- the steps of the VM rows
  have h_component (table : Table (F p)) (h_table : table ∈ witness.vmTables) :
      table.component ∈ vm.tables ++ vm.accessTables :=
    witness.component_mem_tables_of_mem_vmTables h_table
  have h_step (table : Table (F p)) (h_table : table ∈ witness.vmTables) :
      vm.toVmTables.step (witness.component_mem_tables_of_mem_vmTables h_table) =
        ⟨(vm.stepOf (h_component table h_table)).enabled,
          (vm.stepOf (h_component table h_table)).pull,
          (vm.stepOf (h_component table h_table)).push⟩ :=
    vm.toVmTables.step_eq_of_exposed _ (vm.stepOf_spec _).1
  -- every VM row, with its enabled flag and its step
  let rows : List (F p × MemoryStep (vm.Message (F p)) (F p)) :=
    witness.vmTables.attach.flatMap fun ⟨table, h_table⟩ => table.table.map fun row =>
      (Expression.eval (table.environment row) (vm.stepOf (h_component table h_table)).enabled,
        (vm.stepOf (h_component table h_table)).toStep (table.environment row))
  let steps := (rows.filter (·.1 = 1)).map (·.2)
  have h_rowPairs : witness.rowPairs = rows.map fun (enabled, step) =>
      (vm.channel.pulledIfValue enabled step.pull, vm.channel.pushedIfValue enabled step.push) := by
    simp only [VmWitness.rowPairs, rows, List.map_flatMap, List.map_map]
    congr 1
    funext ⟨table, h_table⟩
    dsimp only
    apply List.map_congr_left
    intro row _
    simp only [VmWitness.rowEnabled, VmWitness.rowPull, VmWitness.rowPush, h_step table h_table,
      MemoryStepVars.toStep]
    rfl
  -- the pulled states and the final state are a permutation of the pushed states and the initial
  -- state
  let initial := ProvableType.fromArray vm.Message
    (toElements (eval witness.data.publicEnvironment vm.toVmTables.verifierPush)).toArray
  let final := ProvableType.fromArray vm.Message
    (toElements (eval witness.data.publicEnvironment vm.toVmTables.verifierPull)).toArray
  have state_balance : (final :: steps.map (·.pull)).Perm (initial :: steps.map (·.push)) := by
    rw [witness.vmInteractionsWith_eq_flattenPairs] at vm_balance
    have perm := perm_of_balancedInteractions _ vm_balance (by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨rfl, rfl, rfl, .inr rfl⟩
      · obtain ⟨table, table_mem, row, row_mem, rfl⟩ := VmWitness.mem_rowPairs_iff.mp ht
        exact ⟨rfl, rfl, rfl, witness.rowEnabled_isBool_of_vmConstraints
          (witness.vmConstraints_of_constraints constraints) table table_mem row row_mem⟩)
    have perm := perm.map (ProvableType.fromArray vm.Message)
    simp only [h_rowPairs, VmWitness.verifierPair, VmWitness.verifierPull, VmWitness.verifierPush,
      List.filter_map, Function.comp_def, ProvableType.fromArray_toElements, List.filter_cons,
      Channel.pulledValue, Channel.pushedValue, Channel.pulledIfValue, Channel.pushedIfValue,
      List.map_cons, List.map_map, decide_true, ite_true] at perm
    simp only [steps, List.map_map, Function.comp_def]
    convert perm
  -- the tables of the ensemble: the VM tables, the memory table, and tables that don't use memory
  obtain ⟨rest, h_tables, h_rest⟩ := memory_table
  have h_old := witness.oldTables_map_component
  rw [h_tables] at h_old
  obtain ⟨memoryTable, others, h_oldTables⟩ : ∃ t ts, witness.oldTables = t :: ts := by
    cases h : witness.oldTables with
    | nil => simp [h] at h_old
    | cons t ts => exact ⟨t, ts, rfl⟩
  rw [h_oldTables, List.map_cons, List.cons.injEq] at h_old
  obtain ⟨h_memoryComponent, h_others⟩ := h_old
  have h_witnessTables : witness.tables = witness.vmTables ++ memoryTable :: others := by
    rw [← h_oldTables, witness.vmTables_append_oldTables]
  -- the records that the memory table pulls and pushes, and those of the accesses
  let cellOf (row : Array (F p)) := vm.memory.component.rowInput (memoryTable.environment row)
  let finalOf (row : Array (F p)) : MemoryRecord (F p) :=
    { address := (cellOf row).address, value := (cellOf row).finalValue,
      time := (cellOf row).finalTime }
  let initialOf (row : Array (F p)) : MemoryRecord (F p) :=
    { address := (cellOf row).address, value := (cellOf row).initialValue, time := 0 }
  let cellPairs := memoryTable.table.map fun row =>
    (vm.memory.channel.pulledIfValue (cellOf row).multiplicity (finalOf row),
      vm.memory.channel.pushedIfValue (cellOf row).multiplicity (initialOf row))
  let accessPairs := rows.flatMap fun (enabled, step) => step.access.toList.map fun access =>
    (vm.memory.channel.pulledIfValue enabled access.1,
      vm.memory.channel.pushedIfValue enabled access.2)
  have h_memoryInteractions : witness.interactionsWith vm.memory.channel.toRaw =
      (accessPairs ++ cellPairs).flattenPairs := by
    have h_verifier : witness.verifierInteractionsWith vm.memory.channel.toRaw = [] := by
      simp only [EnsembleWitness.verifierInteractionsWith, Operations.interactionValuesWith_eq_map,
        List.map_eq_nil_iff, Operations.interactionsWith, List.filter_eq_nil_iff]
      intro i h_i h_channel
      change i ∈ (vm.verifier.operations.circuitOperations).interactions at h_i
      rw [Verifier.Operations.circuitOperations_interactions] at h_i
      exact vm.verifier_memory
        (of_decide_eq_true h_channel ▸ Verifier.Operations.channel_mem_of_mem_interactions h_i)
    have h_others : others.flatMap (·.interactionsWith vm.memory.channel.toRaw) = [] := by
      simp only [List.flatMap_eq_nil_iff]
      intro table h_table
      apply Table.interactionsWith_nil_of_channel_not_mem
      exact h_rest _ (h_others ▸ List.mem_map_of_mem h_table)
    have h_vm : witness.vmTables.flatMap (·.interactionsWith vm.memory.channel.toRaw) =
        accessPairs.flattenPairs := by
      rw [List.flattenPairs_flatMap]
      simp only [rows, List.flatMap_assoc]
      conv_lhs => rw [← List.attach_map_subtype_val witness.vmTables, List.flatMap_map]
      rw [List.flatMap_def, List.flatMap_def]
      congr 1
      apply List.map_congr_left
      rintro ⟨table, h_table⟩ -
      simp only [Table.interactionsWith, List.flatMap_map]
      rw [List.flatMap_def, List.flatMap_def]
      congr 1
      apply List.map_congr_left
      intro row _
      rw [Operations.interactionValuesWith_eq_map, (vm.stepOf_spec (h_component table h_table)).2.1]
      cases h : (vm.stepOf (h_component table h_table)).access with
      | none =>
        simp [MemoryStepVars.memoryInteractions, MemoryStepVars.toStep, h, List.flattenPairs]
      | some access =>
        simp [MemoryStepVars.memoryInteractions, MemoryStepVars.toStep, h, List.flattenPairs,
          Channel.eval_pulledIf, Channel.eval_pushedIf]
        simp [circuit_norm]
    have h_memory :
        memoryTable.interactionsWith vm.memory.channel.toRaw = cellPairs.flattenPairs := by
      simp only [Table.interactionsWith, h_memoryComponent,
        ReadWriteMemory.component_interactionValuesWith, cellPairs, List.flattenPairs, List.map_map,
        List.flatMap_def]
      rfl
    simp only [EnsembleWitness.interactionsWith, h_verifier, List.nil_append,
      Tables.interactionsWith, EnsembleWitness.toTables, h_witnessTables, List.flatMap_append,
      List.flatMap_cons, h_vm, h_memory, h_others, List.append_nil, List.flattenPairs]
    simp
  have memory_balance : BalancedInteractions (witness.interactionsWith vm.memory.channel.toRaw) :=
    witness.balancedChannels_of_balanced fit balanced vm.memory.channel.toRaw
      (by simp [Ensemble.addVm, memory_channel])
  rw [h_memoryInteractions] at memory_balance
  -- the enabled flags of the VM rows and the multiplicities of the memory table are boolean
  have rows_isBool : ∀ x ∈ rows, IsBool x.1 := by
    intro x h_x
    simp only [rows, List.mem_flatMap, List.mem_attach, List.mem_map, true_and] at h_x
    obtain ⟨⟨table, h_table⟩, row, h_row, rfl⟩ := h_x
    have := witness.rowEnabled_isBool_of_vmConstraints
      (witness.vmConstraints_of_constraints constraints) table h_table row h_row
    simpa [VmWitness.rowEnabled, h_step table h_table] using this
  have memoryTable_mem : memoryTable ∈ witness.tables := by
    rw [h_witnessTables]
    exact List.mem_append_right _ List.mem_cons_self
  have cells_isBool : ∀ row ∈ memoryTable.table, IsBool (cellOf row).multiplicity := by
    intro row h_row
    apply vm.memory.component_isBool
    have h_constraints := constraints memoryTable memoryTable_mem row h_row
    rwa [h_memoryComponent] at h_constraints
  have memory_perm := perm_of_balancedInteractions _ memory_balance (by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · simp only [accessPairs, List.mem_flatMap, List.mem_map] at ht
      obtain ⟨x, h_x, access, -, rfl⟩ := ht
      exact ⟨rfl, rfl, rfl, rows_isBool x h_x⟩
    · obtain ⟨row, h_row, rfl⟩ := List.mem_map.mp ht
      exact ⟨rfl, rfl, rfl, cells_isBool row h_row⟩)
  -- the enabled cells of the memory table, as their final and initial records
  let cells := (memoryTable.table.filter fun row => (cellOf row).multiplicity = 1).map fun row =>
    (finalOf row, initialOf row)
  have memory_balance' : (cells.map (·.1) ++ (steps.filterMap (·.access)).map (·.1)).Perm
      (cells.map (·.2) ++ (steps.filterMap (·.access)).map (·.2)) := by
    have h_access := List.filter_flatMap_mult rows (·.1) (fun x =>
        x.2.access.toList.map fun access =>
          (vm.memory.channel.pulledIfValue x.1 access.1,
            vm.memory.channel.pushedIfValue x.1 access.2)) (by
        rintro x t ht
        simp only [List.mem_map] at ht
        obtain ⟨access, -, rfl⟩ := ht
        rfl)
    simp only [List.filter_append] at memory_perm
    simp only [accessPairs] at memory_perm
    rw [h_access] at memory_perm
    have perm := memory_perm.map (ProvableType.fromArray MemoryRecord)
    simp only [List.map_append, List.map_map, List.map_flatMap, List.filter_map, cellPairs,
      Function.comp_def, Channel.pulledIfValue, Channel.pushedIfValue,
      ProvableType.fromArray_toElements] at perm
    have h_steps (f : MemoryRecord (F p) × MemoryRecord (F p) → MemoryRecord (F p)) :
        (steps.filterMap (·.access)).map f =
          (rows.filter (·.1 = 1)).flatMap fun x => x.2.access.toList.map f := by
      simp [steps, List.filterMap_eq_flatMap_toList, List.map_flatMap, List.flatMap_map]
    simp only [cells, List.map_map, Function.comp_def, h_steps]
    convert List.perm_append_comm.trans (perm.trans List.perm_append_comm) using 3 <;>
      exact List.filter_congr fun _ _ => decide_eq_decide.mpr Iff.rfl
  -- row `i` of the memory table holds address `i` and its initial value, so the addresses of the
  -- cells are distinct
  have h_fixed := vm.memory.component_fixedRowsMatch
    (h_memoryComponent ▸ memoryTable.fixed_rows_match)
  have cells_nodup : (cells.map (·.2.address)).Nodup := by
    have h_rows : memoryTable.table.map (fun row => (cellOf row).address) =
        (List.finRange memoryTable.table.length).map
          fun (i : Fin memoryTable.table.length) => ((i : ℕ) : F p) := by
      rw [← List.map_getElem_finRange memoryTable.table fun row => (cellOf row).address]
      exact List.map_congr_left fun i _ => (h_fixed.2 i i.isLt memoryTable.data).1
    have h_nodup : ((List.finRange memoryTable.table.length).map
        fun (i : Fin memoryTable.table.length) => ((i : ℕ) : F p)).Nodup := by
      refine (List.nodup_finRange _).map_on fun i _ j _ h_eq => Fin.ext ?_
      have := vm.memory.size_le
      have h_val := congrArg ZMod.val h_eq
      rwa [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at h_val
    refine (h_rows ▸ h_nodup).sublist ?_
    simp only [cells, List.map_map]
    exact List.filter_sublist.map _
  have cells_address : ∀ cell ∈ cells, cell.1.address = cell.2.address := by
    simp only [cells, List.mem_map, List.mem_filter]
    rintro _ ⟨row, -, rfl⟩
    rfl
  have cells_initial : ∀ cell ∈ cells,
      cell.2.time = 0 ∧ cell.2.value = vm.memory.initialMemory cell.2.address := by
    simp only [cells, List.mem_map, List.mem_filter]
    rintro _ ⟨row, ⟨h_row, -⟩, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h_row
    obtain ⟨h_address, h_initial⟩ := h_fixed.2 i hi memoryTable.data
    have := vm.memory.size_le
    refine ⟨rfl, ?_⟩
    simp only [initialOf, cellOf, Table.environment, h_address, h_initial,
      ReadWriteMemory.initialMemory, ZMod.val_cast_of_lt (show i < p by omega)]
  -- every enabled step is valid
  have valid : ∀ step ∈ steps,
      step.Valid vm.clock (vm.Reached · · · witness.data) vm.memory.timeBound.toNat := by
    simp only [steps, rows, List.mem_map, List.mem_filter, List.mem_flatMap, List.mem_attach,
      true_and]
    rintro _ ⟨_, ⟨⟨⟨table, h_table⟩, row, h_row, rfl⟩, h_enabled⟩, rfl⟩
    have h_data : (table.environment row).data = witness.data :=
      witness.same_data table (List.mem_of_mem_take h_table)
    have := (vm.stepOf_spec (h_component table h_table)).2.2.2 (table.environment row)
      (spec table h_table row h_row (vm_guarantees _ _)) (of_decide_eq_true h_enabled)
    rwa [h_data] at this
  -- the verifier pushes the initial state with the initial memory, and pulls the final state
  obtain ⟨pull, push, h_verifier, h_data⟩ := vm.verifier_channel
  have h_initial : initial = eval witness.data.publicEnvironment push := by
    rw [← (vm.toVmTables.verifierPull_eq h_verifier).2]
    exact ProvableType.fromArray_toElements _
  have h_final : final = vm.final witness.publicInput := by
    change final = vm.toVmTables.final witness.publicInput
    rw [← witness.data_getPublicInput, ← vm.toVmTables.eval_verifierPull]
    exact ProvableType.fromArray_toElements _
  obtain ⟨mem, reached⟩ := exists_reached_of_memoryBalance vm.clock
    (vm.Reached · · · witness.data) vm.memory.timeBound.toNat steps cells initial final
    vm.memory.initialMemory state_balance memory_balance' cells_nodup cells_address
    cells_initial valid (h_initial ▸ (h_data witness.data).2)
  -- there are more interactions with the VM channel than enabled steps
  refine ⟨steps.length, (witness.interactionsWith vm.toVmTables.channel.toRaw).length, mem,
    fit _ (by simp [Ensemble.addVm]), ?_, h_final ▸ reached⟩
  have h_steps : steps.length ≤ witness.steps := by
    rw [← witness.length_rowPairs, h_rowPairs, List.length_map, List.length_map]
    exact List.length_filter_le _ _
  have fresh_channel : vm.toVmTables.channel.name ∉ ens.channels.map (·.name) := fresh_channel
  rw [witness.interactionsWith_eq_vmInteractionsWith
      (fun table h_table h_mem =>
        fresh_channel (List.mem_map.mpr ⟨_, ens.tables_channels table h_table h_mem, rfl⟩)),
    witness.length_vmInteractionsWith]
  omega

/-- Add a VM with memory on top of a sound ensemble: the memory, see `addMemory`, then the VM. See
`vmFitsInto` for the conditions on the VM's channels. -/
def addMemoryVm (ens : SoundEnsemble (F p) PublicIO balance) (vm : MemoryVmTables p PublicIO)
    (fresh : vm.memory.name ∉ ens.tables.map (·.circuit.name) ∧
      vm.memory.range.name ∉ ens.tables.map (·.circuit.name) := by simp [circuit_norm])
    (fresh_channels : vm.memory.name ∉ ens.channels.map (·.name) ∧
      vm.memory.range.name ∉ ens.channels.map (·.name) := by simp [circuit_norm])
    (fresh_channel : vm.channel.name ∉
      (ens.addMemory vm.memory fresh fresh_channels).channels.map (·.name) :=
      by simp [circuit_norm])
    (grts_subset_finished : vm.verifier.channelsWithGuarantees ⊆
        vm.channel.toRaw :: (ens.addMemory vm.memory fresh fresh_channels).finished ∧
      ∀ table ∈ vm.tables ++ vm.accessTables, table.circuit.channelsWithGuarantees ⊆
        vm.channel.toRaw :: (ens.addMemory vm.memory fresh fresh_channels).finished
      := by simp [circuit_norm])
    (reqs_unfinished : (∀ channel ∈ vm.verifier.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: (ens.addMemory vm.memory fresh fresh_channels).channels ∧
        channel ∉ (ens.addMemory vm.memory fresh fresh_channels).finished) ∧
      ∀ table ∈ vm.tables ++ vm.accessTables, ∀ channel ∈ table.circuit.channelsWithRequirements,
        channel ∈ vm.channel.toRaw :: (ens.addMemory vm.memory fresh fresh_channels).channels ∧
        channel ∉ (ens.addMemory vm.memory fresh fresh_channels).finished
      := by simp [circuit_norm])
    (names : ((vm.tables ++ vm.accessTables ++
        (ens.addMemory vm.memory fresh fresh_channels).tables).map (·.circuit.name)).Nodup :=
      by simp [circuit_norm]) :
    SoundVmEnsemble (F p) PublicIO balance where
  __ := (ens.addMemory vm.memory fresh fresh_channels).addVm vm.toVmTables fresh_channel
    grts_subset_finished reqs_unfinished names
  FinalReached := vm.FinalReached balance
  soundVmChannel := addMemoryVm_soundVmChannel _ vm fresh_channel grts_subset_finished
    reqs_unfinished names
    ⟨_, rfl, fun table h_table h_mem => fresh_channels.1 (by
      have h_channels := (ens.addLookup vm.memory.range fresh.2 fresh_channels.2).tables_channels
        table h_table h_mem
      simp only [circuit_norm, List.mem_cons] at h_channels
      rcases h_channels with h_eq | h_channel
      · exact absurd h_eq.1 vm.memory.name_ne_range_name
      · exact List.mem_map.mpr ⟨_, h_channel, rfl⟩)⟩
    (List.mem_cons_self ..)

section
variable {ens : SoundEnsemble (F p) PublicIO balance} {vm : MemoryVmTables p PublicIO}
  {fresh fresh_channels fresh_channel grts reqs names}

@[circuit_norm] lemma addMemoryVm_tables :
    (ens.addMemoryVm vm fresh fresh_channels fresh_channel grts reqs names).tables =
      vm.tables ++ vm.accessTables ++
        vm.memory.component :: vm.memory.range.component :: ens.tables := rfl
@[circuit_norm] lemma addMemoryVm_channels :
    (ens.addMemoryVm vm fresh fresh_channels fresh_channel grts reqs names).channels =
      vm.channel.toRaw :: vm.memory.channel.toRaw :: vm.memory.range.channel.toRaw ::
        ens.channels := rfl
@[circuit_norm] lemma addMemoryVm_verifier :
    (ens.addMemoryVm vm fresh fresh_channels fresh_channel grts reqs names).verifier =
      vm.verifier := rfl
@[circuit_norm] lemma addMemoryVm_finalReached :
    (ens.addMemoryVm vm fresh fresh_channels fresh_channel grts reqs names).FinalReached =
      vm.FinalReached balance := rfl
end
end SoundEnsemble
end Air.Flat
