module

public import Clean.Air.GenerationCorrectness
public import Clean.Air.HonestRows

@[expose] public section

/-!
# Completeness of witness generation

`generate_complete`: if the public and private inputs satisfy a formal ensemble's
`ProverAssumptions`, then generation succeeds, and the witness it returns has the given public
input, satisfies the constraints, and balances every channel.

The theorem covers VM ensembles: a VM channel, on which the verifier pushes the initial state and
pulls the final one, and which a VM component answers with one row per state; and lookup channels,
whose pulls a provider component answers. `CompletePlan` collects what the ensemble's author proves
about a generation plan: how rows behave when honestly generated, which rows satisfy their prover
assumptions, the VM run, and bounds on the number of rows.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-! ### Honest rows -/

/-- `env` holds a row of `component` with `input` whose cells its witness programs computed. -/
structure HonestEnv (component : Component F) (input : Array F) (env : ProverEnvironment F) :
    Prop where
  usesLocalWitnesses : env.UsesLocalWitnesses component.rowOffset component.rowOperations
  input_eq : component.rowInput env.toEnvironment = fromElements (inputRow component.Input input)

/-- The interactions of a row of `component` in `env`. -/
def interactionsIn (component : Component F) (env : Environment F) : List (Interaction F) :=
  component.rowOperations.interactions.map (·.eval env)

/-- A pull of at most one message: an interaction that assumes the channel's guarantees, with
multiplicity `0` or `-1`. -/
def _root_.Interaction.IsUnitPull (interaction : Interaction F) : Prop :=
  interaction.assumeGuarantees ∧ (interaction.mult = 0 ∨ interaction.mult = -1)

/-- The circuit input a row with `input` cells holds. -/
def inputOf (component : Component F) (input : Array F) : component.Input F :=
  fromElements (inputRow component.Input input)

/-! ### Prover data fixed before balancing -/

/-- The initial input of row `row` of a preallocated component. -/
def preallocatedInput (component : Component F) (mode : PreallocatedMode F) (hint : ProverHint F)
    (row : ℕ) : Array F :=
  fixedPrefix component (UInt64.ofNat row) ++ (mode.input.eval (UInt64.ofNat row) hint).toArray

/-- Prover data agreeing with what generation fixes before balancing: every preallocated component
has its padded height, and its rows hold their initial inputs, except in handler columns. -/
def StableData (ens : Ensemble F PublicIO) (plan : GenerationPlan F) (hint : ProverHint F)
    (data : ProverData F) : Prop :=
  ∀ component ∈ ens.tables, ∀ rowPlan mode, (component.circuit.name, rowPlan) ∈ plan.components →
    rowPlan.mode = .preallocated mode →
      let rows := data component.circuit.name component.rowOffset
      rows.size = rowPlan.padding.targetHeight mode.rows.toNat ∧
      ∀ row (hrow : row < rows.size) column (hcolumn : column < component.rowOffset),
        column ∉ mode.handlers.map (·.column) →
          rows[row][column] =
            if row < mode.rows.toNat then (preallocatedInput component mode hint row)[column]?.getD 0
            else rowPlan.padding.input[column]?.getD 0

/-! ### What an ensemble's author proves -/

/-- The interactions of `component` on channel `channel` that pull. -/
def pullsOn (component : Component F) (channel : String) : ℕ :=
  (component.rowOperations.interactions.filter fun interaction =>
    interaction.channel.name == channel && interaction.assumeGuarantees).length

/-- The verifier's interactions on channel `channel` that pull. -/
def verifierPullsOn (ens : Ensemble F PublicIO) (channel : String) : ℕ :=
  (ens.verifierOperations.interactions.filter fun interaction =>
    interaction.channel.name == channel && interaction.assumeGuarantees).length

/-- Some component's row plan answers pulls on `channel`; with `preallocated`, a preallocated one. -/
def Answers (ens : Ensemble F PublicIO) (plan : GenerationPlan F) (preallocated : Bool)
    (channel : String) : Prop :=
  ∃ component ∈ ens.tables, ∃ rowPlan, (component.circuit.name, rowPlan) ∈ plan.components ∧
    (channel, Direction.pull) ∈ rowPlan.mode.handled component ∧
    (preallocated → ∃ mode, rowPlan.mode = .preallocated mode)

/-- An interaction an honest row may add besides the ones its generation mode answers with: none
at all, or a pull of one message that some component answers, off the VM channel. -/
def SideInteraction (ens : Ensemble F PublicIO) (plan : GenerationPlan F) (vmChannel : String)
    (preallocated : Bool) (interaction : Interaction F) : Prop :=
  interaction.mult = 0 ∨
    interaction.IsUnitPull ∧ interaction.channel.name ≠ vmChannel ∧
      Answers ens plan preallocated interaction.channel.name

/-- The VM of an ensemble: the channel on which the verifier pushes the initial state and pulls the
final one, the component answering every pushed state with a row, and the step it implements. -/
structure Vm (ens : FormalEnsemble F PublicIO) (plan : GenerationPlan F) where
  channel : RawChannel F
  component : Component F
  mode : DemandMode F
  padding : Padding F
  mem : component ∈ ens.ensemble.tables
  planned : (component.circuit.name, { mode := .demand mode, padding }) ∈ plan.components
  mode_channel : mode.channel = channel
  mode_direction : mode.direction = .push
  mode_aggregation : mode.aggregation = .perOccurrence
  /-- The state after a state. -/
  next : Array F → Array F
  /-- The states the verifier pushes first and pulls last. -/
  initial : PublicIO F → Array F
  final : PublicIO F → Array F

namespace Vm

variable {ens : FormalEnsemble F PublicIO} {plan : GenerationPlan F}

/-- The input of the VM row answering `state`. -/
def input (vm : Vm ens plan) (state : Array F) : Array F := vm.mode.input.eval state 1

/-- The `index`-th state of the run from the public input's initial state. -/
def state (vm : Vm ens plan) (publicInput : PublicIO F) (index : ℕ) : Array F :=
  vm.next^[index] (vm.initial publicInput)

end Vm

/-- Upper bounds on the rows of every component, from a run of `steps` VM steps: powers of two at
least the minimum height, covering the preallocated rows, the VM rows, and one row per pull a
demand-driven component answers; and few enough that all interactions balance in the field. -/
structure RowBounds (ens : FormalEnsemble F PublicIO) (plan : GenerationPlan F) (vm : Vm ens plan)
    (bound : String → ℕ) (steps : ℕ) : Prop where
  steps_le : steps ≤ bound vm.component.circuit.name
  row_plan : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan,
    (component.circuit.name, rowPlan) ∈ plan.components →
      let rows := bound component.circuit.name
      rows.isPowerOfTwo ∧ rowPlan.padding.minimumRows.toNat ≤ rows ∧ rows ≤ UInt64.size ∧
      match rowPlan.mode with
      | .preallocated mode => mode.rows.toNat ≤ rows
      | .demand mode =>
          component = vm.component ∨
            verifierPullsOn ens.ensemble mode.channel.name +
              (ens.ensemble.tables.map fun other =>
                bound other.circuit.name * pullsOn other mode.channel.name).sum ≤ rows
  interactions : 2 * (ens.ensemble.verifierOperations.interactions.length +
      (ens.ensemble.tables.map fun component =>
        bound component.circuit.name * component.rowOperations.interactions.length).sum) <
    FiniteField.char F

/-- What the author of a VM ensemble proves about a generation plan for witness generation to be
complete. Obligations about rows hold whenever the inputs satisfy the ensemble's prover assumptions,
for every prover data agreeing with what generation fixes before balancing. -/
structure CompletePlan (ens : FormalEnsemble F PublicIO) (plan : GenerationPlan F) where
  valid : ∃ validPlan, plan.validate ens.ensemble = .ok validPlan
  vm : Vm ens plan
  /-- Upper bounds on the rows of every component, from the number of VM steps. -/
  rowBound : ℕ → String → ℕ
  /-- The run reaches the final state, through states the VM rows can answer, within the bounds. -/
  run : ∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
    ∃ steps, vm.state publicInput steps = vm.final publicInput ∧
      (∀ index < steps, vm.state publicInput index ≠ vm.final publicInput) ∧
      (∀ index < steps, ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
        vm.component.circuit.ProverAssumptions
          (inputOf vm.component (vm.input (vm.state publicInput index))) data
          (ens.hint proverInput)) ∧
      RowBounds ens plan vm (rowBound steps) steps
  /-- A VM row pulls its state and pushes the next one; it adds nothing else on the VM channel. -/
  vm_row : ∀ state env, state.size = vm.channel.arity → HonestEnv vm.component (vm.input state) env →
    vm.component.circuit.ProverAssumptions (inputOf vm.component (vm.input state)) env.data
      env.hint →
    (∀ message, netOfInteractions (interactionsIn vm.component env.toEnvironment)
        vm.channel.name message =
      (if message = vm.next state then 1 else 0) - (if message = state then 1 else 0)) ∧
    ∀ interaction ∈ interactionsIn vm.component env.toEnvironment,
      interaction.channel.name ≠ vm.channel.name →
        SideInteraction ens.ensemble plan vm.channel.name false interaction
  /-- The verifier pushes the initial state, pulls the final one, and otherwise pulls single
  messages satisfying their prover guarantees. -/
  verifier : ∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
    ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
      let interactions := ens.ensemble.verifierOperations.interactionValues
        (.fromInput publicInput data)
      (∀ message, netOfInteractions interactions vm.channel.name message =
        (if message = vm.initial publicInput then 1 else 0) -
          (if message = vm.final publicInput then 1 else 0)) ∧
      ∀ interaction ∈ interactions, interaction.channel.name ≠ vm.channel.name →
        SideInteraction ens.ensemble plan vm.channel.name false interaction ∧
          interaction.ProverGuarantees data
  /-- A demand-driven component other than the VM answers the pulls of a message satisfying its
  prover guarantees with rows satisfying their prover assumptions, which push exactly the
  answered count of that message and otherwise pull single messages. Coalescing rows do the same
  for every count. -/
  demand : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan mode,
    (component.circuit.name, rowPlan) ∈ plan.components → rowPlan.mode = .demand mode →
    component ≠ vm.component →
      mode.direction = .pull ∧
      (∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
        ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
        ∀ (message : Vector F mode.channel.arity) (count : ℕ), 0 < count →
          mode.channel.ProverGuarantees message data →
            component.circuit.ProverAssumptions
              (inputOf component (mode.input.eval message.toArray count)) data
              (ens.hint proverInput)) ∧
      (∀ message count env, HonestEnv component (mode.input.eval message count) env →
        component.circuit.ProverAssumptions
          (inputOf component (mode.input.eval message count)) env.data env.hint →
        (∀ other, netOfInteractions (interactionsIn component env.toEnvironment)
            mode.channel.name other = if other = message then (count : F) else 0) ∧
        ∀ interaction ∈ interactionsIn component env.toEnvironment,
          interaction.channel.name ≠ mode.channel.name →
            SideInteraction ens.ensemble plan vm.channel.name false interaction) ∧
      (mode.aggregation = .byMessage →
        ∀ message count count' env env', HonestEnv component (mode.input.eval message count) env →
          HonestEnv component (mode.input.eval message count') env' →
          env.data = env'.data → env.hint = env'.hint →
          ∀ channel ≠ mode.channel.name, ∀ other,
            netOfInteractions (interactionsIn component env.toEnvironment) channel other =
              netOfInteractions (interactionsIn component env'.toEnvironment) channel other)
  /-- A preallocated component's initial rows satisfy their prover assumptions, also with any
  handler column changed. Every handled interaction pushes with the handler column as
  multiplicity, the row's other interactions pull single messages, and neither depends on the
  handler column; every message satisfying the channel's prover guarantees has a row. -/
  preallocated : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan mode,
    (component.circuit.name, rowPlan) ∈ plan.components → rowPlan.mode = .preallocated mode →
    ∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
    ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
      (∀ row < mode.rows.toNat, component.circuit.ProverAssumptions
        (inputOf component (preallocatedInput component mode (ens.hint proverInput) row)) data
        (ens.hint proverInput)) ∧
      (∀ input, ∀ handler ∈ mode.handlers, ∀ value,
        component.circuit.ProverAssumptions (inputOf component input) data (ens.hint proverInput) →
        component.circuit.ProverAssumptions (inputOf component (input.set! handler.column value))
          data (ens.hint proverInput)) ∧
      ∀ handler ∈ mode.handlers, ∃ interaction,
        component.rowOperations.interactions[handler.interaction]? = some interaction ∧
        (∀ message, interaction.channel.ProverGuarantees message data →
          ∃ row < mode.rows.toNat, ∀ env,
            HonestEnv component (preallocatedInput component mode (ens.hint proverInput) row) env →
            env.data = data → env.hint = ens.hint proverInput →
              (interaction.eval env.toEnvironment).msg = message.toArray) ∧
        ∀ input env, HonestEnv component input env → env.data = data →
          env.hint = ens.hint proverInput →
          component.circuit.ProverAssumptions (inputOf component input) data env.hint →
            (interaction.eval env.toEnvironment).assumeGuarantees = false ∧
            (interaction.eval env.toEnvironment).mult = input[handler.column]?.getD 0 ∧
            (∀ index, index ∉ mode.handlers.map (·.interaction) →
              ∀ other ∈ (interactionsIn component env.toEnvironment)[index]?,
                SideInteraction ens.ensemble plan vm.channel.name false other) ∧
            ∀ value env', HonestEnv component (input.set! handler.column value) env' →
              env'.data = data → env'.hint = env.hint →
              (interaction.eval env'.toEnvironment).msg = (interaction.eval env.toEnvironment).msg ∧
              ∀ index ≠ handler.interaction,
                (interactionsIn component env'.toEnvironment)[index]? =
                  (interactionsIn component env.toEnvironment)[index]?
  /-- Padding rows satisfy their prover assumptions and add nothing but single pulls that
  preallocated components answer. -/
  padding : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan,
    (component.circuit.name, rowPlan) ∈ plan.components →
    ∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
    ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
      component.circuit.ProverAssumptions (inputOf component rowPlan.padding.input) data
        (ens.hint proverInput) ∧
      ∀ env, HonestEnv component rowPlan.padding.input env → env.data = data →
        env.hint = ens.hint proverInput →
        ∀ interaction ∈ interactionsIn component env.toEnvironment,
          SideInteraction ens.ensemble plan vm.channel.name true interaction

end Air.Flat.WitnessGeneration

/-! ### Counting single pulls and natural pushes

Over a prime field, a channel message's net multiplicity is the number of single pushes answering
it minus the number of single pulls of it, as long as interactions on the channel are pulls of one
message or pushes of a natural multiplicity. -/

namespace Air.Flat.WitnessGeneration

variable {p : ℕ} [Fact p.Prime] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Interactions on `channel` that are pulls of one message or pushes. -/
def Counted (interactions : List (Interaction (F p))) (channel : String) : Prop :=
  ∀ interaction ∈ interactions, interaction.channel.name = channel →
    interaction.IsUnitPull ∨ interaction.assumeGuarantees = false

/-- The number of single pulls of `message` on `channel`. -/
def pulled (interactions : List (Interaction (F p))) (channel : String) (message : Array (F p)) :
    ℕ :=
  (interactions.filter fun interaction => interaction.channel.name = channel ∧
    interaction.msg = message ∧ interaction.assumeGuarantees ∧ interaction.mult = -1).length

/-- The total multiplicity of pushes of `message` on `channel`. -/
def answered (interactions : List (Interaction (F p))) (channel : String) (message : Array (F p)) :
    ℕ :=
  ((interactions.filter fun interaction => interaction.channel.name = channel ∧
    interaction.msg = message ∧ interaction.assumeGuarantees = false).map
      (·.mult.val)).sum

lemma netOfInteractions_eq_answered_sub_pulled {interactions : List (Interaction (F p))}
    {channel : String} (hcounted : Counted interactions channel) (message : Array (F p)) :
    netOfInteractions interactions channel message =
      (answered interactions channel message : F p) - pulled interactions channel message := by
  induction interactions with
  | nil => simp [netOfInteractions, answered, pulled]
  | cons interaction rest ih =>
      have hrest : Counted rest channel := fun i hi => hcounted i (List.mem_cons_of_mem _ hi)
      rw [netOfInteractions_cons, ih hrest]
      by_cases hmatch : interaction.channel.name = channel ∧ interaction.msg = message
      · rcases hcounted interaction (by simp) hmatch.1 with ⟨hpull, hmult⟩ | hpush
        · rcases hmult with hmult | hmult
          · simp [answered, pulled, hmatch, hpull, hmult]
          · simp [answered, pulled, hmatch, hpull, hmult]
            ring
        · simp [answered, pulled, hmatch, hpush]
          ring
      · have : ¬(interaction.channel.name = channel ∧ interaction.msg = message ∧
            interaction.assumeGuarantees = false) := fun h => hmatch ⟨h.1, h.2.1⟩
        have : ¬(interaction.channel.name = channel ∧ interaction.msg = message ∧
            interaction.assumeGuarantees = true ∧ interaction.mult = -1) :=
          fun h => hmatch ⟨h.1, h.2.1⟩
        simp_all [answered, pulled]

end Air.Flat.WitnessGeneration

/-! ### Canonical demand lists

The generator keeps one entry per channel message and drops entries that cancel, so its demand list
is determined by the net multiplicities it records. -/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

namespace Demand

/-- The channel message a demand is about. -/
def key (demand : Demand F) : String × Array F := (demand.channel, demand.message)

/-- One entry per channel message, none of them zero. -/
def Canonical (demands : List (Demand F)) : Prop :=
  (demands.map key).Nodup ∧ ∀ demand ∈ demands, demand.multiplicity ≠ 0

lemma canonical_nil : Canonical ([] : List (Demand F)) := ⟨List.nodup_nil, by simp⟩

lemma key_mem_add {channel : String} {message : Array F} {multiplicity : F}
    {demands : List (Demand F)} {key' : String × Array F}
    (h : key' ∈ (add channel message multiplicity demands).map Demand.key) :
    key' ∈ demands.map Demand.key ∨ key' = (channel, message) := by
  induction demands with
  | nil =>
      simp only [add] at h
      split at h <;> simp_all [Demand.key]
  | cons current rest ih =>
      simp only [add] at h
      split at h
      · split at h
        · exact .inl (List.mem_cons_of_mem _ h)
        · simp only [List.map_cons, List.mem_cons] at h
          rcases h with h | h
          · exact .inl (by simp [h, Demand.key])
          · exact .inl (List.mem_cons_of_mem _ h)
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact .inl (by simp [h])
        · rcases ih h with h | h
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr h

lemma Canonical.add {demands : List (Demand F)} (hcanonical : Canonical demands)
    (channel : String) (message : Array F) (multiplicity : F) :
    Canonical (Demand.add channel message multiplicity demands) := by
  induction demands with
  | nil =>
      simp only [Demand.add]
      split
      · exact canonical_nil
      · rename_i hzero
        exact ⟨by simp, by simpa using hzero⟩
  | cons current rest ih =>
      obtain ⟨hnodup, hnonzero⟩ := hcanonical
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hrest : Canonical rest := ⟨hnodup.2, fun d hd => hnonzero d (List.mem_cons_of_mem _ hd)⟩
      simp only [Demand.add]
      split
      · rename_i hsame
        simp only [Bool.and_eq_true, beq_iff_eq] at hsame
        split
        · exact hrest
        · rename_i htotal
          refine ⟨?_, ?_⟩
          · simpa [Demand.key] using hnodup
          · intro d hd
            simp only [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact htotal
            · exact hrest.2 d hd
      · rename_i hdifferent
        have ⟨hnodup', hnonzero'⟩ := ih hrest
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, hnodup'⟩
          rcases key_mem_add hmem with hmem | hmem
          · exact hnodup.1 hmem
          · simp only [Demand.key, Prod.mk.injEq] at hmem
            simp [hmem.1, hmem.2] at hdifferent
        · intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hnonzero _ (by simp)
          · exact hnonzero' d hd

lemma Canonical.addInteractions {demands : List (Demand F)} (hcanonical : Canonical demands)
    (interactions : List (Interaction F)) :
    Canonical (Demand.addInteractions demands interactions) := by
  induction interactions generalizing demands with
  | nil => exact hcanonical
  | cons interaction rest ih =>
      simp only [Demand.addInteractions, List.foldl_cons] at ih ⊢
      exact ih (hcanonical.add _ _ _)

lemma Canonical.removeInteractions {demands : List (Demand F)} (hcanonical : Canonical demands)
    (interactions : List (Interaction F)) :
    Canonical (Demand.removeInteractions demands interactions) := by
  induction interactions generalizing demands with
  | nil => exact hcanonical
  | cons interaction rest ih =>
      simp only [Demand.removeInteractions, List.foldl_cons] at ih ⊢
      exact ih (hcanonical.add _ _ _)

/-- In a canonical list, a demand's entry is the net multiplicity of its channel message. -/
lemma Canonical.netOf_eq {demands : List (Demand F)} (hcanonical : Canonical demands)
    {demand : Demand F} (hmem : demand ∈ demands) :
    netOf demands demand.channel demand.message = demand.multiplicity := by
  induction demands with
  | nil => simp at hmem
  | cons current rest ih =>
      obtain ⟨hnodup, hnonzero⟩ := hcanonical
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hrest : Canonical rest := ⟨hnodup.2, fun d hd => hnonzero d (List.mem_cons_of_mem _ hd)⟩
      have hzero : ∀ d ∈ rest, d.key ≠ current.key := fun d hd heq =>
        hnodup.1 (heq ▸ List.mem_map_of_mem hd)
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · have hrestZero : netOf rest demand.channel demand.message = 0 := by
          simp only [netOf]
          rw [List.filter_eq_nil_iff.mpr]
          · rfl
          · intro d hd hmatch
            simp only [decide_eq_true_eq] at hmatch
            exact hzero d hd (by simp [Demand.key, hmatch.1, hmatch.2])
        simp only [netOf, List.filter_cons, and_self, decide_true, ↓reduceIte, List.map_cons,
          List.sum_cons] at hrestZero ⊢
        rw [hrestZero, add_zero]
      · have hne : ¬(current.channel = demand.channel ∧ current.message = demand.message) :=
          fun h => hzero demand hmem (by simp [Demand.key, h.1, h.2])
        simp only [netOf, List.filter_cons, hne, decide_false] at ih ⊢
        exact ih hrest hmem

/-- In a canonical list, a channel message has an entry exactly when its net is nonzero. -/
lemma Canonical.mem_iff {demands : List (Demand F)} (hcanonical : Canonical demands)
    (channel : String) (message : Array F) :
    (channel, message) ∈ demands.map Demand.key ↔ netOf demands channel message ≠ 0 := by
  constructor
  · intro hmem
    obtain ⟨demand, hdemand, hkey⟩ := List.mem_map.mp hmem
    simp only [Demand.key, Prod.mk.injEq] at hkey
    obtain ⟨rfl, rfl⟩ := hkey
    rw [hcanonical.netOf_eq hdemand]
    exact hcanonical.2 demand hdemand
  · intro hnet
    by_contra hmem
    apply hnet
    simp only [netOf]
    rw [List.filter_eq_nil_iff.mpr]
    · rfl
    · intro d hd hmatch
      simp only [decide_eq_true_eq] at hmatch
      exact hmem (List.mem_map.mpr ⟨d, hd, by simp [Demand.key, hmatch.1, hmatch.2]⟩)

/-- Canonical lists whose nonzero nets differ by exactly one channel message differ in length by
one. -/
lemma Canonical.length_succ {demands demands' : List (Demand F)} (hcanonical : Canonical demands)
    (hcanonical' : Canonical demands') {channel : String} {message : Array F}
    (hnet : netOf demands channel message ≠ 0)
    (hsupport : ∀ channel' message', netOf demands' channel' message' ≠ 0 ↔
      netOf demands channel' message' ≠ 0 ∧ (channel', message') ≠ (channel, message)) :
    demands'.length + 1 = demands.length := by
  have hkeys : (demands'.map Demand.key).toFinset =
      (demands.map Demand.key).toFinset.erase (channel, message) := by
    ext ⟨channel', message'⟩
    simp only [List.mem_toFinset, Finset.mem_erase]
    rw [hcanonical'.mem_iff, hcanonical.mem_iff, hsupport]
    tauto
  have hcard := congrArg Finset.card hkeys
  rw [List.toFinset_card_of_nodup hcanonical'.1, Finset.card_erase_of_mem
    (by rw [List.mem_toFinset, hcanonical.mem_iff]; exact hnet),
    List.toFinset_card_of_nodup hcanonical.1] at hcard
  simp only [List.length_map] at hcard
  have hpos : 0 < demands.length := by
    rcases demands with _ | _
    · simp [netOf] at hnet
    · simp
  omega

end Demand

end Air.Flat.WitnessGeneration
