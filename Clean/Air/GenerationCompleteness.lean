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

/-- A row computed by honest witness generation is honest. -/
lemma honestEnv_rowEnvironment (component : Component F) (data : ProverData F)
    (hint : ProverHint F) (input : Array F) (hsize : input.size = component.rowOffset)
    (hbelow : flatReadsBelow component.rowOffset component.rowOperations.toFlat = true) :
    HonestEnv component input (rowEnvironment (honestRow component data hint input) data hint) where
  usesLocalWitnesses := by
    rw [ProverEnvironment.usesLocalWitnesses_iff_flat]
    have := honestWitgen_usesLocalWitnesses data hint component.rowOperations.toFlat input
      (by rw [hsize]; exact hbelow)
    rw [hsize] at this
    exact this
  input_eq := by
    change valueFromOffset component.Input 0
      (Environment.fromArray (honestRow component data hint input) data) = _
    rw [valueFromOffset_fromArray, inputRow_honestRow component data hint input hsize]

/-- A property of the interactions of every honestly generated row of `circuit`, stated like
completeness: for every environment whose local witnesses are honest and every input satisfying
the circuit's prover assumptions. -/
def RowInteractions {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output)
    (P : Input F → ProverEnvironment F → List (Interaction F) → Prop) : Prop :=
  ∀ offset (env : ProverEnvironment F) (input_var : Var Input F),
    env.UsesLocalWitnessesCompleteness offset ((circuit.main input_var).operations offset) →
    ∀ input : Input F, eval env input_var = input →
    circuit.ProverAssumptions input env.data env.hint →
    P input env (((circuit.main input_var).operations offset).interactions.map
      (·.eval env.toEnvironment))

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

end Air.Flat.WitnessGeneration

namespace Air.Flat.WitnessGeneration

variable {p : ℕ} [Fact p.Prime] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- The VM of an ensemble: the channel on which the verifier pushes the initial state and pulls the
final one, the component answering every pushed state with a row, and the step it implements. -/
structure Vm (ens : FormalEnsemble (F p) PublicIO) (plan : GenerationPlan (F p)) where
  channel : RawChannel (F p)
  component : Component (F p)
  mode : DemandMode (F p)
  padding : Padding (F p)
  declared : channel ∈ ens.ensemble.channels
  mem : component ∈ ens.ensemble.tables
  planned : (component.circuit.name, { mode := .demand mode, padding }) ∈ plan.components
  mode_channel : mode.channel = channel
  mode_direction : mode.direction = .push
  mode_aggregation : mode.aggregation = .perOccurrence
  /-- No component answers pulls on the VM channel: the verifier's pull of the final state waits
  for the VM. -/
  no_pull_handler : ∀ other ∈ ens.ensemble.tables, ∀ rowPlan,
    (other.circuit.name, rowPlan) ∈ plan.components →
      (channel.name, Direction.pull) ∉ rowPlan.mode.handled other
  /-- The state after a state. -/
  next : Array (F p) → Array (F p)
  /-- The states the verifier pushes first and pulls last. -/
  initial : PublicIO (F p) → Array (F p)
  final : PublicIO (F p) → Array (F p)

namespace Vm

variable {ens : FormalEnsemble (F p) PublicIO} {plan : GenerationPlan (F p)}

/-- The input of the VM row answering `state`. -/
def input (vm : Vm ens plan) (state : Array (F p)) : Array (F p) := vm.mode.input.eval state 1

/-- The `index`-th state of the run from the public input's initial state. -/
def state (vm : Vm ens plan) (publicInput : PublicIO (F p)) (index : ℕ) : Array (F p) :=
  vm.next^[index] (vm.initial publicInput)

end Vm

/-- Upper bounds on the rows of every component, from a run of `steps` VM steps: powers of two at
least the minimum height, covering the preallocated rows, the VM rows, and one row per pull a
demand-driven component answers; and few enough that all interactions balance in the field. -/
structure RowBounds (ens : FormalEnsemble (F p) PublicIO) (plan : GenerationPlan (F p)) (vm : Vm ens plan)
    (bound : String → ℕ) (steps : ℕ) : Prop where
  steps_le : steps ≤ bound vm.component.circuit.name
  row_plan : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan,
    (component.circuit.name, rowPlan) ∈ plan.components →
      let rows := bound component.circuit.name
      (∃ k, rows = 2 ^ k) ∧ rowPlan.padding.minimumRows.toNat ≤ rows ∧ rows ≤ UInt64.size ∧
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
    FiniteField.char (F p)

/-- What the author of a VM ensemble proves about a generation plan for witness generation to be
complete. Obligations about rows hold whenever the inputs satisfy the ensemble's prover assumptions,
for every prover data agreeing with what generation fixes before balancing. -/
structure CompletePlan (ens : FormalEnsemble (F p) PublicIO) (plan : GenerationPlan (F p)) where
  valid : ∃ validPlan, plan.validate ens.ensemble = .ok validPlan
  /-- No cells are defined by reads. -/
  no_lazy : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan mode,
    (component.circuit.name, rowPlan) ∈ plan.components → rowPlan.mode = .preallocated mode →
      mode.lazyColumns = []
  vm : Vm ens plan
  /-- Upper bounds on the rows of every component, from the number of VM steps. -/
  rowBound : ℕ → String → ℕ
  /-- Demand-driven components other than the VM answer pulls only of such components of lower
  rank, so that answering pulls ends. -/
  rank : String → ℕ
  acyclic : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan mode,
    (component.circuit.name, rowPlan) ∈ plan.components → rowPlan.mode = .demand mode →
    component ≠ vm.component → ∀ other ∈ ens.ensemble.tables, ∀ otherPlan otherMode,
      (other.circuit.name, otherPlan) ∈ plan.components → otherPlan.mode = .demand otherMode →
      other ≠ vm.component → 0 < pullsOn other mode.channel.name →
        rank other.circuit.name < rank component.circuit.name
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
  vm_row : ∀ state, state.size = vm.channel.arity →
    RowInteractions vm.component.circuit fun input _ interactions =>
      input = inputOf vm.component (vm.input state) →
      (∀ message, netOfInteractions interactions vm.channel.name message =
        (if message = vm.next state then 1 else 0) - (if message = state then 1 else 0)) ∧
      ∀ interaction ∈ interactions, interaction.channel.name ≠ vm.channel.name →
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
  answered count of that message and otherwise pull single messages. Coalescing rows pull the
  same for every count. -/
  demand : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan mode,
    (component.circuit.name, rowPlan) ∈ plan.components → rowPlan.mode = .demand mode →
    component ≠ vm.component →
      mode.channel ∈ ens.ensemble.channels ∧ mode.direction = .pull ∧
      (∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
        ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
        ∀ (message : Vector (F p) mode.channel.arity) (count : ℕ), 0 < count →
          mode.channel.ProverGuarantees message data →
            component.circuit.ProverAssumptions
              (inputOf component (mode.input.eval message.toArray count)) data
              (ens.hint proverInput)) ∧
      (∀ message count, RowInteractions component.circuit fun input _ interactions =>
        input = inputOf component (mode.input.eval message count) →
        (∀ other, netOfInteractions interactions mode.channel.name other =
          if other = message then (count : F p) else 0) ∧
        ∀ interaction ∈ interactions, interaction.channel.name ≠ mode.channel.name →
          SideInteraction ens.ensemble plan vm.channel.name false interaction) ∧
      (mode.aggregation = .byMessage → ∀ message, ∃ nets : ProverData (F p) → ProverHint (F p) →
          String → Array (F p) → F p, ∀ count,
        RowInteractions component.circuit fun input env interactions =>
          input = inputOf component (mode.input.eval message count) →
          ∀ channel ≠ mode.channel.name, ∀ other,
            netOfInteractions interactions channel other = nets env.data env.hint channel other)
  /-- A preallocated component's initial rows satisfy their prover assumptions, also with any
  handler column changed. Its rows interact as `interactionsOf` their input: every handled
  interaction pushes on a declared channel with the handler column as multiplicity, the other
  interactions pull single messages of channels the component does not answer, and changing a
  handler column changes nothing else; every message satisfying the channel's prover guarantees
  has a row. -/
  preallocated : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan mode,
    (component.circuit.name, rowPlan) ∈ plan.components → rowPlan.mode = .preallocated mode →
    (∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
      ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
        (∀ row < mode.rows.toNat, component.circuit.ProverAssumptions
          (inputOf component (preallocatedInput component mode (ens.hint proverInput) row)) data
          (ens.hint proverInput)) ∧
        (∀ handler ∈ mode.handlers, ∀ row < mode.rows.toNat,
          (preallocatedInput component mode (ens.hint proverInput) row)[handler.column]?.getD 0 =
            0) ∧
        ∀ input, ∀ handler ∈ mode.handlers, ∀ value,
          component.circuit.ProverAssumptions (inputOf component input) data
            (ens.hint proverInput) →
          component.circuit.ProverAssumptions (inputOf component (input.set! handler.column value))
            data (ens.hint proverInput)) ∧
    ∃ interactionsOf : Array (F p) → ProverData (F p) → ProverHint (F p) → List (Interaction (F p)),
      (∀ input, RowInteractions component.circuit fun inputValue env interactions =>
        inputValue = inputOf component input →
          interactions = interactionsOf input env.data env.hint) ∧
      (∀ input data hint, ∀ index, index ∉ mode.handlers.map (·.interaction) →
        ∀ other ∈ (interactionsOf input data hint)[index]?,
          SideInteraction ens.ensemble plan vm.channel.name false other ∧
            (other.channel.name, Direction.pull) ∉ rowPlan.mode.handled component) ∧
      ∀ handler ∈ mode.handlers, ∃ channel ∈ ens.ensemble.channels,
        (∀ input data hint, ∃ interaction ∈ (interactionsOf input data hint)[handler.interaction]?,
          interaction.channel = channel ∧ interaction.assumeGuarantees = false ∧
            interaction.mult = input[handler.column]?.getD 0) ∧
        (∀ input value data hint,
          ((interactionsOf (input.set! handler.column value) data hint)[handler.interaction]?.map
            (·.msg)) = (interactionsOf input data hint)[handler.interaction]?.map (·.msg)) ∧
        (∀ input value data hint, ∀ index ≠ handler.interaction,
          (interactionsOf (input.set! handler.column value) data hint)[index]? =
            (interactionsOf input data hint)[index]?) ∧
        ∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
          ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
          ∀ message : Vector (F p) channel.arity, channel.ProverGuarantees message data →
            ∃ row < mode.rows.toNat, ∃ interaction ∈ (interactionsOf
              (preallocatedInput component mode (ens.hint proverInput) row) data
              (ens.hint proverInput))[handler.interaction]?, interaction.msg = message.toArray
  /-- Padding rows satisfy their prover assumptions and add nothing but single pulls that
  preallocated components answer. -/
  padding : ∀ component ∈ ens.ensemble.tables, ∀ rowPlan,
    (component.circuit.name, rowPlan) ∈ plan.components →
    (∀ publicInput proverInput, ens.ProverAssumptions publicInput proverInput →
      ∀ data, StableData ens.ensemble plan (ens.hint proverInput) data →
        component.circuit.ProverAssumptions (inputOf component rowPlan.padding.input) data
          (ens.hint proverInput)) ∧
    RowInteractions component.circuit fun input _ interactions =>
      input = inputOf component rowPlan.padding.input →
        ∀ interaction ∈ interactions, SideInteraction ens.ensemble plan vm.channel.name true interaction

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

/-! ### What validation guarantees -/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

@[simp] lemma orElse_eq_none {α : Type} (a b : Option α) : (a <|> b) = none ↔ a = none ∧ b = none := by
  cases a <;> simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

@[simp] lemma check_eq_none (condition : Bool) (error : PlanError) :
    check condition error = none ↔ condition = true := by
  cases condition <;> simp [check]

/-- What validation guarantees about one component's row plan. -/
structure RowPlanValid (component : Component F) (rowPlan : RowPlan F) : Prop where
  padding_width : rowPlan.padding.input.size = component.rowOffset
  fixed : ∀ fixed, component.fixedColumns = some fixed → ∃ mode,
    rowPlan.mode = .preallocated mode ∧ mode.rows = fixed.height ∧
      rowPlan.padding.targetHeight fixed.height.toNat = fixed.height.toNat
  demand : ∀ mode, rowPlan.mode = .demand mode →
    mode.input.cells.length = component.rowOffset ∧
      ∀ index, .message index ∈ mode.input.cells → index < mode.channel.arity
  preallocated : ∀ mode, rowPlan.mode = .preallocated mode →
    component.fixedWidth + mode.input.width = component.rowOffset ∧
      ∀ handler ∈ mode.handlers, handler.interaction < component.rowOperations.interactions.length ∧
        component.fixedWidth ≤ handler.column ∧ handler.column < component.rowOffset

lemma rowPlanValid_of_error_eq_none {component : Component F} {rowPlan : RowPlan F}
    (h : rowPlanError component rowPlan = none) : RowPlanValid component rowPlan := by
  simp only [rowPlanError, orElse_eq_none, check_eq_none, beq_iff_eq] at h
  obtain ⟨hpadding, hfixed, hmode⟩ := h
  refine ⟨hpadding, ?_, ?_, ?_⟩
  · intro fixed hcolumns
    rw [hcolumns] at hfixed
    rcases hrow : rowPlan.mode with mode | mode <;> rw [hrow] at hfixed
    · simp at hfixed
    · simp only [orElse_eq_none, check_eq_none, beq_iff_eq] at hfixed
      exact ⟨mode, rfl, hfixed.1, hfixed.2⟩
  · intro mode hrow
    rw [hrow] at hmode
    simp only [orElse_eq_none, check_eq_none, beq_iff_eq, List.findSome?_eq_none_iff] at hmode
    refine ⟨hmode.1, fun index hindex => ?_⟩
    have := hmode.2 _ hindex
    simpa using this
  · intro mode hrow
    rw [hrow] at hmode
    simp only [orElse_eq_none, check_eq_none, beq_iff_eq, List.findSome?_eq_none_iff,
      Bool.and_eq_true, decide_eq_true_eq] at hmode
    exact ⟨hmode.1, fun handler hhandler => ⟨(hmode.2.1 handler hhandler).1,
      (hmode.2.1 handler hhandler).2.1, (hmode.2.1 handler hhandler).2.2⟩⟩

end Air.Flat.WitnessGeneration

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- What validation guarantees about a prover-data read: it targets a stable cell of a preallocated
component that padding does not extend, or a lazy cell through a read step. -/
structure DataReadValid (components : List (Component F)) (rowPlans : List (RowPlan F))
    (read : DataRead) : Prop where
  target : ∃ target rowPlan mode,
    (components.zip rowPlans).find? (fun (target, _) => target.circuit.name == read.key) =
      some (target, rowPlan) ∧
    read.width = target.rowOffset ∧ rowPlan.mode = .preallocated mode ∧
    read.column ∉ mode.handlers.map (·.column) ∧
    (read.defining = false → read.column ∉ mode.lazyColumns) ∧
    rowPlan.padding.targetHeight mode.rows.toNat = mode.rows.toNat

lemma dataReadValid_of_error_eq_none {components : List (Component F)}
    {rowPlans : List (RowPlan F)} {component : Component F} {operation : ℕ} {read : DataRead}
    (h : dataReadError components rowPlans component operation read = none) :
    DataReadValid components rowPlans read := by
  simp only [dataReadError] at h
  split at h
  · simp at h
  · rename_i target rowPlan hfind
    simp only [orElse_eq_none, check_eq_none, beq_iff_eq] at h
    obtain ⟨hwidth, hmode⟩ := h
    split at hmode
    · simp at hmode
    · rename_i mode hrow
      simp only [orElse_eq_none, check_eq_none, beq_iff_eq, Bool.not_eq_true',
        Bool.or_eq_false_iff, List.any_eq_false, decide_eq_true_eq] at hmode
      refine ⟨target, rowPlan, mode, hfind, hwidth, hrow, ?_, ?_, hmode.2⟩
      · simp only [List.mem_map, not_exists, not_and]
        intro handler hhandler hcolumn
        exact hmode.1.1 handler hhandler hcolumn
      · intro hdefining hlazy
        have := hmode.1.2
        simp [hdefining, hlazy] at this

/-- What validation guarantees about a whole plan. -/
structure PlanValid (ensemble : Ensemble F PublicIO) (rowPlans : List (RowPlan F)) : Prop where
  row_plans : ∀ entry ∈ ensemble.tables.zip rowPlans, RowPlanValid entry.1 entry.2
  handlers_nodup : ((ensemble.tables.zip rowPlans).flatMap fun entry =>
    entry.2.mode.handled entry.1).Nodup
  data_reads : ∀ entry ∈ ensemble.tables.zip rowPlans, ∀ m (code : Witgen.WitgenIR F m),
    .witness m code ∈ entry.1.rowOperations.toFlat →
      ∀ read ∈ witnessDataReads code, DataReadValid ensemble.tables rowPlans read
  reads_below : ∀ component ∈ ensemble.tables,
    flatReadsBelow component.rowOffset component.rowOperations.toFlat = true

lemma nodup_of_not_mem_take {α : Type} [BEq α] [LawfulBEq α] {values : List α}
    (h : ∀ entry ∈ values.zipIdx, (values.take entry.2).contains entry.1 = false) :
    values.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · have := h (values[j], j) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
    simp only [List.contains_eq_mem, decide_eq_false_iff_not] at this
    exact this (List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simpa using hij⟩)
  · have := h (values[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp))
    simp only [List.contains_eq_mem, decide_eq_false_iff_not] at this
    exact this (List.mem_iff_getElem.mpr ⟨j, by simp; omega, by simpa using hij.symm⟩)

lemma planValid_of_error_eq_none {ensemble : Ensemble F PublicIO} {rowPlans : List (RowPlan F)}
    (h : planError ensemble rowPlans = none) : PlanValid ensemble rowPlans := by
  simp only [planError, orElse_eq_none, List.findSome?_eq_none_iff] at h
  obtain ⟨hrowPlans, hhandlers, hreads, hbelow⟩ := h
  refine ⟨fun entry hentry => rowPlanValid_of_error_eq_none (hrowPlans entry hentry), ?_, ?_, ?_⟩
  · simp only [handlersError, List.findSome?_eq_none_iff, check_eq_none, Bool.not_eq_true'] at hhandlers
    exact nodup_of_not_mem_take hhandlers
  · intro entry hentry m code hcode read hread
    simp only [dataReadsError, List.findSome?_eq_none_iff] at hreads
    obtain ⟨index, hlt, hindex⟩ := List.mem_iff_getElem.mp hcode
    have := hreads entry hentry (.witness m code, index)
      (List.mem_zipIdx_iff_getElem?.mpr (by simp [hindex, hlt]))
    simp only [orElse_eq_none, List.findSome?_eq_none_iff] at this
    exact dataReadValid_of_error_eq_none (this.2 read hread)
  · simp only [readsAheadError, List.findSome?_eq_none_iff, check_eq_none] at hbelow
    exact hbelow

/-- Alignment by name finds, for every component, its row plan. -/
lemma rowPlansOf_spec {plan : GenerationPlan F} :
    (components : List (Component F)) → {rowPlans : List (RowPlan F)} →
      plan.rowPlansOf components = .ok rowPlans →
      rowPlans.length = components.length ∧
        ∀ entry ∈ components.zip rowPlans, (entry.1.circuit.name, entry.2) ∈ plan.components
  | [], rowPlans, h => by
      simp only [GenerationPlan.rowPlansOf, Except.ok.injEq] at h
      subst h
      simp
  | component :: components, rowPlans, h => by
      simp only [GenerationPlan.rowPlansOf] at h
      split at h
      · cases h
      · rename_i rowPlan hrowPlan
        split at h
        · cases h
        · rename_i rest hrest
          cases h
          obtain ⟨hlength, hmem⟩ := rowPlansOf_spec components hrest
          refine ⟨by simp [hlength], ?_⟩
          intro entry hentry
          simp only [List.zip_cons_cons, List.mem_cons] at hentry
          rcases hentry with rfl | hentry
          · simp only [GenerationPlan.rowPlanOf] at hrowPlan
            split at hrowPlan
            · rename_i name _ hfilter
              cases hrowPlan
              have hmem' : (name, rowPlan) ∈ plan.components.filter (·.1 == component.circuit.name) := by
                rw [hfilter]; simp
              simp only [List.mem_filter, beq_iff_eq] at hmem'
              simpa [hmem'.2] using hmem'.1
            · cases hrowPlan
            · cases hrowPlan
          · exact hmem entry hentry

lemma validate_spec {plan : GenerationPlan F} {ensemble : Ensemble F PublicIO}
    {validPlan : ValidPlan ensemble} (h : plan.validate ensemble = .ok validPlan) :
    ∀ entry ∈ ensemble.tables.zip validPlan.rowPlans,
      (entry.1.circuit.name, entry.2) ∈ plan.components := by
  simp only [GenerationPlan.validate] at h
  split at h
  · cases h
  · rename_i rowPlans halign
    split at h
    · split at h
      · cases h
      · cases h
        simp only [GenerationPlan.align] at halign
        split at halign
        · cases halign
        · exact (rowPlansOf_spec _ halign).2
    · cases h

end Air.Flat.WitnessGeneration
