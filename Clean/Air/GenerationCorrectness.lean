module

public import Clean.Air.WitnessGeneration

@[expose] public section

/-!
# Correctness of ensemble witness generation

Witness generation keeps, for every channel message, the net multiplicity of all interactions
generated so far that are not yet balanced. This file proves that it maintains this invariant, so
that a generated witness has balanced channels.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-! ### Net multiplicities -/

/-- The net multiplicity the pending demands record for a channel message. -/
def netOf (demands : List (Demand F)) (channel : String) (message : Array F) : F :=
  ((demands.filter fun demand => demand.channel = channel ∧ demand.message = message).map
    (·.multiplicity)).sum

/-- The net multiplicity of a channel message over a list of interactions. -/
def netOfInteractions (interactions : List (Interaction F)) (channel : String)
    (message : Array F) : F :=
  ((interactions.filter fun interaction =>
    interaction.channel.name = channel ∧ interaction.msg = message).map (·.mult)).sum

@[simp] lemma netOf_nil (channel : String) (message : Array F) :
    netOf ([] : List (Demand F)) channel message = 0 := rfl

lemma netOfInteractions_nil (channel : String) (message : Array F) :
    netOfInteractions ([] : List (Interaction F)) channel message = 0 := rfl

lemma netOfInteractions_append (left right : List (Interaction F)) (channel : String)
    (message : Array F) :
    netOfInteractions (left ++ right) channel message =
      netOfInteractions left channel message + netOfInteractions right channel message := by
  simp [netOfInteractions, List.filter_append]

lemma netOfInteractions_cons (interaction : Interaction F) (rest : List (Interaction F))
    (channel : String) (message : Array F) :
    netOfInteractions (interaction :: rest) channel message =
      (if interaction.channel.name = channel ∧ interaction.msg = message then interaction.mult
        else 0) + netOfInteractions rest channel message := by
  by_cases h : interaction.channel.name = channel ∧ interaction.msg = message <;>
    simp [netOfInteractions, h]

lemma netOf_add (channel : String) (message : Array F) (multiplicity : F)
    (demands : List (Demand F)) (channel' : String) (message' : Array F) :
    netOf (Demand.add channel message multiplicity demands) channel' message' =
      netOf demands channel' message' +
        if channel = channel' ∧ message = message' then multiplicity else 0 := by
  induction demands with
  | nil =>
      simp only [Demand.add]
      split
      · rename_i hzero
        simp [hzero]
      · by_cases h : channel = channel' ∧ message = message' <;>
          simp [netOf, h]
  | cons current rest ih =>
      simp only [Demand.add]
      split
      · rename_i hsame
        simp only [Bool.and_eq_true, beq_iff_eq] at hsame
        obtain ⟨hchannel, hmessage⟩ := hsame
        split
        · rename_i hzero
          by_cases h : channel = channel' ∧ message = message'
          · obtain ⟨rfl, rfl⟩ := h
            simp [netOf, hchannel, hmessage]
            rw [eq_neg_of_add_eq_zero_left hzero]
            ring
          · have hcurrent : ¬(current.channel = channel' ∧ current.message = message') := by
              rwa [hchannel, hmessage]
            simp [netOf, hcurrent, h]
        · by_cases h : channel = channel' ∧ message = message'
          · obtain ⟨rfl, rfl⟩ := h
            simp [netOf, hchannel, hmessage]
            ring
          · have hcurrent : ¬(current.channel = channel' ∧ current.message = message') := by
              rwa [hchannel, hmessage]
            simp [netOf, hcurrent, h]
      · by_cases hcurrent : current.channel = channel' ∧ current.message = message'
        · simp only [netOf, List.filter_cons, hcurrent, and_self, decide_true, ↓reduceIte,
            List.map_cons, List.sum_cons] at ih ⊢
          rw [ih]
          ring
        · simp only [netOf, List.filter_cons, hcurrent, decide_false] at ih ⊢
          simpa using ih

lemma netOf_addInteractions (demands : List (Demand F)) (interactions : List (Interaction F))
    (channel : String) (message : Array F) :
    netOf (Demand.addInteractions demands interactions) channel message =
      netOf demands channel message + netOfInteractions interactions channel message := by
  induction interactions generalizing demands with
  | nil => simp [Demand.addInteractions, netOfInteractions_nil]
  | cons interaction rest ih =>
      simp only [Demand.addInteractions, List.foldl_cons] at ih ⊢
      rw [ih, netOf_add, netOfInteractions_cons]
      ring

lemma netOf_removeInteractions (demands : List (Demand F)) (interactions : List (Interaction F))
    (channel : String) (message : Array F) :
    netOf (Demand.removeInteractions demands interactions) channel message =
      netOf demands channel message - netOfInteractions interactions channel message := by
  induction interactions generalizing demands with
  | nil => simp [Demand.removeInteractions, netOfInteractions_nil]
  | cons interaction rest ih =>
      simp only [Demand.removeInteractions, List.foldl_cons] at ih ⊢
      rw [ih, netOf_add, netOfInteractions_cons]
      split <;> ring

/-! ### Rows and mutations -/

lemma sum_map_set {α : Type*} {M : Type} [AddCommGroup M] (f : α → M) :
    ∀ (values : List α) (index : ℕ) (hindex : index < values.length) (value : α),
      ((values.set index value).map f).sum =
        (values.map f).sum - f values[index] + f value
  | [], _, hindex, _ => absurd hindex (by simp)
  | head :: tail, 0, _, value => by simp; abel
  | head :: tail, index + 1, hindex, value => by
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      rw [sum_map_set f tail index (by simpa using hindex) value]
      abel

lemma netOfInteractions_flatMap {α : Type*} (values : List α) (g : α → List (Interaction F))
    (channel : String) (message : Array F) :
    netOfInteractions (values.flatMap g) channel message =
      (values.map fun value => netOfInteractions (g value) channel message).sum := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [List.flatMap_cons, netOfInteractions_append, ih]

omit [FiniteField F] in
lemma getElem?_of_findSome?_zipIdx {α β : Type} {values : List α} {g : α × ℕ → Option β}
    {result : β} (h : values.zipIdx.findSome? g = some result) :
    ∃ index value, values[index]? = some value ∧ g (value, index) = some result := by
  obtain ⟨⟨value, index⟩, hmem, hg⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨index, value, List.mem_zipIdx_iff_getElem?.mp hmem, hg⟩

/-- The interactions of a component's rows. -/
def ComponentState.interactionsOf (state : ComponentState F) (data : ProverData F)
    (rows : List (GeneratedRow F)) : List (Interaction F) :=
  rows.flatMap (rowInteractions state · data)

/-- A mutation changes only rows: it replaces `removedRows` by `addedRows`, so it changes the net
multiplicity of the component's interactions by the difference. -/
def Mutation.Valid (state : ComponentState F) (data : ProverData F) (mutation : Mutation F) :
    Prop :=
  { mutation.state with rows := state.rows } = state ∧
    ∀ channel message,
      netOfInteractions (state.interactionsOf data mutation.state.rows) channel message =
        netOfInteractions (state.interactionsOf data state.rows) channel message -
          netOfInteractions (state.interactionsOf data mutation.removedRows) channel message +
          netOfInteractions (state.interactionsOf data mutation.addedRows) channel message

lemma netOf_interactionsOf_set (state : ComponentState F) (data : ProverData F)
    {index : ℕ} {row : GeneratedRow F} (hrow : state.rows[index]? = some row)
    (updated : GeneratedRow F) (channel : String) (message : Array F) :
    netOfInteractions (state.interactionsOf data (state.rows.set index updated)) channel message =
      netOfInteractions (state.interactionsOf data state.rows) channel message -
        netOfInteractions (state.interactionsOf data [row]) channel message +
        netOfInteractions (state.interactionsOf data [updated]) channel message := by
  obtain ⟨hindex, rfl⟩ := List.getElem?_eq_some_iff.mp hrow
  simp only [ComponentState.interactionsOf, netOfInteractions_flatMap, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact sum_map_set _ state.rows index hindex updated

lemma handleDemand_valid (state : ComponentState F) (mode : DemandMode F) (demand : Demand F)
    (data : ProverData F) (hint : ProverHint F) : (handleDemand state mode demand data hint).Valid state data := by
  unfold handleDemand
  split
  · refine ⟨rfl, fun channel message => ?_⟩
    simp [ComponentState.interactionsOf, netOfInteractions_append, netOfInteractions_nil]
  · split
    · refine ⟨rfl, fun channel message => ?_⟩
      simp [ComponentState.interactionsOf, netOfInteractions_append, netOfInteractions_nil]
    · rename_i row origin index hexisting
      obtain ⟨index', value, hvalue, hfound⟩ := getElem?_of_findSome?_zipIdx hexisting
      simp only [Option.bind_eq_some_iff] at hfound
      obtain ⟨origin', _, hsome⟩ := hfound
      split at hsome
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl, rfl⟩ := hsome
        exact ⟨rfl, netOf_interactionsOf_set state data hvalue _⟩
      · simp at hsome

lemma handlePreallocated_valid (state : ComponentState F) (handlers : List PreallocatedHandler)
    (demand : Demand F) (data : ProverData F) (hint : ProverHint F) {mutation : Mutation F}
    (h : handlePreallocated state handlers demand data hint = some mutation) :
    mutation.Valid state data := by
  unfold handlePreallocated at h
  split at h
  · simp at h
  · rename_i handler rowIndex row hfound
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hhandler⟩ := List.exists_of_findSome?_eq_some hfound
    split at hhandler
    · obtain ⟨index, value, hvalue, hrow⟩ := getElem?_of_findSome?_zipIdx hhandler
      simp only [Option.bind_eq_some_iff] at hrow
      obtain ⟨_, _, hsome⟩ := hrow
      split at hsome
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨-, rfl, rfl⟩ := hsome
        exact ⟨rfl, netOf_interactionsOf_set state data hvalue _⟩
      · simp at hsome
    · simp at hhandler

/-- The interactions of all components' rows. -/
def statesInteractions (states : List (ComponentState F)) (data : ProverData F) :
    List (Interaction F) :=
  states.flatMap fun state => state.interactionsOf data state.rows

/-- A component state without its rows. -/
def ComponentState.shape (state : ComponentState F) : ComponentState F :=
  { state with rows := [] }

lemma interactionsOf_eq_of_shape {state state' : ComponentState F}
    (h : { state' with rows := state.rows } = state) (data : ProverData F)
    (rows : List (GeneratedRow F)) :
    state'.interactionsOf data rows = state.interactionsOf data rows := by
  rw [← h]
  rfl

lemma shape_eq_of_rows {state state' : ComponentState F}
    (h : { state' with rows := state.rows } = state) : state'.shape = state.shape := by
  rw [← h]
  rfl

theorem handle_spec (states : List (ComponentState F)) (demand : Demand F) (index : ℕ)
    (data : ProverData F) (hint : ProverHint F) {states' : List (ComponentState F)} {change : Change F}
    (h : handle states demand index data hint = .ok (states', change)) :
    states'.map (·.shape) = states.map (·.shape) ∧
      ∀ channel message,
        netOfInteractions (statesInteractions states' data) channel message =
          netOfInteractions (statesInteractions states data) channel message -
            netOfInteractions change.removed channel message +
            netOfInteractions change.added channel message := by
  unfold handle at h
  cases hstate : states[index]? with
  | none =>
      simp only [hstate] at h
      cases h
      exact ⟨rfl, fun channel message => by simp [netOfInteractions_nil]⟩
  | some state =>
      simp only [hstate] at h
      obtain ⟨mutation, hvalid, rfl, rfl⟩ : ∃ mutation : Mutation F, mutation.Valid state data ∧
          states' = states.set index mutation.state ∧
          change = { removed := state.interactionsOf data mutation.removedRows,
                     added := state.interactionsOf data mutation.addedRows } := by
        split at h
        · simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨_, handleDemand_valid state _ demand data hint, h.1.symm, h.2.symm⟩
        · split at h
          · simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            exact ⟨_, handlePreallocated_valid state _ demand data hint ‹_›, h.1.symm, h.2.symm⟩
          · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      obtain ⟨hindex, rfl⟩ := List.getElem?_eq_some_iff.mp hstate
      constructor
      · rw [List.map_set, shape_eq_of_rows hvalid.1]
        have hget : states[index].shape = (states.map (·.shape))[index]'(by simpa using hindex) := by
          simp
        rw [hget]
        exact List.set_getElem_self _
      · intro channel message
        simp only [statesInteractions, netOfInteractions_flatMap]
        rw [sum_map_set _ states index hindex mutation.state,
          interactionsOf_eq_of_shape hvalid.1, hvalid.2 channel message]
        abel

/-! ### Balancing -/

/-- The balancing invariant: the pending demands record the net multiplicity of the verifier's
and all rows' interactions. -/
def Balancing.Tracks (balancing : Balancing F) (verifier : List (Interaction F))
    (data : ProverData F) : Prop :=
  ∀ channel message, netOf balancing.demands channel message =
    netOfInteractions (verifier ++ statesInteractions balancing.states data) channel message

lemma Balancing.tracks_apply {balancing : Balancing F} {verifier : List (Interaction F)}
    {data : ProverData F} (htracks : balancing.Tracks verifier data)
    {states : List (ComponentState F)} {change : Change F}
    (hstates : ∀ channel message,
      netOfInteractions (statesInteractions states data) channel message =
        netOfInteractions (statesInteractions balancing.states data) channel message -
          netOfInteractions change.removed channel message +
          netOfInteractions change.added channel message) :
    (balancing.apply states change).Tracks verifier data := by
  intro channel message
  simp only [Balancing.apply, netOf_addInteractions, netOf_removeInteractions,
    htracks channel message, netOfInteractions_append, hstates channel message]
  abel

/-- Balancing ends with no pending demand, keeps the invariant, and changes only rows. -/
theorem balance_spec (data : ProverData F) (hint : ProverHint F) (verifier : List (Interaction F))
    (balancing : Balancing F) {balanced : Balancing F}
    (h : balance data hint balancing = .ok balanced) (htracks : balancing.Tracks verifier data) :
    balanced.demands = [] ∧ balanced.Tracks verifier data ∧
      balanced.states.map (·.shape) = balancing.states.map (·.shape) := by
  fun_induction balance data hint balancing with
  | case1 balancing hempty =>
      cases h
      exact ⟨List.isEmpty_iff.mp hempty, htracks, rfl⟩
  | case2 => cases h
  | case3 => cases h
  | case4 => cases h
  | case5 balancing _ _ demand index _ states change hhandle next _ ih =>
      obtain ⟨hshape, hstates⟩ := handle_spec _ demand index data hint hhandle
      obtain ⟨hdemands, htracks', hshape'⟩ := ih h (balancing.tracks_apply htracks hstates)
      exact ⟨hdemands, htracks', hshape'.trans hshape⟩
  | case6 => cases h

@[simp] lemma rowInteractions_withRows (state : ComponentState F)
    (rows : List (GeneratedRow F)) (row : GeneratedRow F) (data : ProverData F) :
    rowInteractions { state with rows } row data = rowInteractions state row data := rfl

lemma padTables_spec (data : ProverData F) (hint : ProverHint F) (states : List (ComponentState F)) :
    (padTables data hint states).1.map (·.shape) = states.map (·.shape) ∧
      ∀ channel message,
        netOfInteractions (statesInteractions (padTables data hint states).1 data) channel message =
          netOfInteractions (statesInteractions states data) channel message -
            netOfInteractions [] channel message +
            netOfInteractions (padTables data hint states).2 channel message := by
  constructor
  · simp only [padTables, List.map_map]
    exact List.map_congr_left fun _ _ => rfl
  · intro channel message
    simp only [padTables, statesInteractions, List.map_map, List.flatMap_map,
      netOfInteractions_flatMap, netOfInteractions_nil, sub_zero]
    rw [← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun state _ => ?_
    simp [ComponentState.interactionsOf, List.flatMap_append, netOfInteractions_append,
      netOfInteractions_flatMap]

/-- Padding and balancing end with no pending demand, keep the invariant, and change only rows. -/
theorem padAndBalance_spec (data : ProverData F) (hint : ProverHint F) (verifier : List (Interaction F))
    (balancing : Balancing F) {balanced : Balancing F}
    (h : padAndBalance data hint balancing = .ok balanced) (htracks : balancing.Tracks verifier data) :
    balanced.demands = [] ∧ balanced.Tracks verifier data ∧
      balanced.states.map (·.shape) = balancing.states.map (·.shape) := by
  fun_induction padAndBalance data hint balancing with
  | case1 => cases h
  | case2 balancing states added hpad balancedRound hround hpadded =>
      cases h
      obtain ⟨hshape, hnet⟩ := padTables_spec data hint balancing.states
      rw [hpad] at hshape hnet
      obtain ⟨hdemands, htracks', hshape'⟩ := balance_spec data hint verifier _ hround
        (balancing.tracks_apply htracks hnet)
      exact ⟨hdemands, htracks', hshape'.trans hshape⟩
  | case3 balancing states added hpad balancedRound hround _ _ ih =>
      obtain ⟨hshape, hnet⟩ := padTables_spec data hint balancing.states
      rw [hpad] at hshape hnet
      obtain ⟨-, htracks', hshape'⟩ := balance_spec data hint verifier _ hround
        (balancing.tracks_apply htracks hnet)
      obtain ⟨hdemands, htracks'', hshape''⟩ := ih h htracks'
      exact ⟨hdemands, htracks'', hshape''.trans (hshape'.trans hshape)⟩
  | case4 => cases h

/-! ### The generated witness -/

omit [FiniteField F] in
lemma expression_eval_congr [Field F] {env env' : Environment F} (h : env.get = env'.get) :
    (e : Expression F) → e.eval env = e.eval env'
  | .var cell => by simp [Expression.eval, h]
  | .const _ => rfl
  | .add left right => by
      simp [Expression.eval, expression_eval_congr h left, expression_eval_congr h right]
  | .mul left right => by
      simp [Expression.eval, expression_eval_congr h left, expression_eval_congr h right]

/-- Interaction values read only the environment's cells, not its prover data. -/
lemma interaction_eval_congr {env env' : Environment F} (h : env.get = env'.get)
    (interaction : AbstractInteraction F) : interaction.eval env = interaction.eval env' := by
  have hmult : env interaction.mult = env' interaction.mult := expression_eval_congr h _
  have hmsg : interaction.msg.map env = interaction.msg.map env' :=
    Vector.map_congr_left fun e _ => expression_eval_congr h e
  simp only [AbstractInteraction.eval, hmult, hmsg]

lemma assembleTables_interactions {components : List (Component F)}
    {states : List (ComponentState F)} {assembled : AssembledTables components}
    (h : assembleTables components states = .ok assembled)
    (hinteractions : states.map (·.interactions) =
      components.map (·.rowOperations.interactions))
    (data : ProverData F) :
    assembled.tables.flatMap (·.interactions) = statesInteractions states data := by
  fun_induction assembleTables components states with
  | case1 => cases h; rfl
  | case4 component components state states =>
    rename_i ih
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i rest hrest
      cases h
      simp only [List.map_cons, List.cons.injEq] at hinteractions
      rw [List.flatMap_cons, statesInteractions, List.flatMap_cons]
      congr 1
      · change List.flatMap (fun row => component.operations.interactionValues
            (Environment.fromArray row fun _ _ => #[])) (state.rows.map (·.values)) = _
        simp only [ComponentState.interactionsOf, rowInteractions, Operations.interactionValues,
          Component.interactions_eq, hinteractions.1, List.flatMap_map]
        refine List.flatMap_congr fun row _ => List.map_congr_left fun interaction _ =>
          interaction_eval_congr ?_ interaction
        rfl
      · exact ih hrest hinteractions.2
  | _ => cases h

lemma withDerivedData_interactions (tables : List (Table F)) :
    (withDerivedData tables).flatMap (·.interactions) = tables.flatMap (·.interactions) := by
  simp only [withDerivedData, List.flatMap_map]
  refine List.flatMap_congr fun table _ => List.flatMap_congr fun row _ =>
    List.map_congr_left fun interaction _ => interaction_eval_congr ?_ interaction
  rfl

/-! ### Channel balance -/

open Classical in
lemma interactionsWith_eq_filter {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) :
    witness.interactionsWith channel = witness.interactions.filter (·.channel = channel) := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.verifierInteractionsWith,
    Operations.interactionValuesWith_eq_filter, Tables.interactionsWith,
    EnsembleWitness.toTables, Table.interactionsWith_eq_filter, EnsembleWitness.interactions,
    List.filter_append, List.filter_flatMap]

open Classical in
lemma balanceOf_filter_channel {interactions : List (Interaction F)} {channel : RawChannel F}
    (hnamed : ∀ interaction ∈ interactions,
      interaction.channel.name = channel.name → interaction.channel = channel)
    (message : Array F) :
    balanceOf (interactions.filter (·.channel = channel)) message =
      netOfInteractions interactions channel.name message := by
  simp only [balanceOf, netOfInteractions, List.filter_filter]
  congr 2
  refine List.filter_congr fun interaction hmem => ?_
  by_cases hname : interaction.channel.name = channel.name
  · simp [hnamed interaction hmem hname]
  · have : interaction.channel ≠ channel := fun h => hname (h ▸ rfl)
    simp [this, hname]

lemma mem_interactions_named {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    {channel : RawChannel F} (hchannel : channel ∈ ens.channels) :
    ∀ interaction ∈ witness.interactions,
      interaction.channel.name = channel.name → interaction.channel = channel := by
  intro interaction hmem
  simp only [EnsembleWitness.interactions, Operations.interactionValues, Table.interactions,
    List.mem_append, List.mem_map, List.mem_flatMap] at hmem
  rcases hmem with ⟨abstract, habstract, rfl⟩ | ⟨table, htable, row, _, abstract, habstract, rfl⟩
  · exact ens.channels_named channel hchannel _
      (Ensemble.channel_mem_declaredChannels (List.mem_append_left _ habstract))
  · exact ens.channels_named channel hchannel _ (Ensemble.channel_mem_declaredChannels
      (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨_, EnsembleWitness.mem_component_of_mem htable, habstract⟩)))

/-- A witness whose interactions have zero net multiplicity per channel name and message, and
fewer interactions than the field characteristic, balances all ensemble channels. -/
lemma balancedChannels_of_net {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens}
    (hlength : witness.interactions.length < ringChar F)
    (hnet : ∀ channel message, netOfInteractions witness.interactions channel message = 0) :
    witness.BalancedChannels := by
  intro channel hchannel
  rw [EnsembleWitness.BalancedChannel, interactionsWith_eq_filter]
  refine ⟨.inl (lt_of_le_of_lt (List.length_filter_le _ _) hlength), fun message => ?_⟩
  rw [balanceOf_filter_channel (mem_interactions_named witness hchannel), hnet]

lemma initialStates_interactions {ens : Ensemble F PublicIO} (plan : ValidPlan ens)
    (hint : ProverHint F) :
    (initialStates plan hint).1.map (·.interactions) =
      ens.tables.map (·.rowOperations.interactions) := by
  conv_rhs => rw [← List.map_fst_zip (l₁ := ens.tables) (l₂ := plan.rowPlans) (by rw [plan.aligned])]
  simp [initialStates, ComponentState.initial, Function.comp_def]

/-- Generated witnesses have the requested public input and balance all channels. -/
theorem generateValid_balanced {ens : Ensemble F PublicIO} {plan : ValidPlan ens}
    {publicInput : PublicIO F} {hint : ProverHint F} {witness : EnsembleWitness ens} (h : generateValid plan publicInput hint = .ok witness) :
    witness.publicInput = publicInput ∧ witness.BalancedChannels := by
  have hinteractions := initialStates_interactions plan hint
  rcases hinit : initialStates plan hint with ⟨initial, data⟩
  rw [hinit] at hinteractions
  simp only [generateValid, hinit, bind, Except.bind] at h
  split at h
  · cases h
  rename_i balanced hbalanced
  split at h
  · cases h
  rename_i padded hpadded
  split at h
  · cases h
  rename_i assembled hassembled
  split at h
  swap
  · cases h
  rename_i hlength
  cases h
  refine ⟨rfl, balancedChannels_of_net (FiniteField.ringChar_eq (F := F) ▸ hlength)
    fun channel message => ?_⟩
  set verifier := ens.verifierOperations.interactionValues (Environment.fromInput publicInput data)
  have htracks : Balancing.Tracks ⟨initial,
      Demand.addInteractions [] (verifier ++ statesInteractions initial data),
      (verifier ++ statesInteractions initial data).length⟩ verifier data :=
    fun channel message => by simp [netOf_addInteractions]
  obtain ⟨-, htracks, hshape⟩ := balance_spec data hint verifier _ hbalanced htracks
  obtain ⟨hempty, htracks, hshape'⟩ := padAndBalance_spec data hint verifier _ hpadded htracks
  have hpaddedInteractions : padded.states.map (·.interactions) =
      ens.tables.map (·.rowOperations.interactions) := by
    rw [← hinteractions]
    simpa [List.map_map, Function.comp_def, ComponentState.shape] using
      congrArg (List.map (·.interactions)) (hshape'.trans hshape)
  have hnet := htracks channel message
  rw [hempty, netOf_nil] at hnet
  simp only [EnsembleWitness.interactions]
  rw [withDerivedData_interactions, assembleTables_interactions hassembled hpaddedInteractions data,
    hnet]
  congr 2
  refine List.map_congr_left fun interaction _ => interaction_eval_congr ?_ interaction
  rfl
