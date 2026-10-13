module

public import Clean.Air.GenerationCompleteness

@[expose] public section

/-!
# Proof of the completeness of witness generation

A `Run` bundles a complete plan, its validated form, inputs satisfying the prover assumptions, and
the run the plan's author provides. The proof follows the generator: the initial rows, channel
balancing under an invariant that every step preserves, padding, and assembly.
-/

/-! ### Validation facts -/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Alignment by name finds, for every component, the only row plan named after it. -/
lemma rowPlansOf_unique {plan : GenerationPlan F} :
    (components : List (Component F)) → {rowPlans : List (RowPlan F)} →
      plan.rowPlansOf components = .ok rowPlans →
      ∀ entry ∈ components.zip rowPlans, ∀ rowPlan,
        (entry.1.circuit.name, rowPlan) ∈ plan.components → rowPlan = entry.2
  | [], rowPlans, h => by simp
  | component :: components, rowPlans, h => by
      simp only [GenerationPlan.rowPlansOf] at h
      split at h
      · cases h
      · rename_i rowPlan hrowPlan
        split at h
        · cases h
        · rename_i rest hrest
          cases h
          intro entry hentry rowPlan' hmem
          simp only [List.zip_cons_cons, List.mem_cons] at hentry
          rcases hentry with rfl | hentry
          · simp only [GenerationPlan.rowPlanOf] at hrowPlan
            split at hrowPlan
            · rename_i name _ hfilter
              cases hrowPlan
              have hmem' : (component.circuit.name, rowPlan') ∈
                  plan.components.filter (·.1 == component.circuit.name) := by
                simp [hmem]
              rw [hfilter] at hmem'
              simp only [List.mem_singleton, Prod.mk.injEq] at hmem'
              exact hmem'.2
            · cases hrowPlan
            · cases hrowPlan
          · exact rowPlansOf_unique components hrest entry hentry rowPlan' hmem

lemma validate_unique {plan : GenerationPlan F} {ensemble : Ensemble F PublicIO}
    {validPlan : ValidPlan ensemble} (h : plan.validate ensemble = .ok validPlan) :
    ∀ entry ∈ ensemble.tables.zip validPlan.rowPlans, ∀ rowPlan,
      (entry.1.circuit.name, rowPlan) ∈ plan.components → rowPlan = entry.2 := by
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
        · exact rowPlansOf_unique _ halign
    · cases h

/-- In a zip whose first components have distinct names, an entry is the one found by its name. -/
lemma find?_zip_name {components : List (Component F)} {rowPlans : List (RowPlan F)}
    (hnames : (components.map (·.circuit.name)).Nodup) {entry : Component F × RowPlan F}
    (hentry : entry ∈ components.zip rowPlans) :
    (components.zip rowPlans).find? (fun (target, _) => target.circuit.name == entry.1.circuit.name) =
      some entry := by
  obtain ⟨found, hfound⟩ : ∃ found, (components.zip rowPlans).find?
      (fun (target, _) => target.circuit.name == entry.1.circuit.name) = some found := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨entry, hentry, by simp⟩
  rw [hfound]
  have hname := List.find?_some hfound
  have hmem := List.mem_of_find?_eq_some hfound
  simp only [beq_iff_eq] at hname
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hentry
  have hlength : i < components.length := by simp at hi; omega
  have hlength' : j < components.length := by simp at hj; omega
  rw [List.getElem_zip, List.getElem_zip] at hname
  have := (List.Nodup.getElem_inj_iff hnames (i := i) (j := j) (hi := by simpa using hlength)
    (hj := by simpa using hlength')).mp (by simpa using hname)
  subst this
  rfl

end Air.Flat.WitnessGeneration

namespace Air.Flat.WitnessGeneration

variable {p : ℕ} [Fact p.Prime] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A generation run from inputs satisfying an ensemble's prover assumptions. -/
structure Run (ens : FormalEnsemble (F p) PublicIO) (plan : GenerationPlan (F p)) where
  complete : CompletePlan ens plan
  validPlan : ValidPlan ens.ensemble
  validated : plan.validate ens.ensemble = .ok validPlan
  publicInput : PublicIO (F p)
  proverInput : ens.ProverInput (F p)
  assumptions : ens.ProverAssumptions publicInput proverInput
  steps : ℕ
  reaches : complete.vm.state publicInput steps = complete.vm.final publicInput
  distinct : ∀ index < steps, complete.vm.state publicInput index ≠ complete.vm.final publicInput
  vm_assumptions : ∀ index < steps, ∀ data,
    StableData ens.ensemble plan (ens.hint proverInput) data →
      complete.vm.component.circuit.ProverAssumptions
        (inputOf complete.vm.component (complete.vm.input (complete.vm.state publicInput index)))
        data (ens.hint proverInput)
  bounds : RowBounds ens plan complete.vm (complete.rowBound steps) steps

namespace Run

variable {ens : FormalEnsemble (F p) PublicIO} {plan : GenerationPlan (F p)} (run : Run ens plan)

abbrev hint : ProverHint (F p) := ens.hint run.proverInput

abbrev Stable (data : ProverData (F p)) : Prop := StableData ens.ensemble plan run.hint data

abbrev rowPlans : List (RowPlan (F p)) := run.validPlan.rowPlans

lemma planValid : PlanValid ens.ensemble run.rowPlans :=
  planValid_of_error_eq_none run.validPlan.valid

lemma planned : ∀ entry ∈ ens.ensemble.tables.zip run.rowPlans,
    (entry.1.circuit.name, entry.2) ∈ plan.components :=
  validate_spec run.validated

lemma length_rowPlans : run.rowPlans.length = ens.ensemble.tables.length := run.validPlan.aligned

/-- A component's row plan is its entry in the validated plan. -/
lemma mem_zip {component : Component (F p)} (hmem : component ∈ ens.ensemble.tables)
    {rowPlan : RowPlan (F p)} (hplanned : (component.circuit.name, rowPlan) ∈ plan.components) :
    (component, rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hi' : i < run.rowPlans.length := by rw [run.length_rowPlans]; exact hi
  have hentry : (ens.ensemble.tables[i], run.rowPlans[i]) ∈ ens.ensemble.tables.zip run.rowPlans := by
    have hzip : i < (ens.ensemble.tables.zip run.rowPlans).length := by simp; omega
    rw [← List.getElem_zip (i := i) (h := hzip)]
    exact List.getElem_mem _
  rw [validate_unique run.validated _ hentry rowPlan hplanned]
  exact hentry

lemma find?_eq {entry : Component (F p) × RowPlan (F p)}
    (hentry : entry ∈ ens.ensemble.tables.zip run.rowPlans) :
    (ens.ensemble.tables.zip run.rowPlans).find?
      (fun (target, _) => target.circuit.name == entry.1.circuit.name) = some entry :=
  find?_zip_name ens.ensemble.unique_names hentry

/-! ### A stable prover data -/

/-- Row `row` of a preallocated component before balancing: its initial input, or its padding
input beyond the preallocated rows. -/
def baseInput (component : Component (F p)) (rowPlan : RowPlan (F p))
    (mode : PreallocatedMode (F p)) (row : ℕ) : Array (F p) :=
  if row < mode.rows.toNat then preallocatedInput component mode run.hint row
  else rowPlan.padding.input

/-- The prover data of padded preallocated components with their base inputs. -/
def stableData : ProverData (F p) := fun name n =>
  match (ens.ensemble.tables.zip run.rowPlans).find? (fun (target, _) => target.circuit.name == name) with
  | some (component, rowPlan) =>
      match rowPlan.mode with
      | .preallocated mode => component.proverRows
          ((List.range (rowPlan.padding.targetHeight mode.rows.toNat)).map
            (run.baseInput component rowPlan mode)) n
      | .demand _ => #[]
  | none => #[]

lemma stableData_eq {component : Component (F p)} {rowPlan : RowPlan (F p)}
    {mode : PreallocatedMode (F p)} (hentry : (component, rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans)
    (hmode : rowPlan.mode = .preallocated mode) :
    run.stableData component.circuit.name (size component.Input) =
      ((List.range (rowPlan.padding.targetHeight mode.rows.toNat)).map
        (inputRow component.Input ∘ run.baseInput component rowPlan mode)).toArray := by
  simp only [stableData, run.find?_eq hentry, hmode, Component.proverRows, dite_true, List.map_map]

lemma stableData_stable : run.Stable run.stableData := by
  intro component hmem rowPlan mode hplanned hmode
  have h := run.stableData_eq (run.mem_zip hmem hplanned) hmode
  refine ⟨by simp [Component.rowOffset, h], fun row hrow column hcolumn _ => ?_⟩
  simp only [Component.rowOffset] at hrow hcolumn ⊢
  simp [h, inputRow, baseInput]
  split <;> rfl

/-- Stable prover data agree on every cell a witness program may read. -/
lemma dataCell_eq_of_stable {data data' : ProverData (F p)} (hstable : run.Stable data)
    (hstable' : run.Stable data') {read : DataRead}
    (hread : DataReadValid ens.ensemble.tables run.rowPlans read) (row : ℕ) :
    dataCell data read.key read.width row read.column =
      dataCell data' read.key read.width row read.column := by
  obtain ⟨target, rowPlan, mode, hfind, hwidth, hmode, hcolumn, -, -⟩ := hread.target
  have hentry := List.mem_of_find?_eq_some hfind
  have hkey : target.circuit.name = read.key := by simpa using List.find?_some hfind
  have hmem : target ∈ ens.ensemble.tables := (List.of_mem_zip hentry).1
  obtain ⟨hsize, hcell⟩ := hstable target hmem rowPlan mode (run.planned _ hentry) hmode
  obtain ⟨hsize', hcell'⟩ := hstable' target hmem rowPlan mode (run.planned _ hentry) hmode
  rw [← hkey, hwidth]
  simp only [dataCell]
  by_cases hrow : row < (data target.circuit.name target.rowOffset).size
  · have hrow' : row < (data' target.circuit.name target.rowOffset).size := by omega
    rw [Array.getElem?_eq_getElem hrow, Array.getElem?_eq_getElem hrow']
    simp only [Option.bind_some]
    by_cases hcol : read.column < target.rowOffset
    · rw [Vector.getElem?_eq_getElem hcol, Vector.getElem?_eq_getElem hcol, Option.getD_some,
        Option.getD_some, hcell row hrow _ hcol hcolumn, hcell' row hrow' _ hcol hcolumn]
    · rw [Vector.getElem?_eq_none (by omega), Vector.getElem?_eq_none (by omega)]
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

lemma exists_mem_zip {component : Component (F p)} (hmem : component ∈ ens.ensemble.tables) :
    ∃ rowPlan, (component, rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hzip : i < (ens.ensemble.tables.zip run.rowPlans).length := by
    simp [run.length_rowPlans]; omega
  refine ⟨run.rowPlans[i]'(by rw [run.length_rowPlans]; exact hi), ?_⟩
  rw [← List.getElem_zip (i := i) (h := hzip)]
  exact List.getElem_mem _

/-- Honest rows are the same for all stable prover data. -/
lemma honestRow_eq_of_stable {component : Component (F p)} (hmem : component ∈ ens.ensemble.tables)
    {data data' : ProverData (F p)} (hstable : run.Stable data) (hstable' : run.Stable data')
    {input : Array (F p)} (hsize : input.size = component.rowOffset) :
    honestRow component data run.hint input = honestRow component data' run.hint input := by
  obtain ⟨rowPlan, hentry⟩ := run.exists_mem_zip hmem
  exact honestWitgen_congr run.hint _ input (hsize ▸ run.planValid.reads_below component hmem)
    fun m code hcode read hread row => run.dataCell_eq_of_stable hstable hstable'
      (run.planValid.data_reads _ hentry m code hcode read hread) row

/-! ### Generated rows -/

/-- The prover data that generation reads before balancing. -/
def data0 : ProverData (F p) := (initialStates run.validPlan run.hint).2

/-- The verifier's interactions. -/
def verifier : List (Interaction (F p)) :=
  ens.ensemble.verifierOperations.interactionValues (.fromInput run.publicInput run.data0)

/-- The row of `component` with `input` that generation computes. -/
def row (component : Component (F p)) (input : Array (F p)) (origin : Option (Origin (F p))) :
    GeneratedRow (F p) where
  input
  values := honestRow component run.stableData run.hint input
  origin
  undefined := []

/-- The origin of a row answering `count` occurrences of `message` in mode `mode`. -/
def demandOrigin (mode : DemandMode (F p)) (message : Array (F p)) (count : ℕ) : Origin (F p) where
  channel := mode.channel.name
  direction := mode.direction
  message
  multiplicity := count

/-- The VM row answering the `index`-th state. -/
def vmRow (index : ℕ) : GeneratedRow (F p) :=
  let vm := run.complete.vm
  run.row vm.component (vm.input (vm.state run.publicInput index))
    (some (demandOrigin vm.mode (vm.state run.publicInput index) 1))

/-- The row of a demand-driven component answering `count` occurrences of `message`. -/
def answerRow (component : Component (F p)) (mode : DemandMode (F p)) (message : Array (F p))
    (count : ℕ) : GeneratedRow (F p) :=
  run.row component (mode.input.eval message count) (some (demandOrigin mode message count))

/-- An input whose rows satisfy the prover assumptions for every stable prover data. -/
structure Admissible (component : Component (F p)) (input : Array (F p)) : Prop where
  size : input.size = component.rowOffset
  assumptions : ∀ data, run.Stable data →
    component.circuit.ProverAssumptions (inputOf component input) data run.hint

/-- A message satisfying a channel's prover guarantees for every stable prover data. -/
def Pullable (channel : RawChannel (F p)) (message : Array (F p)) : Prop :=
  ∀ data, run.Stable data → ∀ vector : Vector (F p) channel.arity, vector.toArray = message →
    channel.ProverGuarantees vector data

end Run

/-- The inputs reached from `base` by changing handler columns. -/
inductive Reachable {F : Type} (handlers : List PreallocatedHandler) (base : Array F) :
    Array F → Prop
  | base : Reachable handlers base base
  | set {input : Array F} (h : Reachable handlers base input) (handler : PreallocatedHandler)
      (hmem : handler ∈ handlers) (value : F) : Reachable handlers base (input.set! handler.column value)

namespace Run

variable {ens : FormalEnsemble (F p) PublicIO} {plan : GenerationPlan (F p)} (run : Run ens plan)

/-- The rows of a component state during balancing after `k` VM steps, before or after padding. -/
def RowsOk (k : ℕ) (padded : Bool) (state : ComponentState (F p)) : Prop :=
  match state.rowPlan.mode with
  | .preallocated mode =>
      state.rows.length = (if padded then state.rowPlan.padding.targetHeight mode.rows.toNat
        else mode.rows.toNat) ∧
      ∀ j (hj : j < state.rows.length), ∃ input,
        Reachable mode.handlers (run.baseInput state.component state.rowPlan mode j) input ∧
          state.rows[j] = run.row state.component input none
  | .demand mode =>
      ∃ main pad, state.rows = main ++
          List.replicate pad (run.row state.component state.rowPlan.padding.input none) ∧
        (padded = false → pad = 0) ∧
        (state.component = run.complete.vm.component → main = (List.range k).map run.vmRow) ∧
        (state.component ≠ run.complete.vm.component → ∀ row ∈ main, ∃ message count,
          0 < count ∧ message.size = mode.channel.arity ∧ run.Pullable mode.channel message ∧
          (mode.aggregation = .perOccurrence → count = 1) ∧
          row = run.answerRow state.component mode message count)

/-! ### Honest generated rows -/

/-- The environment of the honest row of `component` with `input` over `data`. -/
abbrev rowEnv (component : Component (F p)) (input : Array (F p)) (data : ProverData (F p)) :
    ProverEnvironment (F p) :=
  rowEnvironment (honestRow component data run.hint input) data run.hint

lemma honestEnv_row {component : Component (F p)} (hmem : component ∈ ens.ensemble.tables)
    {input : Array (F p)} (hsize : input.size = component.rowOffset) (data : ProverData (F p)) :
    HonestEnv component input (run.rowEnv component input data) :=
  honestEnv_rowEnvironment component data run.hint input hsize
    (run.planValid.reads_below component hmem)

/-- The interactions of a generated row are those of its honest row over any stable data. -/
lemma rowInteractions_row {state : ComponentState (F p)}
    (hinteractions : state.interactions = state.component.rowOperations.interactions)
    (hmem : state.component ∈ ens.ensemble.tables) {input : Array (F p)}
    (hsize : input.size = state.component.rowOffset) (origin : Option (Origin (F p)))
    {data : ProverData (F p)} (hstable : run.Stable data) :
    rowInteractions state (run.row state.component input origin) run.data0 =
      interactionsIn state.component (run.rowEnv state.component input data).toEnvironment := by
  simp only [rowInteractions, interactionsIn, hinteractions, row]
  congr 1
  funext interaction
  apply interaction_eval_congr
  funext index
  simp [rowEnvironment, run.honestRow_eq_of_stable hmem hstable run.stableData_stable hsize]

/-- An interaction of a component on a declared channel uses the declared channel. -/
lemma channel_eq_of_mem {component : Component (F p)} (hmem : component ∈ ens.ensemble.tables)
    {interaction : AbstractInteraction (F p)}
    (hinteraction : interaction ∈ component.rowOperations.interactions)
    {channel : RawChannel (F p)} (hchannel : channel ∈ ens.ensemble.channels)
    (hname : interaction.channel.name = channel.name) : interaction.channel = channel :=
  ens.ensemble.channels_named channel hchannel _ (Ensemble.channel_mem_declaredChannels
    (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨component, hmem, by rw [Component.interactions_eq]; exact hinteraction⟩))) hname

/-- A message an admissible row pulls on a declared channel is pullable. -/
lemma pullable_of_row {component : Component (F p)} (hmem : component ∈ ens.ensemble.tables)
    {input : Array (F p)} (hadmissible : run.Admissible component input)
    {interaction : Interaction (F p)}
    (hinteraction : interaction ∈
      interactionsIn component (run.rowEnv component input run.stableData).toEnvironment)
    {channel : RawChannel (F p)} (hchannel : channel ∈ ens.ensemble.channels)
    (hname : interaction.channel.name = channel.name) (hmult : interaction.mult ≠ 0) :
    run.Pullable channel interaction.msg := by
  intro data hstable vector hvector
  obtain ⟨abstract, habstract, rfl⟩ := List.mem_map.mp hinteraction
  have hcomplete := (honestRow_complete component data run.hint input hadmissible.size
    (run.planValid.reads_below component hmem) (hadmissible.assumptions data hstable)).2.2
    abstract habstract
  have hrow := run.honestRow_eq_of_stable hmem hstable run.stableData_stable hadmissible.size
  have hget : (run.rowEnv component input data).toEnvironment.get =
      (run.rowEnv component input run.stableData).toEnvironment.get := by
    funext index
    simp [rowEnvironment, hrow]
  have heval : abstract.eval (run.rowEnv component input data).toEnvironment =
      abstract.eval (run.rowEnv component input run.stableData).toEnvironment :=
    interaction_eval_congr hget abstract
  have hchannel' := channel_eq_of_mem hmem habstract hchannel hname
  subst hchannel'
  rw [← heval] at hmult hvector
  have hvector' : vector = abstract.msg.map (run.rowEnv component input data).toEnvironment :=
    Vector.toArray_inj.mp hvector
  subst hvector'
  exact hcomplete hmult

/-! ### Answered and pulled messages -/

/-- A component state answers pulls on `channel`. -/
abbrev AnswersPull (state : ComponentState (F p)) (channel : String) : Prop :=
  (channel, Direction.pull) ∈ state.rowPlan.mode.handled state.component

/-- The messages a row answers on `channel`, with multiplicity. -/
def answeredBy (state : ComponentState (F p)) (row : GeneratedRow (F p)) (channel : String) :
    Multiset (Array (F p)) :=
  match state.rowPlan.mode with
  | .demand mode =>
      if mode.channel.name = channel then
        match row.origin with
        | some origin => Multiset.replicate origin.multiplicity origin.message
        | none => 0
      else 0
  | .preallocated mode => (mode.handlers.map fun handler =>
      match state.interactions[handler.interaction]? with
      | some interaction =>
          if interaction.channel.name = channel then
            Multiset.replicate (row.input[handler.column]?.getD 0).val
              (interaction.eval (Environment.fromArray row.values run.data0)).msg
          else 0
      | none => 0).sum

/-- The messages of single pulls on `channel` among `interactions`. -/
def pullsOf (interactions : List (Interaction (F p))) (channel : String) : Multiset (Array (F p)) :=
  ((interactions.filter fun interaction => interaction.channel.name = channel ∧
    interaction.assumeGuarantees ∧ interaction.mult = -1).map (·.msg) : List _)

/-- The messages a row pulls on `channel`, unless its component answers that channel. -/
def pulledBy (state : ComponentState (F p)) (row : GeneratedRow (F p))
    (channel : String) : Multiset (Array (F p)) :=
  if AnswersPull state channel then 0 else pullsOf (rowInteractions state row run.data0) channel

/-- The messages all rows answer on `channel`. -/
def answeredMsgs (states : List (ComponentState (F p))) (channel : String) : Multiset (Array (F p)) :=
  (states.map fun state => (state.rows.map fun row => run.answeredBy state row channel).sum).sum

/-- The messages the verifier and all rows pull on `channel`, except rows answering it. -/
def pulledMsgs (states : List (ComponentState (F p))) (channel : String) :
    Multiset (Array (F p)) :=
  pullsOf run.verifier channel +
    (states.map fun state => (state.rows.map fun row => run.pulledBy state row channel).sum).sum

lemma count_pullsOf (interactions : List (Interaction (F p))) (channel : String)
    (message : Array (F p)) :
    (pullsOf interactions channel).count message = pulled interactions channel message := by
  induction interactions with
  | nil => simp [pullsOf, pulled]
  | cons interaction rest ih =>
      simp only [pullsOf, pulled] at ih ⊢
      by_cases h : interaction.channel.name = channel ∧ interaction.assumeGuarantees = true ∧
          interaction.mult = -1
      · by_cases hmessage : interaction.msg = message
        · simp_all
        · simp_all
      · have h' : ¬(interaction.channel.name = channel ∧ interaction.msg = message ∧
            interaction.assumeGuarantees = true ∧ interaction.mult = -1) := by tauto
        simp only [List.filter_cons, decide_eq_true_eq, h, h', if_false, ih]

/-- On a channel where every interaction is a single pull or has multiplicity zero, the net
multiplicity of a message is minus the number of its single pulls. -/
lemma net_eq_neg_pullsOf {interactions : List (Interaction (F p))} {channel : String}
    (hside : ∀ interaction ∈ interactions, interaction.channel.name = channel →
      interaction.mult = 0 ∨ interaction.IsUnitPull) (message : Array (F p)) :
    netOfInteractions interactions channel message =
      -((pullsOf interactions channel).count message : F p) := by
  have hcounted : Counted interactions channel := by
    intro interaction hmem hname
    rcases hside interaction hmem hname with hzero | hpull
    · cases hguarantees : interaction.assumeGuarantees
      · exact .inr rfl
      · exact .inl ⟨hguarantees, .inl hzero⟩
    · exact .inl hpull
  rw [netOfInteractions_eq_answered_sub_pulled hcounted, count_pullsOf]
  have hanswered : answered interactions channel message = 0 := by
    simp only [answered, List.sum_eq_zero_iff, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    rintro _ ⟨interaction, ⟨hmem, hname, -, hpush⟩, rfl⟩
    rcases hside interaction hmem hname with hzero | hpull
    · simp [hzero]
    · simp [Interaction.IsUnitPull, hpush] at hpull
  rw [hanswered]
  simp

end Run

lemma netOfInteractions_eq_zero {F : Type} [FiniteField F] {interactions : List (Interaction F)}
    {channel : String} (hzero : ∀ interaction ∈ interactions, interaction.channel.name = channel →
      interaction.mult = 0) (message : Array F) :
    netOfInteractions interactions channel message = 0 := by
  simp only [netOfInteractions]
  apply List.sum_eq_zero
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  rintro _ ⟨interaction, ⟨hmem, hname, -⟩, rfl⟩
  exact hzero interaction hmem hname

lemma exists_of_netOfInteractions_ne_zero {F : Type} [FiniteField F]
    {interactions : List (Interaction F)} {channel : String} {message : Array F}
    (h : netOfInteractions interactions channel message ≠ 0) :
    ∃ interaction ∈ interactions, interaction.channel.name = channel ∧ interaction.msg = message ∧
      interaction.mult ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply h
  simp only [netOfInteractions]
  apply List.sum_eq_zero
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  rintro _ ⟨interaction, ⟨hmem, hname, hmsg⟩, rfl⟩
  exact hnone interaction hmem hname hmsg

omit [Fact p.Prime] in
lemma filterMap_nodup_unique {α β : Type*} {g : α → Option β} {b : β} :
    ∀ {values : List α}, (values.filterMap g).Nodup → ∀ {a a' : α}, a ∈ values → a' ∈ values →
      g a = some b → g a' = some b → a = a'
  | [], _, _, _, ha, _, _, _ => by simp at ha
  | head :: rest, hnodup, a, a', ha, ha', hga, hga' => by
      have hrest : (rest.filterMap g).Nodup := by
        rw [List.filterMap_cons] at hnodup
        split at hnodup
        · exact hnodup
        · exact (List.nodup_cons.mp hnodup).2
      have hhead : ∀ x ∈ rest, g x = some b → g head ≠ some b := by
        intro x hx hgx hghead
        rw [List.filterMap_cons, hghead] at hnodup
        exact (List.nodup_cons.mp hnodup).1 (List.mem_filterMap.mpr ⟨x, hx, hgx⟩)
      simp only [List.mem_cons] at ha ha'
      rcases ha with rfl | ha <;> rcases ha' with rfl | ha'
      · rfl
      · exact absurd hga (hhead a' ha' hga')
      · exact absurd hga' (hhead a ha hga)
      · exact filterMap_nodup_unique hrest ha ha' hga hga'

omit [Fact p.Prime] in
lemma sum_map_eq_of_unique {α β M : Type*} [AddCommMonoid M] {g : α → Option β} {b : β}
    {f : α → M} {values : List α} (hnodup : (values.filterMap g).Nodup) {a : α} (ha : a ∈ values)
    (hga : g a = some b) (hzero : ∀ a' ∈ values, g a' ≠ some b → f a' = 0) :
    (values.map f).sum = f a := by
  induction values with
  | nil => simp at ha
  | cons head rest ih =>
      have hrest : (rest.filterMap g).Nodup := by
        rw [List.filterMap_cons] at hnodup
        split at hnodup
        · exact hnodup
        · exact (List.nodup_cons.mp hnodup).2
      simp only [List.map_cons, List.sum_cons]
      by_cases hhead : g head = some b
      · obtain rfl := filterMap_nodup_unique hnodup (List.mem_cons_self ..) ha hhead hga
        rw [List.sum_eq_zero]
        · simp
        · intro x hx
          obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hx
          apply hzero a' (List.mem_cons_of_mem _ ha')
          intro hga'
          have := filterMap_nodup_unique hnodup (List.mem_cons_self ..)
            (List.mem_cons_of_mem _ ha') hhead hga'
          subst this
          rw [List.filterMap_cons, hhead] at hnodup
          exact (List.nodup_cons.mp hnodup).1 (List.mem_filterMap.mpr ⟨_, ha', hga'⟩)
      · have ha' : a ∈ rest := by
          rcases List.mem_cons.mp ha with rfl | ha
          · exact absurd hga hhead
          · exact ha
        rw [hzero head (List.mem_cons_self ..) hhead, zero_add,
          ih hrest ha' fun a' ha' => hzero a' (List.mem_cons_of_mem _ ha')]

lemma netOfInteractions_eq_single {F : Type} [FiniteField F] :
    ∀ {interactions : List (Interaction F)} {index : ℕ} {interaction : Interaction F},
      interactions[index]? = some interaction → ∀ {channel : String},
      (∀ index' (h : index' < interactions.length), index' ≠ index →
        interactions[index'].channel.name ≠ channel) → ∀ message,
      netOfInteractions interactions channel message =
        if interaction.channel.name = channel ∧ interaction.msg = message then interaction.mult
        else 0
  | [], _, _, h, _, _, _ => by simp at h
  | head :: rest, 0, interaction, h, channel, hother, message => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [netOfInteractions_cons, netOfInteractions_eq_zero (fun i hi hname => ?_), add_zero]
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
      have := hother (j + 1) (by simp; omega) (by omega)
      rw [List.getElem_cons_succ] at this
      exact absurd hname this
  | head :: rest, index + 1, interaction, h, channel, hother, message => by
      simp only [List.getElem?_cons_succ] at h
      have hhead : head.channel.name ≠ channel := by
        have := hother 0 (by simp) (by omega)
        rwa [List.getElem_cons_zero] at this
      rw [netOfInteractions_cons, netOfInteractions_eq_single h (fun j hj hne => by
        have := hother (j + 1) (by simp; omega) (by omega)
        rwa [List.getElem_cons_succ] at this) message]
      simp [hhead]

namespace Run

variable {ens : FormalEnsemble (F p) PublicIO} {plan : GenerationPlan (F p)} (run : Run ens plan)

/-- At most one component handles each channel and direction. -/
lemma handled_unique {entry entry' : Component (F p) × RowPlan (F p)}
    (hentry : entry ∈ ens.ensemble.tables.zip run.rowPlans)
    (hentry' : entry' ∈ ens.ensemble.tables.zip run.rowPlans) {handled : String × Direction}
    (hmem : handled ∈ entry.2.mode.handled entry.1) (hmem' : handled ∈ entry'.2.mode.handled entry'.1) :
    entry = entry' := by
  have hnodup := run.planValid.handlers_nodup
  rw [List.nodup_flatMap, List.pairwise_iff_getElem] at hnodup
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hentry
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hentry'
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact absurd hmem' (List.disjoint_left.mp (hnodup.2 i j hi hj hij) hmem)
  · rfl
  · exact absurd hmem (List.disjoint_left.mp (hnodup.2 j i hj hi hij) hmem')

/-- A component handles each channel and direction at most once. -/
lemma handled_nodup {entry : Component (F p) × RowPlan (F p)}
    (hentry : entry ∈ ens.ensemble.tables.zip run.rowPlans) :
    (entry.2.mode.handled entry.1).Nodup :=
  (List.nodup_flatMap.mp run.planValid.handlers_nodup).1 entry hentry

/-! ### The VM -/

lemma verifier_eq (data : ProverData (F p)) :
    ens.ensemble.verifierOperations.interactionValues (.fromInput run.publicInput data) =
      run.verifier := by
  simp only [verifier, Operations.interactionValues]
  congr 1
  funext interaction
  apply interaction_eval_congr
  rfl

/-- A verifier interaction on a declared channel uses the declared channel. -/
lemma verifier_channel_eq {interaction : Interaction (F p)} (hinteraction : interaction ∈ run.verifier)
    {channel : RawChannel (F p)} (hchannel : channel ∈ ens.ensemble.channels)
    (hname : interaction.channel.name = channel.name) : interaction.channel = channel := by
  obtain ⟨abstract, habstract, rfl⟩ := List.mem_map.mp hinteraction
  exact ens.ensemble.channels_named channel hchannel _
    (Ensemble.channel_mem_declaredChannels (List.mem_append_left _ habstract)) hname

lemma vm_entry : (run.complete.vm.component, { mode := .demand run.complete.vm.mode, padding := run.complete.vm.padding }) ∈
    ens.ensemble.tables.zip run.rowPlans :=
  run.mem_zip run.complete.vm.mem run.complete.vm.planned

lemma eval_size (template : InputTemplate (F p)) (message : Array (F p)) (count : ℕ) :
    (template.eval message count).size = template.cells.length := by
  simp [InputTemplate.eval]

lemma demand_input_size {component : Component (F p)} {rowPlan : RowPlan (F p)}
    {mode : DemandMode (F p)} (hentry : (component, rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans)
    (hmode : rowPlan.mode = .demand mode) (message : Array (F p)) (count : ℕ) :
    (mode.input.eval message count).size = component.rowOffset := by
  rw [eval_size]
  exact ((run.planValid.row_plans _ hentry).demand mode hmode).1

lemma vm_input_size (state : Array (F p)) : (run.complete.vm.input state).size = run.complete.vm.component.rowOffset :=
  run.demand_input_size run.vm_entry rfl state 1

/-- The facts the VM obligation gives about the row answering a state. -/
lemma vm_row_facts {state : Array (F p)} (hsize : state.size = run.complete.vm.channel.arity)
    (hassumptions : run.Admissible run.complete.vm.component (run.complete.vm.input state)) :
    let interactions := interactionsIn run.complete.vm.component
      (run.rowEnv run.complete.vm.component (run.complete.vm.input state) run.stableData).toEnvironment
    (∀ message, netOfInteractions interactions run.complete.vm.channel.name message =
      (if message = run.complete.vm.next state then 1 else 0) - (if message = state then 1 else 0)) ∧
    ∀ interaction ∈ interactions, interaction.channel.name ≠ run.complete.vm.channel.name →
      SideInteraction ens.ensemble plan run.complete.vm.channel.name false interaction :=
  run.complete.vm_row state _ hsize
    (run.honestEnv_row run.complete.vm.mem (run.vm_input_size state) run.stableData)
    (hassumptions.assumptions _ run.stableData_stable)

lemma vm_admissible {index : ℕ} (hindex : index < run.steps) :
    run.Admissible run.complete.vm.component (run.complete.vm.input (run.complete.vm.state run.publicInput index)) :=
  ⟨run.vm_input_size _, run.vm_assumptions index hindex⟩

/-- The states of the run have the VM channel's arity. -/
lemma state_size : ∀ index < run.steps,
    (run.complete.vm.state run.publicInput index).size = run.complete.vm.channel.arity
  | 0, hindex => by
      have hverifier := (run.complete.verifier run.publicInput run.proverInput run.assumptions
        run.stableData run.stableData_stable).1 (run.complete.vm.initial run.publicInput)
      rw [run.verifier_eq] at hverifier
      have hne : run.complete.vm.initial run.publicInput ≠ run.complete.vm.final run.publicInput :=
        run.distinct 0 hindex
      simp only [hne, if_true, if_false, sub_zero] at hverifier
      obtain ⟨interaction, hmem, hname, hmsg, -⟩ :=
        exists_of_netOfInteractions_ne_zero (hverifier ▸ one_ne_zero)
      rw [← run.verifier_channel_eq hmem run.complete.vm.declared hname]
      simp only [Vm.state, Function.iterate_zero, id_eq, ← hmsg]
      exact interaction.same_size
  | index + 1, hindex => by
      have hsize := state_size index (by omega)
      have hstep : run.complete.vm.state run.publicInput (index + 1) =
          run.complete.vm.next (run.complete.vm.state run.publicInput index) := by
        simp only [Vm.state, Function.iterate_succ_apply']
      rw [hstep]
      by_cases hsame : run.complete.vm.next (run.complete.vm.state run.publicInput index) =
          run.complete.vm.state run.publicInput index
      · rw [hsame, hsize]
      have hnet := (run.vm_row_facts hsize (run.vm_admissible (by omega))).1
        (run.complete.vm.next (run.complete.vm.state run.publicInput index))
      simp only [hsame, if_true, if_false, sub_zero] at hnet
      obtain ⟨interaction, hmem, hname, hmsg, -⟩ :=
        exists_of_netOfInteractions_ne_zero (hnet ▸ one_ne_zero)
      obtain ⟨abstract, habstract, rfl⟩ := List.mem_map.mp hmem
      rw [← hmsg, ← channel_eq_of_mem run.complete.vm.mem habstract run.complete.vm.declared hname]
      exact (abstract.eval _).same_size

/-! ### Facts about rows -/

/-- The component states before rows are added. -/
def initialShape : List (ComponentState (F p)) :=
  (ens.ensemble.tables.zip run.rowPlans).map fun (component, rowPlan) =>
    ComponentState.initial component rowPlan

/-- A component state of a validated plan, with some rows. -/
structure StateOk (state : ComponentState (F p)) : Prop where
  entry : (state.component, state.rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans
  interactions : state.interactions = state.component.rowOperations.interactions
  witgenOps : state.witgenOps = witnessOperationsOnly state.component.rowOperations.toFlat

lemma StateOk.mem {state : ComponentState (F p)} (h : run.StateOk state) :
    state.component ∈ ens.ensemble.tables :=
  (List.of_mem_zip h.entry).1

lemma stateOk_of_shape {states : List (ComponentState (F p))}
    (hshape : states.map (·.shape) = run.initialShape) {state : ComponentState (F p)}
    (hstate : state ∈ states) : run.StateOk state := by
  have hmem : state.shape ∈ run.initialShape := hshape ▸ List.mem_map_of_mem hstate
  obtain ⟨⟨component, rowPlan⟩, hentry, heq⟩ := List.mem_map.mp hmem
  simp only [ComponentState.initial, ComponentState.shape] at heq
  cases state
  simp only [ComponentState.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := heq
  exact ⟨hentry, rfl, rfl⟩

/-- The net multiplicity a row adds on the VM channel: a VM row pulls its state and pushes the
next one. -/
def vmNet (state : ComponentState (F p)) (row : GeneratedRow (F p))
    (message : Array (F p)) : F p :=
  if state.component.circuit.name = run.complete.vm.component.circuit.name then
    match row.origin with
    | some origin => (if message = run.complete.vm.next origin.message then 1 else 0) -
        (if message = origin.message then 1 else 0)
    | none => 0
  else 0

/-- What every row satisfies: its input is admissible, its interactions on channels its component
does not answer are side interactions, and its nets on answered channels and the VM channel are
what its component's mode says. -/
structure RowFacts (state : ComponentState (F p)) (row : GeneratedRow (F p)) : Prop where
  admissible : run.Admissible state.component row.input
  side : ∀ interaction ∈ rowInteractions state row run.data0,
    ¬AnswersPull state interaction.channel.name →
    (state.component = run.complete.vm.component → interaction.channel.name ≠ run.complete.vm.channel.name) →
      SideInteraction ens.ensemble plan run.complete.vm.channel.name false interaction
  answered_zero : ∀ channel ≠ run.complete.vm.channel.name, ¬AnswersPull state channel →
    run.answeredBy state row channel = 0
  answered_net : ∀ channel ≠ run.complete.vm.channel.name, AnswersPull state channel → ∀ message,
    netOfInteractions (rowInteractions state row run.data0) channel message =
      ((run.answeredBy state row channel).count message : F p)
  vm_net : ∀ message, netOfInteractions (rowInteractions state row run.data0)
    run.complete.vm.channel.name message = run.vmNet state row message

lemma entry_unique_name {entry entry' : Component (F p) × RowPlan (F p)}
    (hentry : entry ∈ ens.ensemble.tables.zip run.rowPlans)
    (hentry' : entry' ∈ ens.ensemble.tables.zip run.rowPlans)
    (h : entry.1.circuit.name = entry'.1.circuit.name) : entry = entry' := by
  have := run.find?_eq hentry
  rw [h, run.find?_eq hentry'] at this
  exact (Option.some.inj this).symm

lemma entry_unique {entry entry' : Component (F p) × RowPlan (F p)}
    (hentry : entry ∈ ens.ensemble.tables.zip run.rowPlans)
    (hentry' : entry' ∈ ens.ensemble.tables.zip run.rowPlans) (h : entry.1 = entry'.1) :
    entry = entry' :=
  run.entry_unique_name hentry hentry' (by rw [h])

lemma StateOk.name_ne_vm {state : ComponentState (F p)} (hok : run.StateOk state)
    (hvm : state.component ≠ run.complete.vm.component) :
    state.component.circuit.name ≠ run.complete.vm.component.circuit.name := fun h =>
  hvm (congrArg Prod.fst (run.entry_unique_name hok.entry run.vm_entry h))

lemma StateOk.vm_rowPlan {state : ComponentState (F p)} (hok : run.StateOk state)
    (hvm : state.component = run.complete.vm.component) :
    state.rowPlan = { mode := .demand run.complete.vm.mode, padding := run.complete.vm.padding } :=
  congrArg Prod.snd (run.entry_unique hok.entry run.vm_entry hvm)

lemma not_answersPull_vm {state : ComponentState (F p)} (hok : run.StateOk state)
    (hvm : state.component = run.complete.vm.component) (channel : String) :
    ¬AnswersPull state channel := by
  have hplan := StateOk.vm_rowPlan run hok hvm
  simp [AnswersPull, hplan, Mode.handled, run.complete.vm.mode_direction]

lemma rowFacts_vmRow {state : ComponentState (F p)} (hok : run.StateOk state)
    (hvm : state.component = run.complete.vm.component) {index : ℕ} (hindex : index < run.steps) :
    run.RowFacts state (run.vmRow index) := by
  have hadmissible := run.vm_admissible hindex
  have hfacts := run.vm_row_facts (run.state_size index hindex) hadmissible
  have hinteractions : rowInteractions state (run.vmRow index) run.data0 =
      interactionsIn run.complete.vm.component (run.rowEnv run.complete.vm.component
        (run.complete.vm.input (run.complete.vm.state run.publicInput index)) run.stableData).toEnvironment := by
    have := run.rowInteractions_row hok.interactions hok.mem (input :=
      run.complete.vm.input (run.complete.vm.state run.publicInput index)) (hvm ▸ run.vm_input_size _)
      (some (demandOrigin run.complete.vm.mode (run.complete.vm.state run.publicInput index) 1)) run.stableData_stable
    rw [hvm] at this
    exact this
  refine ⟨hvm ▸ hadmissible, ?_, ?_, ?_, ?_⟩
  · intro interaction hmem _ hname
    rw [hinteractions] at hmem
    exact hfacts.2 interaction hmem (hname hvm)
  · intro channel hchannel _
    have hplan := StateOk.vm_rowPlan run hok hvm
    simp only [answeredBy, hplan, run.complete.vm.mode_channel]
    simp [Ne.symm hchannel]
  · intro channel _ hanswers
    exact absurd hanswers (run.not_answersPull_vm hok hvm channel)
  · intro message
    have hname : state.component.circuit.name = run.complete.vm.component.circuit.name := by
      rw [hvm]
    rw [hinteractions, hfacts.1 message]
    simp [vmNet, hname, vmRow, row, demandOrigin]

lemma answersPull_demand {state : ComponentState (F p)} (hok : run.StateOk state)
    (hvm : state.component ≠ run.complete.vm.component) {mode : DemandMode (F p)}
    (hmode : state.rowPlan.mode = .demand mode) (channel : String) :
    AnswersPull state channel ↔ channel = mode.channel.name := by
  have hdirection := (run.complete.demand state.component hok.mem state.rowPlan mode
    (run.planned _ hok.entry) hmode hvm).2.1
  simp [AnswersPull, hmode, Mode.handled, hdirection]

/-- No component answers pulls on the VM channel. -/
lemma not_answersPull_vmChannel {state : ComponentState (F p)} (hok : run.StateOk state) :
    ¬AnswersPull state run.complete.vm.channel.name :=
  run.complete.vm.no_pull_handler state.component hok.mem state.rowPlan (run.planned _ hok.entry)

lemma rowFacts_answerRow {state : ComponentState (F p)} (hok : run.StateOk state)
    (hvm : state.component ≠ run.complete.vm.component) {mode : DemandMode (F p)}
    (hmode : state.rowPlan.mode = .demand mode) {message : Array (F p)} {count : ℕ}
    (hcount : 0 < count) (hsize : message.size = mode.channel.arity)
    (hpullable : run.Pullable mode.channel message) :
    run.RowFacts state (run.answerRow state.component mode message count) := by
  obtain ⟨-, -, hassumptions, hnet, -⟩ := run.complete.demand state.component hok.mem
    state.rowPlan mode (run.planned _ hok.entry) hmode hvm
  have hentry := hok.entry
  have hinputSize := run.demand_input_size hentry hmode message count
  have hadmissible : run.Admissible state.component (mode.input.eval message count) :=
    ⟨hinputSize, fun data hstable => hassumptions run.publicInput run.proverInput run.assumptions
      data hstable ⟨message, hsize⟩ count hcount (hpullable data hstable ⟨message, hsize⟩ rfl)⟩
  obtain ⟨hnet, hside⟩ := hnet message count _ (run.honestEnv_row hok.mem hinputSize run.stableData)
    (hadmissible.assumptions _ run.stableData_stable)
  have hinteractions := run.rowInteractions_row hok.interactions hok.mem hinputSize
    (some (demandOrigin mode message count)) run.stableData_stable
  have hanswers := run.answersPull_demand hok hvm hmode
  have hmodeChannel : mode.channel.name ≠ run.complete.vm.channel.name := fun h =>
    run.not_answersPull_vmChannel hok ((hanswers _).mpr h.symm)
  refine ⟨hadmissible, ?_, ?_, ?_, ?_⟩
  · intro interaction hmem hnot _
    rw [answerRow, hinteractions] at hmem
    exact hside interaction hmem fun h => hnot ((hanswers _).mpr h)
  · intro channel _ hnot
    have : mode.channel.name ≠ channel := fun h => hnot ((hanswers _).mpr h.symm)
    simp [answeredBy, hmode, this]
  · intro channel _ hanswers' message'
    obtain rfl := (hanswers _).mp hanswers'
    rw [answerRow, hinteractions, hnet message']
    simp only [answeredBy, hmode, if_true, row, demandOrigin, Multiset.count_replicate]
    by_cases hmessage : message' = message
    · simp [hmessage]
    · simp [hmessage, Ne.symm hmessage]
  · intro message'
    rw [answerRow, hinteractions]
    simp only [vmNet, if_neg (StateOk.name_ne_vm run hok hvm)]
    apply netOfInteractions_eq_zero
    intro interaction hmem hname
    rcases hside interaction hmem (by rw [hname]; exact Ne.symm hmodeChannel) with hzero | ⟨-, hne, -⟩
    · exact hzero
    · exact absurd hname hne

lemma sideInteraction_false {interaction : Interaction (F p)}
    (h : SideInteraction ens.ensemble plan run.complete.vm.channel.name true interaction) :
    SideInteraction ens.ensemble plan run.complete.vm.channel.name false interaction := by
  rcases h with h | ⟨hpull, hne, component, hmem, rowPlan, hplanned, hhandled, -⟩
  · exact .inl h
  · exact .inr ⟨hpull, hne, component, hmem, rowPlan, hplanned, hhandled, by simp⟩

/-- The component answering a channel, as a plan entry. -/
lemma answers_entry {preallocated : Bool} {channel : String}
    (h : Answers ens.ensemble plan preallocated channel) :
    ∃ entry ∈ ens.ensemble.tables.zip run.rowPlans,
      (channel, Direction.pull) ∈ entry.2.mode.handled entry.1 ∧
      (preallocated → ∃ mode, entry.2.mode = .preallocated mode) := by
  obtain ⟨component, hmem, rowPlan, hplanned, hhandled, hpreallocated⟩ := h
  exact ⟨(component, rowPlan), run.mem_zip hmem hplanned, hhandled, hpreallocated⟩

/-- A side interaction of a padding row on a channel a demand-driven component answers has
multiplicity zero. -/
lemma mult_eq_zero_of_padding {state : ComponentState (F p)} (hok : run.StateOk state)
    {mode : DemandMode (F p)} (hmode : state.rowPlan.mode = .demand mode)
    {interaction : Interaction (F p)}
    (hside : SideInteraction ens.ensemble plan run.complete.vm.channel.name true interaction)
    (hanswers : AnswersPull state interaction.channel.name) : interaction.mult = 0 := by
  rcases hside with hzero | ⟨-, -, hanswered⟩
  · exact hzero
  obtain ⟨entry, hentry, hhandled, hpreallocated⟩ := run.answers_entry hanswered
  obtain ⟨mode', hmode'⟩ := hpreallocated rfl
  have := run.handled_unique hentry hok.entry hhandled hanswers
  rw [this] at hmode'
  rw [hmode] at hmode'
  cases hmode'

lemma rowFacts_padding {state : ComponentState (F p)} (hok : run.StateOk state)
    {mode : DemandMode (F p)} (hmode : state.rowPlan.mode = .demand mode) :
    run.RowFacts state (run.row state.component state.rowPlan.padding.input none) := by
  have hpadding := run.complete.padding state.component hok.mem state.rowPlan
    (run.planned _ hok.entry) run.publicInput run.proverInput run.assumptions
  have hsize : state.rowPlan.padding.input.size = state.component.rowOffset :=
    (run.planValid.row_plans _ hok.entry).padding_width
  have hadmissible : run.Admissible state.component state.rowPlan.padding.input :=
    ⟨hsize, fun data hstable => (hpadding data hstable).1⟩
  have hside' := (hpadding _ run.stableData_stable).2 _
    (run.honestEnv_row hok.mem hsize run.stableData) rfl rfl
  have hinteractions := run.rowInteractions_row hok.interactions hok.mem hsize none
    run.stableData_stable
  refine ⟨hadmissible, fun interaction hmem _ _ => run.sideInteraction_false
    (hside' interaction (hinteractions ▸ hmem)), ?_, ?_, ?_⟩
  · intro channel _ _
    simp [answeredBy, hmode, row]
  · intro channel _ hanswers message
    rw [hinteractions, netOfInteractions_eq_zero fun interaction hmem hname =>
      run.mult_eq_zero_of_padding hok hmode (hside' interaction hmem) (hname ▸ hanswers)]
    simp [answeredBy, hmode, row]
  · intro message
    rw [hinteractions, netOfInteractions_eq_zero]
    · simp [vmNet, row]
    · intro interaction hmem hname
      rcases hside' interaction hmem with hzero | ⟨-, hne, -⟩
      · exact hzero
      · exact absurd hname hne

lemma rowFacts_preallocated {state : ComponentState (F p)} (hok : run.StateOk state)
    {mode : PreallocatedMode (F p)} (hmode : state.rowPlan.mode = .preallocated mode)
    {input : Array (F p)} (hadmissible : run.Admissible state.component input) :
    run.RowFacts state (run.row state.component input none) := by
  obtain ⟨-, -, -, hsideP, hhandlers⟩ := run.complete.preallocated state.component hok.mem
    state.rowPlan mode (run.planned _ hok.entry) hmode run.publicInput run.proverInput
    run.assumptions run.stableData run.stableData_stable
  have hhonest := run.honestEnv_row hok.mem hadmissible.size run.stableData
  have hPA := hadmissible.assumptions _ run.stableData_stable
  have hside := hsideP input _ hhonest rfl rfl hPA
  have hinteractions := run.rowInteractions_row hok.interactions hok.mem hadmissible.size none
    run.stableData_stable
  set env := run.rowEnv state.component input run.stableData
  set rowInts := interactionsIn state.component env.toEnvironment
  have hnodup := run.handled_nodup hok.entry
  simp only [hmode, Mode.handled] at hnodup
  have hhandler : ∀ handler ∈ mode.handlers, ∃ interaction,
      state.component.rowOperations.interactions[handler.interaction]? = some interaction ∧
      interaction.assumeGuarantees = false ∧
      (interaction.eval env.toEnvironment).mult = input[handler.column]?.getD 0 := by
    intro handler hhandler
    obtain ⟨interaction, hinteraction, -, -, hfacts⟩ := hhandlers handler hhandler
    obtain ⟨hpush, hmult, -⟩ := hfacts input env hhonest rfl rfl hPA
    exact ⟨interaction, hinteraction, hpush, hmult⟩
  have hhandled : ∀ handler ∈ mode.handlers, ∀ interaction,
      state.component.rowOperations.interactions[handler.interaction]? = some interaction →
      (state.component.rowOperations.interactions[handler.interaction]?.map fun interaction =>
        (interaction.channel.name, handlerDirection interaction)) =
        some (interaction.channel.name, Direction.pull) := by
    intro handler hmem interaction hinteraction
    obtain ⟨interaction', hinteraction', hpush, -⟩ := hhandler handler hmem
    rw [hinteraction] at hinteraction' ⊢
    cases hinteraction'
    simp [handlerDirection, hpush]
  have hanswers : ∀ channel, AnswersPull state channel ↔ ∃ handler ∈ mode.handlers,
      ∃ interaction, state.component.rowOperations.interactions[handler.interaction]? =
        some interaction ∧ interaction.channel.name = channel := by
    intro channel
    constructor
    · intro h
      simp only [AnswersPull, hmode, Mode.handled, List.mem_filterMap, Option.map_eq_some_iff,
        Prod.mk.injEq] at h
      obtain ⟨handler, hmem, interaction, hinteraction, hname, -⟩ := h
      exact ⟨handler, hmem, interaction, hinteraction, hname⟩
    · rintro ⟨handler, hmem, interaction, hinteraction, rfl⟩
      simp only [AnswersPull, hmode, Mode.handled]
      exact List.mem_filterMap.mpr ⟨handler, hmem, hhandled handler hmem interaction hinteraction⟩
  have hlength : rowInts.length = state.component.rowOperations.interactions.length := by
    simp [rowInts, interactionsIn]
  have hclass : ∀ index (hindex : index < rowInts.length),
      (∃ handler ∈ mode.handlers, handler.interaction = index) ∨
        (SideInteraction ens.ensemble plan run.complete.vm.channel.name false rowInts[index] ∧
          ¬AnswersPull state rowInts[index].channel.name) := by
    intro index hindex
    by_cases hmem : index ∈ mode.handlers.map (·.interaction)
    · obtain ⟨handler, hhandler, rfl⟩ := List.mem_map.mp hmem
      exact .inl ⟨handler, hhandler, rfl⟩
    · exact .inr (hside index hmem _ (List.getElem?_eq_getElem hindex))
  have hhandlerElem : ∀ (handler : PreallocatedHandler) (interaction : AbstractInteraction (F p)),
      state.component.rowOperations.interactions[handler.interaction]? = some interaction →
      ∃ hindex : handler.interaction < rowInts.length,
        rowInts[handler.interaction] = interaction.eval env.toEnvironment := by
    intro handler interaction hinteraction
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hinteraction
    exact ⟨by omega, by simp [rowInts, interactionsIn, heq]⟩
  refine ⟨hadmissible, ?_, ?_, ?_, ?_⟩
  · intro interaction hmem hnot _
    rw [hinteractions] at hmem
    obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hmem
    rcases hclass index hindex with ⟨handler, hmem', rfl⟩ | ⟨hside', -⟩
    · obtain ⟨abstract, habstract, -⟩ := hhandler handler hmem'
      obtain ⟨_, helem⟩ := hhandlerElem handler abstract habstract
      exact absurd ((hanswers _).mpr ⟨handler, hmem', abstract, habstract, by rw [helem]; rfl⟩) hnot
    · exact hside'
  · intro channel _ hnot
    simp only [answeredBy, hmode]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨handler, hmem, rfl⟩ := List.mem_map.mp hx
    rw [hok.interactions]
    split
    · rename_i abstract habstract
      rw [if_neg fun hname => hnot ((hanswers _).mpr ⟨handler, hmem, abstract, habstract, hname⟩)]
    · rfl
  · intro channel _ hanswer message
    obtain ⟨handler, hmem, abstract, habstract, hname⟩ := (hanswers channel).mp hanswer
    obtain ⟨hindex, heq⟩ := hhandlerElem handler abstract habstract
    obtain ⟨abstract', habstract', -, hmult⟩ := hhandler handler hmem
    rw [habstract] at habstract'
    cases habstract'
    rw [hinteractions, netOfInteractions_eq_single (index := handler.interaction)
      (List.getElem?_eq_some_iff.mpr ⟨hindex, heq⟩) ?_ message]
    · simp only [answeredBy, hmode]
      rw [sum_map_eq_of_unique hnodup hmem (hhandled handler hmem abstract habstract)]
      · rw [hok.interactions, habstract]
        simp only [AbstractInteraction.eval_channel, hname, true_and, if_true, row,
          Multiset.count_replicate, hmult]
        have hmsg : (abstract.eval (Environment.fromArray
            (honestRow state.component run.stableData run.hint input) run.data0)).msg =
            (abstract.eval env.toEnvironment).msg := by
          rw [interaction_eval_congr (env := Environment.fromArray
            (honestRow state.component run.stableData run.hint input) run.data0)
            (env' := env.toEnvironment) rfl abstract]
        rw [hmsg]
        split_ifs <;> simp
      · intro handler' hmem' hne
        rw [hok.interactions]
        split
        · rename_i abstract'' habstract''
          rw [if_neg]
          intro hname'
          exact hne (by rw [hhandled handler' hmem' abstract'' habstract'', hname', hname])
        · rfl
    · intro index' hindex' hne hname'
      rcases hclass index' hindex' with ⟨handler', hmem', rfl⟩ | ⟨-, hnot⟩
      · obtain ⟨abstract', habstract', -⟩ := hhandler handler' hmem'
        obtain ⟨_, helem'⟩ := hhandlerElem handler' abstract' habstract'
        rw [helem'] at hname'
        have := filterMap_nodup_unique hnodup hmem hmem'
          (hhandled handler hmem abstract habstract)
          (by rw [hhandled handler' hmem' abstract' habstract', hname, ← hname']; rfl)
        exact hne (by rw [this])
      · exact hnot (hname' ▸ hanswer)
  · intro message
    have hvm : state.component ≠ run.complete.vm.component := by
      intro hvm
      have := StateOk.vm_rowPlan run hok hvm
      rw [this] at hmode
      cases hmode
    rw [hinteractions, netOfInteractions_eq_zero]
    · simp [vmNet, StateOk.name_ne_vm run hok hvm]
    · intro interaction hmem hname
      obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hmem
      rcases hclass index hindex with ⟨handler, hmem', rfl⟩ | ⟨hside', -⟩
      · obtain ⟨abstract, habstract, -⟩ := hhandler handler hmem'
        obtain ⟨_, helem⟩ := hhandlerElem handler abstract habstract
        rw [helem] at hname
        exact absurd ((hanswers _).mpr ⟨handler, hmem', abstract, habstract, hname⟩)
          (run.not_answersPull_vmChannel hok)
      · rcases hside' with hzero | ⟨-, hne, -⟩
        · exact hzero
        · exact absurd hname hne

lemma fixedPrefix_size (component : Component (F p)) (row : UInt64) :
    (fixedPrefix component row).size = component.fixedWidth := by
  unfold fixedPrefix Component.fixedWidth
  cases component.fixedColumns <;> simp [FixedColumns.row]

lemma preallocatedInput_size {component : Component (F p)} {rowPlan : RowPlan (F p)}
    {mode : PreallocatedMode (F p)} (hentry : (component, rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans)
    (hmode : rowPlan.mode = .preallocated mode) (row : ℕ) :
    (preallocatedInput component mode run.hint row).size = component.rowOffset := by
  simp only [preallocatedInput, Array.size_append, fixedPrefix_size, Vector.size_toArray]
  exact ((run.planValid.row_plans _ hentry).preallocated mode hmode).1

lemma admissible_baseInput {state : ComponentState (F p)} (hok : run.StateOk state)
    {mode : PreallocatedMode (F p)} (hmode : state.rowPlan.mode = .preallocated mode) (row : ℕ) :
    run.Admissible state.component (run.baseInput state.component state.rowPlan mode row) := by
  unfold baseInput
  split
  · rename_i hrow
    exact ⟨run.preallocatedInput_size hok.entry hmode row, fun data hstable =>
      (run.complete.preallocated state.component hok.mem state.rowPlan mode
        (run.planned _ hok.entry) hmode run.publicInput run.proverInput run.assumptions data
        hstable).1 row hrow⟩
  · exact ⟨(run.planValid.row_plans _ hok.entry).padding_width, fun data hstable =>
      (run.complete.padding state.component hok.mem state.rowPlan (run.planned _ hok.entry)
        run.publicInput run.proverInput run.assumptions data hstable).1⟩

lemma admissible_of_reachable {state : ComponentState (F p)} (hok : run.StateOk state)
    {mode : PreallocatedMode (F p)} (hmode : state.rowPlan.mode = .preallocated mode)
    {base input : Array (F p)} (hreachable : Reachable mode.handlers base input)
    (hbase : run.Admissible state.component base) : run.Admissible state.component input := by
  induction hreachable with
  | base => exact hbase
  | set _ handler hmem value ih =>
      refine ⟨by simp [ih.size], fun data hstable => ?_⟩
      exact (run.complete.preallocated state.component hok.mem state.rowPlan mode
        (run.planned _ hok.entry) hmode run.publicInput run.proverInput run.assumptions data
        hstable).2.2.1 _ handler hmem value (ih.assumptions data hstable)

lemma rowFacts_of_rowsOk {k : ℕ} {padded : Bool} {state : ComponentState (F p)}
    (hok : run.StateOk state) (hrows : run.RowsOk k padded state) (hk : k ≤ run.steps) :
    ∀ row ∈ state.rows, run.RowFacts state row := by
  intro row hrow
  unfold RowsOk at hrows
  split at hrows
  · rename_i mode hmode
    obtain ⟨-, hrowsEq⟩ := hrows
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrow
    obtain ⟨input, hreachable, heq⟩ := hrowsEq j hj
    rw [heq]
    exact run.rowFacts_preallocated hok hmode (run.admissible_of_reachable hok hmode hreachable
      (run.admissible_baseInput hok hmode j))
  · rename_i mode hmode
    obtain ⟨main, pad, hrowsEq, -, hvm, hanswer⟩ := hrows
    rw [hrowsEq, List.mem_append] at hrow
    rcases hrow with hrow | hrow
    · by_cases hcomponent : state.component = run.complete.vm.component
      · rw [hvm hcomponent] at hrow
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
        exact run.rowFacts_vmRow hok hcomponent (by simp at hj; omega)
      · obtain ⟨message, count, hcount, hsize, hpullable, -, rfl⟩ := hanswer hcomponent row hrow
        exact run.rowFacts_answerRow hok hcomponent hmode hcount hsize hpullable
    · rw [List.eq_of_mem_replicate hrow]
      exact run.rowFacts_padding hok hmode

/-! ### Nets of all interactions -/

omit [Fact p.Prime] in
lemma count_list_sum {α : Type} [DecidableEq α] (values : List (Multiset α)) (a : α) :
    values.sum.count a = (values.map (·.count a)).sum := by
  induction values with
  | nil => simp
  | cons head rest ih => simp [ih]

omit [Fact p.Prime] in
lemma list_sum_map_sub {α M : Type*} [AddCommGroup M] (values : List α) (f g : α → M) :
    (values.map fun x => f x - g x).sum = (values.map f).sum - (values.map g).sum := by
  induction values with
  | nil => simp
  | cons head rest ih => simp [ih]; abel

lemma rowFacts_net {state : ComponentState (F p)} {row : GeneratedRow (F p)}
    (h : run.RowFacts state row) {channel : String} (hchannel : channel ≠ run.complete.vm.channel.name)
    (message : Array (F p)) :
    netOfInteractions (rowInteractions state row run.data0) channel message =
      ((run.answeredBy state row channel).count message : F p) -
        ((run.pulledBy state row channel).count message : F p) := by
  by_cases hanswers : AnswersPull state channel
  · rw [h.answered_net channel hchannel hanswers message]
    simp [pulledBy, hanswers]
  · rw [h.answered_zero channel hchannel hanswers, net_eq_neg_pullsOf]
    · simp [pulledBy, hanswers]
    · intro interaction hmem hname
      rcases h.side interaction hmem (hname ▸ hanswers) (fun _ => hname ▸ hchannel) with
        hzero | ⟨hpull, -⟩
      · exact .inl hzero
      · exact .inr hpull

/-- The verifier's interactions off the VM channel are side interactions satisfying their prover
guarantees for every stable data. -/
lemma verifier_side {interaction : Interaction (F p)} (hmem : interaction ∈ run.verifier)
    (hname : interaction.channel.name ≠ run.complete.vm.channel.name) :
    SideInteraction ens.ensemble plan run.complete.vm.channel.name false interaction ∧
      ∀ data, run.Stable data → interaction.ProverGuarantees data := by
  refine ⟨?_, fun data hstable => ?_⟩
  · have h := (run.complete.verifier run.publicInput run.proverInput run.assumptions
      run.stableData run.stableData_stable).2
    rw [run.verifier_eq] at h
    exact (h interaction hmem hname).1
  · have h := (run.complete.verifier run.publicInput run.proverInput run.assumptions
      data hstable).2
    rw [run.verifier_eq] at h
    exact (h interaction hmem hname).2

/-- States whose rows all satisfy their facts. -/
def StatesOk (states : List (ComponentState (F p))) : Prop :=
  ∀ state ∈ states, run.StateOk state ∧ ∀ row ∈ state.rows, run.RowFacts state row

/-- Off the VM channel, the net of all interactions is what rows answer minus what is pulled. -/
lemma net_eq_answered_sub_pulled {states : List (ComponentState (F p))} (hstates : run.StatesOk states)
    {channel : String} (hchannel : channel ≠ run.complete.vm.channel.name) (message : Array (F p)) :
    netOfInteractions (run.verifier ++ statesInteractions states run.data0) channel message =
      ((run.answeredMsgs states channel).count message : F p) -
        ((run.pulledMsgs states channel).count message : F p) := by
  rw [netOfInteractions_append, net_eq_neg_pullsOf]
  · simp only [statesInteractions, ComponentState.interactionsOf, netOfInteractions_flatMap,
      answeredMsgs, pulledMsgs, count_list_sum, Multiset.count_add, List.map_map, Nat.cast_add,
      Nat.cast_list_sum]
    have hrows : ∀ state ∈ states,
        (state.rows.map fun row => netOfInteractions (rowInteractions state row run.data0) channel
          message) =
        state.rows.map fun row => ((run.answeredBy state row channel).count message : F p) -
          ((run.pulledBy state row channel).count message : F p) := by
      intro state hstate
      apply List.map_congr_left
      intro row hrow
      exact run.rowFacts_net ((hstates state hstate).2 row hrow) hchannel message
    rw [List.map_congr_left fun state hstate => congrArg List.sum (hrows state hstate)]
    simp only [list_sum_map_sub, count_list_sum, Nat.cast_list_sum, List.map_map,
      Function.comp_def]
    ring
  · intro interaction hmem hname
    rcases (run.verifier_side hmem (hname ▸ hchannel)).1 with hzero | ⟨hpull, -⟩
    · exact .inl hzero
    · exact .inr hpull

lemma components_eq {states : List (ComponentState (F p))}
    (hshape : states.map (·.shape) = run.initialShape) :
    states.map (·.component) = ens.ensemble.tables := by
  have h := congrArg (List.map (·.component)) hshape
  simp only [List.map_map, Function.comp_def, ComponentState.shape, initialShape,
    ComponentState.initial] at h
  rw [h]
  exact List.map_fst_zip (by rw [run.length_rowPlans])

lemma names_nodup {states : List (ComponentState (F p))}
    (hshape : states.map (·.shape) = run.initialShape) :
    (states.map (·.component.circuit.name)).Nodup := by
  have := ens.ensemble.unique_names
  rw [← run.components_eq hshape, List.map_map] at this
  exact this

/-- A sum over states of terms that vanish off one state. -/
lemma sum_states_eq {M : Type*} [AddCommMonoid M] {states : List (ComponentState (F p))}
    (hshape : states.map (·.shape) = run.initialShape) {state : ComponentState (F p)}
    (hstate : state ∈ states) (f : ComponentState (F p) → M)
    (hzero : ∀ other ∈ states, other.component ≠ state.component → f other = 0) :
    (states.map f).sum = f state := by
  apply sum_map_eq_of_unique (g := fun state => some state.component.circuit.name)
    (b := state.component.circuit.name)
  · change (states.filterMap (some ∘ fun state => state.component.circuit.name)).Nodup
    rw [List.filterMap_eq_map]
    exact run.names_nodup hshape
  · exact hstate
  · rfl
  · intro other hother hname
    apply hzero other hother
    intro hcomponent
    exact hname (by rw [hcomponent])

lemma exists_vm_state {states : List (ComponentState (F p))}
    (hshape : states.map (·.shape) = run.initialShape) :
    ∃ state ∈ states, state.component = run.complete.vm.component := by
  have := run.complete.vm.mem
  rw [← run.components_eq hshape] at this
  obtain ⟨state, hstate, h⟩ := List.mem_map.mp this
  exact ⟨state, hstate, h⟩

lemma telescope (k : ℕ) (message : Array (F p)) :
    ((List.range k).map fun index =>
      (if message = run.complete.vm.state run.publicInput (index + 1) then (1 : F p) else 0) -
        (if message = run.complete.vm.state run.publicInput index then 1 else 0)).sum =
      (if message = run.complete.vm.state run.publicInput k then 1 else 0) -
        (if message = run.complete.vm.state run.publicInput 0 then 1 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      ring

/-! ### The balancing invariant -/

/-- What holds of a balancing state after `k` VM steps, before or after padding. -/
structure Inv (k : ℕ) (padded : Bool) (balancing : Balancing (F p)) : Prop where
  shape : balancing.states.map (·.shape) = run.initialShape
  rows : ∀ state ∈ balancing.states, run.RowsOk k padded state
  steps_le : k ≤ run.steps
  padded_steps : padded = true → k = run.steps
  tracks : balancing.Tracks run.verifier run.data0
  canonical : Demand.Canonical balancing.demands
  interactions : balancing.interactions =
    (run.verifier ++ statesInteractions balancing.states run.data0).length
  answered_le : ∀ channel ≠ run.complete.vm.channel.name,
    run.answeredMsgs balancing.states channel ≤ run.pulledMsgs balancing.states channel
  padded_answered : padded = true → ∀ channel ≠ run.complete.vm.channel.name,
    (∀ state ∈ balancing.states, AnswersPull state channel →
      ∃ mode, state.rowPlan.mode = .demand mode) →
    run.answeredMsgs balancing.states channel = run.pulledMsgs balancing.states channel


namespace Inv

variable {run} {k : ℕ} {padded : Bool} {balancing : Balancing (F p)}

lemma statesOk (hinv : run.Inv k padded balancing) : run.StatesOk balancing.states := by
  intro state hstate
  have hok := run.stateOk_of_shape hinv.shape hstate
  exact ⟨hok, run.rowFacts_of_rowsOk hok (hinv.rows state hstate) hinv.steps_le⟩

lemma vm_rows (hinv : run.Inv k padded balancing) {state : ComponentState (F p)}
    (hstate : state ∈ balancing.states) (hvm : state.component = run.complete.vm.component) :
    ∃ pad, state.rows = (List.range k).map run.vmRow ++
      List.replicate pad (run.row state.component run.complete.vm.padding.input none) := by
  have hok := run.stateOk_of_shape hinv.shape hstate
  have hplan := StateOk.vm_rowPlan run hok hvm
  have hrows := hinv.rows state hstate
  simp only [RowsOk, hplan] at hrows
  obtain ⟨main, pad, hrowsEq, -, hmain, -⟩ := hrows
  exact ⟨pad, by rw [hrowsEq, hmain hvm]⟩

/-- On the VM channel, all interactions net the state after `k` steps against the final state. -/
lemma net_vm (hinv : run.Inv k padded balancing) (message : Array (F p)) :
    netOfInteractions (run.verifier ++ statesInteractions balancing.states run.data0)
      run.complete.vm.channel.name message =
      (if message = run.complete.vm.state run.publicInput k then 1 else 0) -
        (if message = run.complete.vm.final run.publicInput then 1 else 0) := by
  have hverifier := (run.complete.verifier run.publicInput run.proverInput run.assumptions
    run.stableData run.stableData_stable).1 message
  rw [run.verifier_eq] at hverifier
  rw [netOfInteractions_append, hverifier]
  simp only [statesInteractions, ComponentState.interactionsOf, netOfInteractions_flatMap]
  have hstates := hinv.statesOk
  rw [List.map_congr_left fun state hstate => congrArg List.sum (List.map_congr_left
    fun row hrow => ((hstates state hstate).2 row hrow).vm_net message)]
  obtain ⟨vmState, hvmState, hvm⟩ := run.exists_vm_state hinv.shape
  rw [run.sum_states_eq hinv.shape hvmState _ fun other hother hne => by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
    simp [vmNet, StateOk.name_ne_vm run (run.stateOk_of_shape hinv.shape hother) (hvm ▸ hne)]]
  obtain ⟨pad, hrows⟩ := hinv.vm_rows hvmState hvm
  rw [hrows, List.map_append, List.sum_append, List.map_map]
  have hpad : ((List.replicate pad (run.row vmState.component run.complete.vm.padding.input none)).map
      fun row => run.vmNet vmState row message).sum = 0 := by
    simp [vmNet, row]
  have hsteps : (((List.range k).map ((fun row => run.vmNet vmState row message) ∘ run.vmRow))).sum =
      ((List.range k).map fun index =>
        (if message = run.complete.vm.state run.publicInput (index + 1) then (1 : F p) else 0) -
          (if message = run.complete.vm.state run.publicInput index then 1 else 0)).sum := by
    congr 1
    apply List.map_congr_left
    intro index _
    have hname : vmState.component.circuit.name = run.complete.vm.component.circuit.name := by
      rw [hvm]
    simp only [Function.comp_apply, vmNet, hname, if_true, vmRow, row, demandOrigin, Vm.state,
      Function.iterate_succ_apply']
    by_cases hnext : message = run.complete.vm.next (run.complete.vm.next^[index]
        (run.complete.vm.initial run.publicInput)) <;>
      by_cases hcurrent : message = run.complete.vm.next^[index]
        (run.complete.vm.initial run.publicInput) <;>
      simp [hnext, hcurrent]
  rw [hpad, add_zero, hsteps, run.telescope]
  simp only [Vm.state, Function.iterate_zero, id_eq]
  by_cases hinitial : message = run.complete.vm.initial run.publicInput <;>
    by_cases hfinal : message = run.complete.vm.final run.publicInput <;>
    by_cases hstate : message = run.complete.vm.next^[k] (run.complete.vm.initial run.publicInput) <;>
    simp [hinitial, hfinal, hstate]

end Inv

end Run

end Air.Flat.WitnessGeneration
