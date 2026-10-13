module

public import Clean.Air.GenerationCompleteness

@[expose] public section

/-!
# Proof of the completeness of witness generation

A `Run` bundles a complete plan, its validated form, inputs satisfying the prover assumptions, and
the run the plan's author provides. The proof follows the generator: the initial rows, channel
balancing under an invariant that every step preserves, padding, and assembly.
-/

/-! ### Target heights -/

namespace Air.Flat.WitnessGeneration

lemma le_targetHeight {F : Type} (padding : Padding F) (rowCount : ℕ) :
    rowCount ≤ padding.targetHeight rowCount ∧
      padding.minimumRows.toNat ≤ padding.targetHeight rowCount := by
  have := Nat.le_pow_clog (b := 2) (by decide) (max rowCount padding.minimumRows.toNat)
  exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩

/-- The target height is the least power of two at least the row count and the minimum. -/
lemma targetHeight_le {F : Type} (padding : Padding F) {rowCount bound : ℕ}
    (hpower : ∃ k, bound = 2 ^ k) (hrows : rowCount ≤ bound)
    (hminimum : padding.minimumRows.toNat ≤ bound) : padding.targetHeight rowCount ≤ bound := by
  obtain ⟨k, rfl⟩ := hpower
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow (max_le hrows hminimum))

lemma targetHeight_targetHeight {F : Type} (padding : Padding F) (rowCount : ℕ) :
    padding.targetHeight (padding.targetHeight rowCount) = padding.targetHeight rowCount := by
  apply le_antisymm
  · exact targetHeight_le padding ⟨_, rfl⟩ le_rfl (le_targetHeight padding rowCount).2
  · exact (le_targetHeight padding _).1

end Air.Flat.WitnessGeneration

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
        (padded = true → main.length + pad = state.rowPlan.padding.targetHeight main.length) ∧
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
  eq_row : row = run.row state.component row.input row.origin
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
  refine ⟨by simp [vmRow, row, hvm], hvm ▸ hadmissible, ?_, ?_, ?_, ?_⟩
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
  refine ⟨rfl, hadmissible, ?_, ?_, ?_, ?_⟩
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
  refine ⟨rfl, hadmissible, fun interaction hmem _ _ => run.sideInteraction_false
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
  refine ⟨rfl, hadmissible, ?_, ?_, ?_, ?_⟩
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
    obtain ⟨main, pad, hrowsEq, -, -, hvm, hanswer⟩ := hrows
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

/-! ### The generator's view of prover data -/

end Run

omit [Fact p.Prime] in
lemma find?_key_eq {α β : Type*} [BEq β] [LawfulBEq β] {values : List α} (key : α → β)
    (hnodup : (values.map key).Nodup) {a : α} (ha : a ∈ values) :
    values.find? (fun x => key x == key a) = some a := by
  obtain ⟨found, hfound⟩ : ∃ found, values.find? (fun x => key x == key a) = some found := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨a, ha, by simp⟩
  rw [hfound]
  have hkey := List.find?_some hfound
  have hmem := List.mem_of_find?_eq_some hfound
  simp only [beq_iff_eq] at hkey
  rw [List.inj_on_of_nodup_map hnodup hmem ha hkey]

lemma honestWitgen_witnessOperationsOnly {F : Type} [FiniteField F] (data : ProverData F)
    (hint : ProverHint F) :
    (ops : List (FlatOperation F)) → (input : Array F) →
      honestWitgen data hint (witnessOperationsOnly ops) input = honestWitgen data hint ops input
  | [], _ => rfl
  | .witness m code :: ops, input => by
      simp only [witnessOperationsOnly, honestWitgen, List.foldl_cons]
      exact honestWitgen_witnessOperationsOnly data hint ops _
  | .assert _ :: ops, input | .lookup _ :: ops, input | .interact _ :: ops, input => by
      simp only [witnessOperationsOnly, honestWitgen, List.foldl_cons, honestStep]
      exact honestWitgen_witnessOperationsOnly data hint ops input

lemma flatReadsBelow_witnessOperationsOnly {F : Type} [FiniteField F] :
    (n : ℕ) → (ops : List (FlatOperation F)) → flatReadsBelow n ops = true →
      flatReadsBelow n (witnessOperationsOnly ops) = true
  | _, [], _ => rfl
  | n, .witness m code :: ops, h => by
      simp only [flatReadsBelow, Bool.and_eq_true, witnessOperationsOnly] at h ⊢
      exact ⟨h.1, flatReadsBelow_witnessOperationsOnly _ ops h.2⟩
  | n, .assert _ :: ops, h | n, .lookup _ :: ops, h | n, .interact _ :: ops, h => by
      simp only [flatReadsBelow, witnessOperationsOnly] at h ⊢
      exact flatReadsBelow_witnessOperationsOnly n ops h

lemma mem_of_mem_witnessOperationsOnly {F : Type} [FiniteField F] {op : FlatOperation F} :
    {ops : List (FlatOperation F)} → op ∈ witnessOperationsOnly ops → op ∈ ops
  | [], h => by simp [witnessOperationsOnly] at h
  | .witness m code :: ops, h => by
      simp only [witnessOperationsOnly, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_of_mem_witnessOperationsOnly h)
  | .assert _ :: ops, h | .lookup _ :: ops, h | .interact _ :: ops, h => by
      simp only [witnessOperationsOnly] at h
      exact List.mem_cons_of_mem _ (mem_of_mem_witnessOperationsOnly h)

namespace Reachable

variable {F : Type} {handlers : List PreallocatedHandler} {base input : Array F}

lemma size_eq (h : Reachable handlers base input) : input.size = base.size := by
  induction h with
  | base => rfl
  | set _ _ _ _ ih => simp [ih]

lemma getElem?_eq (h : Reachable handlers base input) {column : ℕ}
    (hcolumn : column ∉ handlers.map (·.column)) : input[column]? = base[column]? := by
  induction h with
  | base => rfl
  | set _ handler hmem _ ih =>
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, ih]
      intro heq
      exact hcolumn (List.mem_map.mpr ⟨handler, hmem, heq⟩)

end Reachable

namespace Run

variable {ens : FormalEnsemble (F p) PublicIO} {plan : GenerationPlan (F p)} (run : Run ens plan)

/-- The states generation starts from, with initial inputs as rows. -/
def initialRows : List (ComponentState (F p)) :=
  ((ens.ensemble.tables.zip run.rowPlans).map fun (component, rowPlan) =>
    ComponentState.initial component rowPlan).map fun state =>
      { state with rows := (initialInputs state run.hint).map fun input =>
        { input, values := input, undefined := state.rowPlan.mode.lazyColumns } }

lemma data0_eq : run.data0 = generatedData run.initialRows := rfl

/-- What witness programs see of a state's preallocated rows: when padding does not extend the
component, its preallocated rows with their initial inputs off the handler columns. -/
def ViewRows (state : ComponentState (F p)) : Prop :=
  ∀ mode, state.rowPlan.mode = .preallocated mode →
    state.rowPlan.padding.targetHeight mode.rows.toNat = mode.rows.toNat →
    state.rows.length = mode.rows.toNat ∧ ∀ j (hj : j < state.rows.length),
      state.rows[j].undefined = [] ∧ state.rows[j].input.size = state.component.rowOffset ∧
      ∀ column ∉ mode.handlers.map (·.column),
        state.rows[j].input[column]? = (preallocatedInput state.component mode run.hint j)[column]?

/-- States whose shape is the plan's and whose preallocated rows witness programs read are
stable. -/
structure ViewOk (states : List (ComponentState (F p))) : Prop where
  shape : states.map (·.shape) = run.initialShape
  rows : ∀ state ∈ states, run.ViewRows state

lemma find?_state {states : List (ComponentState (F p))}
    (hshape : states.map (·.shape) = run.initialShape) {entry : Component (F p) × RowPlan (F p)}
    (hentry : entry ∈ ens.ensemble.tables.zip run.rowPlans) :
    ∃ state ∈ states, states.find? (fun state => state.component.circuit.name ==
      entry.1.circuit.name) = some state ∧ state.component = entry.1 ∧ state.rowPlan = entry.2 := by
  have hmem : ComponentState.initial entry.1 entry.2 ∈ states.map (·.shape) := by
    rw [hshape]
    exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
  obtain ⟨state, hstate, hshapeEq⟩ := List.mem_map.mp hmem
  have hcomponent : state.component = entry.1 := by
    have := congrArg (·.component) hshapeEq
    simpa [ComponentState.shape, ComponentState.initial] using this
  have hrowPlan : state.rowPlan = entry.2 := by
    have := congrArg (·.rowPlan) hshapeEq
    simpa [ComponentState.shape, ComponentState.initial] using this
  refine ⟨state, hstate, ?_, hcomponent, hrowPlan⟩
  have := find?_key_eq (fun state : ComponentState (F p) => state.component.circuit.name)
    (run.names_nodup hshape) hstate
  rw [hcomponent] at this
  exact this

/-- Generation reads, before balancing, the stable data at every component padding does not
extend. -/
lemma data0_eq_stableData {component : Component (F p)} {rowPlan : RowPlan (F p)}
    {mode : PreallocatedMode (F p)}
    (hentry : (component, rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans)
    (hmode : rowPlan.mode = .preallocated mode)
    (hheight : rowPlan.padding.targetHeight mode.rows.toNat = mode.rows.toNat) :
    run.data0 component.circuit.name (size component.Input) =
      run.stableData component.circuit.name (size component.Input) := by
  rw [run.stableData_eq hentry hmode, data0_eq, initialRows]
  simp only [generatedData, List.find?_map, Function.comp_def, ComponentState.initial]
  rw [show (fun (entry : Component (F p) × RowPlan (F p)) => entry.1.circuit.name ==
      component.circuit.name) = fun entry => entry.1.circuit.name == (component, rowPlan).1.circuit.name
    from rfl, run.find?_eq hentry]
  simp only [Option.map_some, dite_true, initialInputs, hmode, List.map_map, hheight]
  congr 1
  apply List.map_congr_left
  intro row hrow
  simp only [Function.comp_apply, baseInput, List.mem_range.mp hrow, if_true, preallocatedInput]

/-- Witness programs read, through the generator's view, the stable data. -/
lemma readCell_eq {states : List (ComponentState (F p))} (hview : run.ViewOk states)
    {read : DataRead} (hread : DataReadValid ens.ensemble.tables run.rowPlans read) (row : ℕ) :
    readCell states [] read.key read.width row read.column =
      some (dataCell run.stableData read.key read.width row read.column) ∧
    dataCell run.data0 read.key read.width row read.column =
      dataCell run.stableData read.key read.width row read.column := by
  obtain ⟨target, rowPlan, mode, hfind, hwidth, hmode, hcolumn, -, hheight⟩ := hread.target
  have hentry := List.mem_of_find?_eq_some hfind
  have hkey : target.circuit.name = read.key := by simpa using List.find?_some hfind
  obtain ⟨state, hstate, hfound, hcomponent, hrowPlan⟩ := run.find?_state hview.shape hentry
  simp only at hfound hcomponent hrowPlan
  have hdata := run.data0_eq_stableData hentry hmode hheight
  rw [← hkey, hwidth]
  refine ⟨?_, by simp only [dataCell, Component.rowOffset, hdata]⟩
  have hrows := hview.rows state hstate mode (by rw [hrowPlan]; exact hmode)
    (by rw [hrowPlan]; exact hheight)
  have hstable := run.stableData_eq hentry hmode
  rw [hheight] at hstable
  simp only [Component.rowOffset]
  simp only [readCell, List.find?_nil, hfound, dataCell, hstable]
  by_cases hrow : row < mode.rows.toNat
  · have hrow' : row < state.rows.length := by rw [hrows.1]; exact hrow
    obtain ⟨hundefined, hsize, hcell⟩ := hrows.2 row hrow'
    rw [List.getElem?_eq_getElem hrow']
    simp only [hundefined, List.contains_nil, Bool.false_eq_true, if_false, hcell _ hcolumn]
    simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hrow, Option.map_some,
      Option.bind_some, Function.comp_apply, baseInput, hrow, if_true, inputRow,
      Vector.getElem?_mk, List.getElem?_toArray, List.getElem?_ofFn]
    have hpreallocated : (preallocatedInput target mode run.hint row).size = size target.Input :=
      run.preallocatedInput_size hentry hmode row
    rw [hcomponent]
    by_cases hcol : read.column < size target.Input
    · simp [hcol, Component.rowOffset]
    · simp [hcol, Component.rowOffset, Array.getElem?_eq_none (show (preallocatedInput target mode run.hint row).size ≤
        read.column by omega)]
  · rw [List.getElem?_eq_none (by rw [hrows.1]; omega)]
    simp [hrow]

lemma viewAgreesOps {states : List (ComponentState (F p))} (hview : run.ViewOk states)
    {component : Component (F p)} (hmem : component ∈ ens.ensemble.tables) :
    ViewAgreesOps states run.data0 run.stableData
      (witnessOperationsOnly component.rowOperations.toFlat) := by
  obtain ⟨rowPlan, hentry⟩ := run.exists_mem_zip hmem
  intro op hop m code hcode read hread row
  subst hcode
  have hvalid := run.planValid.data_reads _ hentry m code (mem_of_mem_witnessOperationsOnly hop)
    read hread
  obtain ⟨hreadCell, hdata⟩ := run.readCell_eq hview hvalid row
  exact ⟨hdata, hreadCell⟩

/-- On a stable view, generation completes a row as its honest row. -/
lemma completeRow_eq {states : List (ComponentState (F p))} (hview : run.ViewOk states)
    {state : ComponentState (F p)} (hok : run.StateOk state) {input : Array (F p)}
    (hsize : input.size = state.component.rowOffset) (origin : Option (Origin (F p))) :
    completeRow states [] state input run.data0 run.hint origin [] =
      (run.row state.component input origin, []) := by
  have h := witgen_eq_honestWitgen states run.data0 run.stableData run.hint
    (witnessOperationsOnly state.component.rowOperations.toFlat) input
    (flatReadsBelow_witnessOperationsOnly _ _ (hsize ▸ run.planValid.reads_below _ hok.mem))
    (run.viewAgreesOps hview hok.mem)
  simp only [completeRow, hok.witgenOps, h, row, honestRow, honestWitgen_witnessOperationsOnly]

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


omit [Fact p.Prime] in
lemma mem_sum_map {α : Type*} {β : Type} {values : List α} {f : α → Multiset β} {b : β}
    (h : b ∈ (values.map f).sum) : ∃ a ∈ values, b ∈ f a := by
  induction values with
  | nil => simp at h
  | cons head rest ih =>
      simp only [List.map_cons, List.sum_cons, Multiset.mem_add] at h
      rcases h with h | h
      · exact ⟨head, List.mem_cons_self .., h⟩
      · obtain ⟨a, ha, hb⟩ := ih h
        exact ⟨a, List.mem_cons_of_mem _ ha, hb⟩

lemma mem_pullsOf {interactions : List (Interaction (F p))} {channel : String}
    {message : Array (F p)} (h : message ∈ pullsOf interactions channel) :
    ∃ interaction ∈ interactions, interaction.channel.name = channel ∧
      interaction.assumeGuarantees = true ∧ interaction.mult = -1 ∧ interaction.msg = message := by
  simp only [pullsOf, Multiset.mem_coe, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨interaction, ⟨hmem, hname, hguarantees, hmult⟩, rfl⟩ := h
  exact ⟨interaction, hmem, hname, hguarantees, hmult, rfl⟩

/-- A pulled message has a component answering its channel, and is pullable on the declared
channel of that name. -/
lemma pulled_facts {states : List (ComponentState (F p))} (hstates : run.StatesOk states)
    {channel : String} (hchannel : channel ≠ run.complete.vm.channel.name) {message : Array (F p)}
    (hmessage : message ∈ run.pulledMsgs states channel) :
    Answers ens.ensemble plan false channel ∧
      ∀ declared ∈ ens.ensemble.channels, declared.name = channel →
        run.Pullable declared message ∧ message.size = declared.arity := by
  rcases Multiset.mem_add.mp hmessage with hverifier | hrows
  · obtain ⟨interaction, hmem, hname, -, hmult, rfl⟩ := mem_pullsOf hverifier
    obtain ⟨hside, hguarantees⟩ := run.verifier_side hmem (hname ▸ hchannel)
    have hmult' : interaction.mult ≠ 0 := by rw [hmult]; exact neg_ne_zero.mpr one_ne_zero
    refine ⟨?_, fun declared hdeclared hdeclaredName => ?_⟩
    · rcases hside with hzero | ⟨-, -, hanswers⟩
      · exact absurd hzero hmult'
      · exact hname ▸ hanswers
    · have hchannelEq := run.verifier_channel_eq hmem hdeclared (hname.trans hdeclaredName.symm)
      subst hchannelEq
      refine ⟨fun data hstable vector hvector => ?_, interaction.same_size⟩
      have hvector' : vector = interaction.msgVector := Vector.toArray_inj.mp hvector
      subst hvector'
      exact hguarantees data hstable hmult'
  · obtain ⟨state, hstate, hrow⟩ := mem_sum_map hrows
    obtain ⟨row, hrowMem, hpulled⟩ := mem_sum_map hrow
    obtain ⟨hok, hfacts⟩ := hstates state hstate
    have hrowFacts := hfacts row hrowMem
    unfold pulledBy at hpulled
    split at hpulled
    · simp at hpulled
    rename_i hnot
    obtain ⟨interaction, hmem, hname, -, hmult, rfl⟩ := mem_pullsOf hpulled
    have hmult' : interaction.mult ≠ 0 := by rw [hmult]; exact neg_ne_zero.mpr one_ne_zero
    refine ⟨?_, fun declared hdeclared hdeclaredName => ?_⟩
    · rcases hrowFacts.side interaction hmem (hname ▸ hnot) (fun _ => hname ▸ hchannel) with
        hzero | ⟨-, -, hanswers⟩
      · exact absurd hzero hmult'
      · exact hname ▸ hanswers
    · rw [hrowFacts.eq_row, run.rowInteractions_row hok.interactions hok.mem
        hrowFacts.admissible.size _ run.stableData_stable] at hmem
      refine ⟨run.pullable_of_row hok.mem hrowFacts.admissible hmem hdeclared
        (hname.trans hdeclaredName.symm) hmult', ?_⟩
      obtain ⟨abstract, habstract, rfl⟩ := List.mem_map.mp hmem
      rw [← channel_eq_of_mem hok.mem habstract hdeclared (hname.trans hdeclaredName.symm)]
      exact (abstract.eval _).same_size

/-! ### Row bounds -/

lemma card_pullsOf_map (interactions : List (AbstractInteraction (F p))) (env : Environment (F p))
    (channel : String) :
    Multiset.card (pullsOf (interactions.map (·.eval env)) channel) ≤
      (interactions.filter fun interaction =>
        interaction.channel.name == channel && interaction.assumeGuarantees).length := by
  simp only [pullsOf, Multiset.coe_card, List.length_map, List.filter_map, Function.comp_def]
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro interaction h
  have h' := of_decide_eq_true h
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨h'.1, h'.2.1⟩

omit [Fact p.Prime] in
lemma card_list_sum {α : Type} (values : List (Multiset α)) :
    Multiset.card values.sum = (values.map Multiset.card).sum := by
  induction values with
  | nil => simp
  | cons head rest ih => simp [ih]

lemma card_pulledBy_le {state : ComponentState (F p)} (hok : run.StateOk state)
    (row : GeneratedRow (F p)) (channel : String) :
    Multiset.card (run.pulledBy state row channel) ≤
      if AnswersPull state channel then 0 else pullsOn state.component channel := by
  unfold pulledBy
  split
  · simp
  · simp only [rowInteractions, hok.interactions]
    exact card_pullsOf_map _ _ channel

lemma card_pulledMsgs_le {states : List (ComponentState (F p))}
    (hok : ∀ state ∈ states, run.StateOk state) (channel : String) :
    Multiset.card (run.pulledMsgs states channel) ≤
      verifierPullsOn ens.ensemble channel + (states.map fun state =>
        if AnswersPull state channel then 0
        else state.rows.length * pullsOn state.component channel).sum := by
  simp only [pulledMsgs, Multiset.card_add]
  apply Nat.add_le_add
  · exact card_pullsOf_map _ _ channel
  · rw [card_list_sum]
    simp only [List.map_map, Function.comp_def]
    apply List.sum_le_sum
    intro state hstate
    rw [card_list_sum]
    simp only [List.map_map, Function.comp_def]
    calc (state.rows.map fun row => Multiset.card (run.pulledBy state row channel)).sum
        ≤ (state.rows.map fun _ => if AnswersPull state channel then 0
            else pullsOn state.component channel).sum :=
          List.sum_le_sum fun row _ => run.card_pulledBy_le (hok state hstate) row channel
      _ = _ := by split <;> simp

/-- The row bounds of the run. -/
abbrev bound : String → ℕ := run.complete.rowBound run.steps

omit [Fact p.Prime] in
lemma padded_le {F : Type} {padding : Padding F} {padded : Bool} {main pad bound : ℕ}
    (hpower : ∃ k, bound = 2 ^ k) (hminimum : padding.minimumRows.toNat ≤ bound)
    (hmain : main ≤ bound) (hpad : padded = false → pad = 0)
    (htarget : padded = true → main + pad = padding.targetHeight main) : main + pad ≤ bound := by
  cases padded
  · rw [hpad rfl]; simpa using hmain
  · rw [htarget rfl]; exact targetHeight_le padding hpower hmain hminimum

lemma card_answeredBy_ge {state : ComponentState (F p)} {mode : DemandMode (F p)}
    (hmode : state.rowPlan.mode = .demand mode) {main : List (GeneratedRow (F p))} {pad : ℕ}
    (hrows : state.rows = main ++
      List.replicate pad (run.row state.component state.rowPlan.padding.input none))
    (hanswer : ∀ row ∈ main, ∃ message count, 0 < count ∧ row = run.answerRow state.component mode
      message count) :
    main.length ≤
      Multiset.card ((state.rows.map fun row => run.answeredBy state row mode.channel.name).sum) := by
  rw [card_list_sum, hrows, List.map_append, List.map_append, List.sum_append]
  have hpadding : ((List.replicate pad (run.row state.component state.rowPlan.padding.input none)).map
      (fun row => run.answeredBy state row mode.channel.name)).map Multiset.card = List.replicate pad 0 := by
    simp [answeredBy, hmode, row]
  rw [List.map_map, hpadding, List.sum_replicate, smul_zero, add_zero]
  calc main.length = (main.map fun _ => 1).sum := by simp
    _ ≤ _ := by
      apply List.sum_le_sum
      intro row hrow
      obtain ⟨message, count, hcount, rfl⟩ := hanswer row hrow
      simp [answeredBy, hmode, answerRow, row, demandOrigin]
      omega


/-! ### Generator steps -/

omit [Fact p.Prime] in
lemma findAction_some {F : Type} [FiniteField F] {states : List (ComponentState F)} :
    ∀ {demands : List (Demand F)} {demand : Demand F} {index : ℕ},
      findAction states demands = some (demand, index) →
      demand ∈ demands ∧ ∃ state, states[index]? = some state ∧ state.handles demand = true
  | [], _, _, h => by simp [findAction] at h
  | head :: rest, demand, index, h => by
      simp only [findAction] at h
      split at h
      · rename_i found hfound
        cases h
        obtain ⟨hlt, hhandles, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfound
        exact ⟨List.mem_cons_self .., _, List.getElem?_eq_getElem hlt, hhandles⟩
      · obtain ⟨hmem, rest⟩ := findAction_some h
        exact ⟨List.mem_cons_of_mem _ hmem, rest⟩

omit [Fact p.Prime] in
lemma findAction_isSome {F : Type} [FiniteField F] {states : List (ComponentState F)} :
    ∀ {demands : List (Demand F)}, (∃ demand ∈ demands, ∃ state ∈ states,
      state.handles demand = true) → ∃ result, findAction states demands = some result
  | [], h => by simp at h
  | head :: rest, ⟨demand, hmem, state, hstate, hhandles⟩ => by
      simp only [findAction]
      split
      · exact ⟨_, rfl⟩
      · rename_i hnone
        rcases List.mem_cons.mp hmem with rfl | hmem
        · rw [List.findIdx?_eq_none_iff] at hnone
          exact absurd hhandles (by simpa using hnone state hstate)
        · exact findAction_isSome ⟨demand, hmem, state, hstate, hhandles⟩

lemma handles_iff {state : ComponentState (F p)} (hok : run.StateOk state) (demand : Demand (F p)) :
    state.handles demand = true ↔
      (demand.channel, demand.direction) ∈ state.rowPlan.mode.handled state.component := by
  rcases hmode : state.rowPlan.mode with mode | mode
  · simp only [ComponentState.handles, hmode, Mode.handled, List.mem_singleton, Prod.mk.injEq,
      Bool.and_eq_true, beq_iff_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
  · simp only [ComponentState.handles, hmode, Mode.handled, List.any_eq_true, List.mem_filterMap,
      PreallocatedHandler.handles, hok.interactions, Option.map_eq_some_iff]
    constructor
    · rintro ⟨handler, hmem, h⟩
      split at h
      · simp at h
      · rename_i interaction hinteraction
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨handler, hmem, interaction, hinteraction, by rw [h.1, h.2]⟩
    · rintro ⟨handler, hmem, interaction, hinteraction, h⟩
      refine ⟨handler, hmem, ?_⟩
      rw [hinteraction]
      simp only [Prod.mk.injEq] at h
      simp [h.1, h.2]

lemma val_eq (x : F p) : FiniteField.val x = ZMod.val x := rfl

lemma size_eq : FiniteField.size (F := F p) = p := rfl

/-- A demand of `δ` pulls. -/
lemma demand_pull {demand : Demand (F p)} {δ : ℕ} (hmult : demand.multiplicity = -(δ : F p))
    (hpos : 0 < δ) (hlt : 2 * δ < p) : demand.direction = .pull ∧ demand.count = δ := by
  have hδ : δ < p := by omega
  have hne : (δ : F p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hpos h) (by omega)
  have hval : ZMod.val (δ : F p) = δ := ZMod.val_natCast_of_lt hδ
  have hneg : ZMod.val (-(δ : F p)) = p - δ := by rw [ZMod.neg_val, if_neg hne, hval]
  have hnot : ¬ 2 * ZMod.val (-(δ : F p)) ≤ p := by rw [hneg]; omega
  simp only [Demand.direction, Demand.count, Demand.surplus, hmult, val_eq, size_eq, if_neg hnot,
    neg_neg, hval, and_self]

/-- A demand of one push. -/
lemma demand_push {demand : Demand (F p)} (hmult : demand.multiplicity = 1) :
    demand.direction = .push ∧ demand.count = 1 := by
  have hp := (Fact.out : p.Prime).two_le
  have hval : ZMod.val (1 : F p) = 1 := ZMod.val_one_eq_one_mod p ▸ Nat.mod_eq_of_lt (by omega)
  have hle : 2 * ZMod.val (1 : F p) ≤ p := by rw [hval]; omega
  simp only [Demand.direction, Demand.count, Demand.surplus, hmult, val_eq, size_eq, hval]
  rw [if_pos (by omega)]
  exact ⟨rfl, rfl⟩

omit [Fact p.Prime] in
lemma sum_map_set_add {α : Type*} {M : Type*} [AddCommMonoid M] (f : α → M) :
    ∀ (values : List α) (index : ℕ) (hindex : index < values.length) (value : α),
      ((values.set index value).map f).sum + f values[index] = (values.map f).sum + f value
  | [], _, hindex, _ => absurd hindex (by simp)
  | head :: tail, 0, _, value => by
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]
      abel
  | head :: tail, index + 1, hindex, value => by
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      rw [add_assoc, sum_map_set_add f tail index (by simpa using hindex) value, add_assoc]

/-- Handling a demand with a demand-driven component that defines no cell. -/
lemma handle_demand {states : List (ComponentState (F p))} {index : ℕ}
    {state : ComponentState (F p)} (hstate : states[index]? = some state)
    {mode : DemandMode (F p)} (hmode : state.rowPlan.mode = .demand mode) (demand : Demand (F p))
    (hdefinitions : (handleDemand states state mode demand run.data0 run.hint).definitions = []) :
    let mutation := handleDemand states state mode demand run.data0 run.hint
    handle states demand index run.data0 run.hint = .ok (states.set index mutation.state,
      ⟨mutation.removedRows.flatMap (rowInteractions state · run.data0),
        mutation.addedRows.flatMap (rowInteractions state · run.data0)⟩) := by
  simp [handle, hstate, hmode, hdefinitions, define, Change.append, pure, Except.pure, bind,
    Except.bind]

/-- Handling a demand with a preallocated row that defines no cell. -/
lemma handle_preallocated {states : List (ComponentState (F p))} {index : ℕ}
    {state : ComponentState (F p)} (hstate : states[index]? = some state)
    {mode : PreallocatedMode (F p)} (hmode : state.rowPlan.mode = .preallocated mode)
    {demand : Demand (F p)} {mutation : Mutation (F p)}
    (hmutation : handlePreallocated states state mode.handlers demand run.data0 run.hint =
      some mutation) (hdefinitions : mutation.definitions = []) :
    handle states demand index run.data0 run.hint = .ok (states.set index mutation.state,
      ⟨mutation.removedRows.flatMap (rowInteractions state · run.data0),
        mutation.addedRows.flatMap (rowInteractions state · run.data0)⟩) := by
  simp [handle, hstate, hmode, hmutation, hdefinitions, define, Change.append, pure, Except.pure,
    bind, Except.bind]

omit [Fact p.Prime] in
lemma length_statesInteractions {F : Type} [FiniteField F] (states : List (ComponentState F))
    (data : ProverData F) : (statesInteractions states data).length =
      (states.map fun state => state.rows.length * state.interactions.length).sum := by
  simp [statesInteractions, ComponentState.interactionsOf, List.length_flatMap, rowInteractions]

lemma card_pullsOf_le (interactions : List (Interaction (F p))) (channel : String) :
    Multiset.card (pullsOf interactions channel) ≤ interactions.length := by
  simp only [pullsOf, Multiset.coe_card, List.length_map]
  exact List.length_filter_le _ _

lemma card_pulledMsgs_le_length (states : List (ComponentState (F p))) (channel : String) :
    Multiset.card (run.pulledMsgs states channel) ≤
      (run.verifier ++ statesInteractions states run.data0).length := by
  simp only [pulledMsgs, Multiset.card_add, List.length_append, statesInteractions,
    ComponentState.interactionsOf, List.length_flatMap, card_list_sum, List.map_map]
  apply Nat.add_le_add (card_pullsOf_le _ _)
  apply List.sum_le_sum
  intro state _
  simp only [Function.comp_apply, card_list_sum, List.map_map]
  apply List.sum_le_sum
  intro row _
  simp only [Function.comp_apply, pulledBy]
  split
  · simp
  · exact card_pullsOf_le _ _

omit [Fact p.Prime] in
lemma mem_set_cases {α : Type*} {values : List α} {index : ℕ} {value x : α}
    (h : x ∈ values.set index value) :
    x = value ∨ ∃ j, ∃ hj : j < values.length, j ≠ index ∧ values[j] = x := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  by_cases hji : index = j
  · subst hji
    exact .inl (by simp)
  · exact .inr ⟨j, by simpa using hj, Ne.symm hji, by rw [List.getElem_set_ne hji]⟩

/-- The rows of a component other than the VM do not depend on the VM steps. -/
lemma rowsOk_of_ne_vm {k k' : ℕ} {padded : Bool} {state : ComponentState (F p)}
    (hvm : state.component ≠ run.complete.vm.component) (h : run.RowsOk k padded state) :
    run.RowsOk k' padded state := by
  unfold RowsOk at h ⊢
  split at h
  · exact h
  · obtain ⟨main, pad, hrows, hpad, htarget, -, hanswer⟩ := h
    exact ⟨main, pad, hrows, hpad, htarget, fun h => absurd h hvm, hanswer⟩

/-- States other than the replaced one keep their component, which differs from the replaced
one's. -/
lemma component_ne_of_set {states : List (ComponentState (F p))}
    (hshape : states.map (·.shape) = run.initialShape) {index : ℕ} {state : ComponentState (F p)}
    (hstate : states[index]? = some state) {j : ℕ} (hj : j < states.length) (hji : j ≠ index) :
    states[j].component ≠ state.component := by
  intro heq
  obtain ⟨hindex, rfl⟩ := List.getElem?_eq_some_iff.mp hstate
  have := (List.Nodup.getElem_inj_iff (run.names_nodup hshape) (i := j) (j := index)
    (hi := by simpa using hj) (hj := by simpa using hindex)).mp
    (by simpa using congrArg (fun component : Component (F p) => component.circuit.name) heq)
  exact hji this

/-- Replacing a state's rows changes the answered and pulled messages by that state's. -/
lemma answeredMsgs_set {states : List (ComponentState (F p))} {index : ℕ}
    {state : ComponentState (F p)} (hstate : states[index]? = some state)
    (rows : List (GeneratedRow (F p))) (channel : String) :
    run.answeredMsgs (states.set index { state with rows }) channel +
        (state.rows.map fun row => run.answeredBy state row channel).sum =
      run.answeredMsgs states channel + (rows.map fun row => run.answeredBy state row channel).sum := by
  obtain ⟨hindex, rfl⟩ := List.getElem?_eq_some_iff.mp hstate
  exact sum_map_set_add (fun state => (state.rows.map fun row =>
    run.answeredBy state row channel).sum) states index hindex _

lemma pulledMsgs_set {states : List (ComponentState (F p))} {index : ℕ}
    {state : ComponentState (F p)} (hstate : states[index]? = some state)
    (rows : List (GeneratedRow (F p))) (channel : String) :
    run.pulledMsgs (states.set index { state with rows }) channel +
        (state.rows.map fun row => run.pulledBy state row channel).sum =
      run.pulledMsgs states channel + (rows.map fun row => run.pulledBy state row channel).sum := by
  obtain ⟨hindex, rfl⟩ := List.getElem?_eq_some_iff.mp hstate
  simp only [pulledMsgs, add_assoc]
  rw [sum_map_set_add (fun state => (state.rows.map fun row =>
    run.pulledBy state row channel).sum) states index hindex _]
  rfl

omit [Fact p.Prime] in
lemma length_statesInteractions_set {F : Type} [FiniteField F] {states : List (ComponentState F)}
    {index : ℕ} {state : ComponentState F} (hstate : states[index]? = some state)
    (rows : List (GeneratedRow F)) (data : ProverData F) :
    (statesInteractions (states.set index { state with rows }) data).length +
        state.rows.length * state.interactions.length =
      (statesInteractions states data).length + rows.length * state.interactions.length := by
  obtain ⟨hindex, rfl⟩ := List.getElem?_eq_some_iff.mp hstate
  rw [length_statesInteractions, length_statesInteractions]
  exact sum_map_set_add (fun state => state.rows.length * state.interactions.length) states index
    hindex _

lemma length_rowInteractions_flatMap {F : Type} [FiniteField F] (state : ComponentState F)
    (rows : List (GeneratedRow F)) (data : ProverData F) :
    (rows.flatMap (rowInteractions state · data)).length = rows.length * state.interactions.length := by
  simp [List.length_flatMap, rowInteractions, mul_comm]

/-- Before the final state, the VM moves. -/
lemma next_ne {index : ℕ} (hindex : index < run.steps) :
    run.complete.vm.next (run.complete.vm.state run.publicInput index) ≠
      run.complete.vm.state run.publicInput index := by
  intro hstuck
  have hconstant : ∀ j, run.complete.vm.state run.publicInput (index + j) =
      run.complete.vm.state run.publicInput index := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [← Nat.add_assoc, show run.complete.vm.state run.publicInput (index + j + 1) =
          run.complete.vm.next (run.complete.vm.state run.publicInput (index + j)) by
            simp only [Vm.state, Function.iterate_succ_apply'], ih, hstuck]
  have := hconstant (run.steps - index)
  rw [Nat.add_sub_cancel' hindex.le, run.reaches] at this
  exact run.distinct index hindex this.symm

lemma measure_lt_left {balancing balancing' : Balancing (F p)} (hlt : balancing.interactions < p)
    (hgt : balancing.interactions < balancing'.interactions) :
    Prod.Lex (· < ·) (· < ·) balancing'.measure balancing.measure :=
  Prod.Lex.left _ _ (show p - balancing'.interactions < p - balancing.interactions by omega)

lemma measure_lt_right {balancing balancing' : Balancing (F p)}
    (heq : balancing'.interactions = balancing.interactions)
    (hlt : balancing'.demands.length < balancing.demands.length) :
    Prod.Lex (· < ·) (· < ·) balancing'.measure balancing.measure := by
  simp only [Balancing.measure, heq]
  exact Prod.Lex.right _ hlt

/-- The contribution of one interaction to the net of a channel message. -/
def contribution {F : Type} [FiniteField F] (channel : String) (message : Array F)
    (interaction : Interaction F) : F :=
  if interaction.channel.name = channel ∧ interaction.msg = message then interaction.mult else 0

lemma netOfInteractions_eq_sum {F : Type} [FiniteField F] (interactions : List (Interaction F))
    (channel : String) (message : Array F) :
    netOfInteractions interactions channel message =
      (interactions.map (contribution channel message)).sum := by
  induction interactions with
  | nil => rfl
  | cons interaction rest ih =>
      rw [netOfInteractions_cons, ih]
      simp [contribution]

lemma netOfInteractions_set {F : Type} [FiniteField F] (interactions : List (Interaction F))
    {index : ℕ} (hindex : index < interactions.length) (value : Interaction F) (channel : String)
    (message : Array F) :
    netOfInteractions (interactions.set index value) channel message =
      netOfInteractions interactions channel message -
        contribution channel message interactions[index] + contribution channel message value := by
  rw [netOfInteractions_eq_sum, netOfInteractions_eq_sum, sum_map_set _ _ _ hindex]

omit [Fact p.Prime] in
lemma eq_set_of_agree {α : Type*} {values values' : List α} (hlength : values'.length = values.length)
    {index : ℕ} (hindex : index < values.length)
    (hagree : ∀ i ≠ index, values'[i]? = values[i]?) :
    values' = values.set index (values'[index]'(hlength ▸ hindex)) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i = index
  · subst hi
    simp [List.getElem?_set_self hindex, List.getElem?_eq_getElem (hlength ▸ hindex)]
  · rw [List.getElem?_set_ne (Ne.symm hi), hagree i hi]

lemma findPreallocatedRow_some {F : Type} [FiniteField F] {state : ComponentState F}
    {handlers : List PreallocatedHandler} {demand : Demand F} {data : ProverData F}
    {handler : PreallocatedHandler} {position : ℕ} {row : GeneratedRow F}
    (h : findPreallocatedRow state handlers demand data = some (handler, position, row)) :
    handler ∈ handlers ∧ handler.handles state demand = true ∧ state.rows[position]? = some row ∧
      ∃ interaction, state.interactions[handler.interaction]? = some interaction ∧
        (interaction.eval (Environment.fromArray row.values data)).msg = demand.message := by
  obtain ⟨handler', hmem, hfound⟩ := List.exists_of_findSome?_eq_some h
  split at hfound
  · rename_i hhandles
    obtain ⟨position', row', hrow, hg⟩ := getElem?_of_findSome?_zipIdx hfound
    rcases hinteraction : state.interactions[handler'.interaction]? with _ | interaction
    · simp [hinteraction] at hg
    simp only [hinteraction, Option.bind_some] at hg
    split at hg
    · rename_i hmsg
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl, rfl⟩ := hg
      exact ⟨hmem, hhandles, hrow, interaction, hinteraction, by simpa using hmsg⟩
    · simp at hg
  · simp at hfound

lemma findPreallocatedRow_isSome {F : Type} [FiniteField F] {state : ComponentState F}
    {handlers : List PreallocatedHandler} {demand : Demand F} {data : ProverData F}
    {handler : PreallocatedHandler} (hmem : handler ∈ handlers)
    (hhandles : handler.handles state demand = true) {position : ℕ} {row : GeneratedRow F}
    (hrow : state.rows[position]? = some row) {interaction : AbstractInteraction F}
    (hinteraction : state.interactions[handler.interaction]? = some interaction)
    (hmsg : (interaction.eval (Environment.fromArray row.values data)).msg = demand.message) :
    ∃ result, findPreallocatedRow state handlers demand data = some result := by
  rw [← Option.isSome_iff_exists]
  unfold findPreallocatedRow
  rw [List.findSome?_isSome_iff]
  refine ⟨handler, hmem, ?_⟩
  rw [if_pos hhandles, Option.isSome_iff_exists]
  rw [← Option.isSome_iff_exists, List.findSome?_isSome_iff]
  refine ⟨(row, position), List.mem_zipIdx_iff_getElem?.mpr hrow, ?_⟩
  simp [hinteraction, hmsg]

/-- Changing handler columns keeps the message of every handled interaction. -/
lemma msg_reachable {state : ComponentState (F p)} (hok : run.StateOk state)
    {mode : PreallocatedMode (F p)} (hmode : state.rowPlan.mode = .preallocated mode)
    {handler : PreallocatedHandler} {interaction : AbstractInteraction (F p)}
    (hinteraction : state.component.rowOperations.interactions[handler.interaction]? =
      some interaction) {base input : Array (F p)} (hreachable : Reachable mode.handlers base input)
    (hbase : run.Admissible state.component base) :
    (interaction.eval (run.rowEnv state.component input run.stableData).toEnvironment).msg =
      (interaction.eval (run.rowEnv state.component base run.stableData).toEnvironment).msg := by
  induction hreachable with
  | base => rfl
  | set hprevious handler' hmem value ih =>
      rename_i previous
      have hadmissible := run.admissible_of_reachable hok hmode hprevious hbase
      have hadmissible' := run.admissible_of_reachable hok hmode (hprevious.set handler' hmem value)
        hbase
      obtain ⟨interaction', hinteraction', -, -, hfacts⟩ :=
        (run.complete.preallocated state.component hok.mem state.rowPlan mode
          (run.planned _ hok.entry) hmode run.publicInput run.proverInput run.assumptions
          run.stableData run.stableData_stable).2.2.2.2 handler' hmem
      obtain ⟨-, -, hset⟩ := hfacts previous _ (run.honestEnv_row hok.mem hadmissible.size _) rfl rfl
        (hadmissible.assumptions _ run.stableData_stable)
      obtain ⟨hmsg, hother⟩ := hset value _ (run.honestEnv_row hok.mem hadmissible'.size _) rfl rfl
      rw [← ih]
      by_cases hindex : handler.interaction = handler'.interaction
      · rw [hindex] at hinteraction
        rw [hinteraction] at hinteraction'
        cases hinteraction'
        exact hmsg
      · have := hother handler.interaction hindex
        simp only [interactionsIn, List.getElem?_map, hinteraction, Option.map_some,
          Option.some.injEq] at this
        exact congrArg (·.msg) this

/-- What a preallocated row answers on the channel of one of its handlers. -/
lemma answeredBy_preallocated {state : ComponentState (F p)} (hok : run.StateOk state)
    {mode : PreallocatedMode (F p)} (hmode : state.rowPlan.mode = .preallocated mode)
    {input : Array (F p)} (hadmissible : run.Admissible state.component input)
    {handler : PreallocatedHandler} (hhandler : handler ∈ mode.handlers)
    {interaction : AbstractInteraction (F p)}
    (hinteraction : state.component.rowOperations.interactions[handler.interaction]? =
      some interaction) :
    run.answeredBy state (run.row state.component input none) interaction.channel.name =
      Multiset.replicate (input[handler.column]?.getD 0).val
        (interaction.eval (run.rowEnv state.component input run.stableData).toEnvironment).msg := by
  have hnodup := run.handled_nodup hok.entry
  simp only [hmode, Mode.handled] at hnodup
  have hpush : ∀ handler ∈ mode.handlers, ∀ interaction,
      state.component.rowOperations.interactions[handler.interaction]? = some interaction →
      interaction.assumeGuarantees = false := by
    intro handler hmem interaction hinteraction
    obtain ⟨interaction', hinteraction', -, -, hfacts⟩ :=
      (run.complete.preallocated state.component hok.mem state.rowPlan mode
        (run.planned _ hok.entry) hmode run.publicInput run.proverInput run.assumptions
        run.stableData run.stableData_stable).2.2.2.2 handler hmem
    rw [hinteraction] at hinteraction'
    cases hinteraction'
    exact (hfacts input _ (run.honestEnv_row hok.mem hadmissible.size _) rfl rfl
      (hadmissible.assumptions _ run.stableData_stable)).1
  have hhandled : ∀ handler ∈ mode.handlers, ∀ interaction,
      state.component.rowOperations.interactions[handler.interaction]? = some interaction →
      (state.component.rowOperations.interactions[handler.interaction]?.map fun interaction =>
        (interaction.channel.name, handlerDirection interaction)) =
        some (interaction.channel.name, Direction.pull) := by
    intro handler hmem interaction hinteraction
    rw [hinteraction]
    simp [handlerDirection, hpush handler hmem interaction hinteraction]
  simp only [answeredBy, hmode]
  rw [sum_map_eq_of_unique hnodup hhandler (hhandled handler hhandler interaction hinteraction)]
  · rw [hok.interactions, hinteraction]
    simp only [if_true, row]
    congr 2
    apply interaction_eval_congr
    rfl
  · intro handler' hmem' hne
    rw [hok.interactions]
    split
    · rename_i interaction' hinteraction'
      rw [if_neg]
      intro hname
      exact hne (by rw [hhandled handler' hmem' interaction' hinteraction', hname])
    · rfl

/-! ### Initial states -/

lemma no_lazy {component : Component (F p)} {rowPlan : RowPlan (F p)}
    (hentry : (component, rowPlan) ∈ ens.ensemble.tables.zip run.rowPlans) :
    rowPlan.mode.lazyColumns = [] := by
  rcases hmode : rowPlan.mode with mode | mode
  · rfl
  · exact run.complete.no_lazy component (List.of_mem_zip hentry).1 rowPlan mode
      (run.planned _ hentry) hmode

lemma mem_initialRows {state : ComponentState (F p)} (hstate : state ∈ run.initialRows) :
    ∃ entry ∈ ens.ensemble.tables.zip run.rowPlans,
      state = { ComponentState.initial entry.1 entry.2 with
        rows := (initialInputs (ComponentState.initial entry.1 entry.2) run.hint).map fun input =>
          { input, values := input, undefined := entry.2.mode.lazyColumns } } := by
  simp only [initialRows, List.map_map, List.mem_map] at hstate
  obtain ⟨entry, hentry, rfl⟩ := hstate
  exact ⟨entry, hentry, rfl⟩

lemma initialRows_shape : run.initialRows.map (·.shape) = run.initialShape := by
  simp only [initialRows, initialShape, List.map_map]
  apply List.map_congr_left
  intro entry _
  rfl

lemma initialRows_viewOk : run.ViewOk run.initialRows := by
  refine ⟨run.initialRows_shape, fun state hstate mode hmode _ => ?_⟩
  obtain ⟨⟨component, rowPlan⟩, hentry, rfl⟩ := run.mem_initialRows hstate
  simp only [ComponentState.initial] at hmode ⊢
  have hlazy := run.no_lazy hentry
  rw [hmode] at hlazy
  simp only [initialInputs, hmode, List.map_map, List.length_map, List.length_range, true_and]
  intro j hj
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  exact ⟨hlazy, run.preallocatedInput_size hentry hmode j, fun column _ => rfl⟩

lemma initialRows_stateOk {state : ComponentState (F p)} (hstate : state ∈ run.initialRows) :
    run.StateOk state :=
  run.stateOk_of_shape run.initialRows_shape hstate

/-- Completing rows on a stable view computes their honest rows. -/
lemma completeRows_eq {view : List (ComponentState (F p))} (hview : run.ViewOk view)
    {state : ComponentState (F p)} (hok : run.StateOk state) :
    ∀ rows : List (GeneratedRow (F p)), (∀ row ∈ rows, row.origin = none ∧ row.undefined = [] ∧
      row.input.size = state.component.rowOffset) →
    completeRows run.data0 run.hint view state rows [] =
      (rows.map fun row => run.row state.component row.input none, [])
  | [], _ => rfl
  | row :: rows, hrows => by
      obtain ⟨horigin, hundefined, hsize⟩ := hrows row (List.mem_cons_self ..)
      simp only [completeRows, horigin, hundefined, run.completeRow_eq hview hok hsize,
        completeRows_eq hview hok rows fun row hrow => hrows row (List.mem_cons_of_mem _ hrow),
        List.map_cons]

lemma completeStates_eq {view : List (ComponentState (F p))} (hview : run.ViewOk view) :
    ∀ states : List (ComponentState (F p)), (∀ state ∈ states, run.StateOk state ∧
      ∀ row ∈ state.rows, row.origin = none ∧ row.undefined = [] ∧
        row.input.size = state.component.rowOffset) →
    completeStates run.data0 run.hint view states [] =
      (states.map fun state => { state with rows := (state.rows.map fun row =>
        run.row state.component row.input none) }, [])
  | [], _ => rfl
  | state :: states, hstates => by
      obtain ⟨hok, hrows⟩ := hstates state (List.mem_cons_self ..)
      simp only [completeStates, run.completeRows_eq hview hok state.rows hrows,
        completeStates_eq hview states fun state hstate => hstates state (List.mem_cons_of_mem _
          hstate), List.map_cons]

/-- The states generation starts balancing from. -/
def initial : List (ComponentState (F p)) :=
  run.initialRows.map fun state => { state with rows := (state.rows.map fun row =>
    run.row state.component row.input none) }

lemma initialStates_eq : initialStates run.validPlan run.hint = (run.initial, run.data0) := by
  have hrows : ∀ state ∈ run.initialRows, run.StateOk state ∧ ∀ row ∈ state.rows,
      row.origin = none ∧ row.undefined = [] ∧ row.input.size = state.component.rowOffset := by
    intro state hstate
    refine ⟨run.initialRows_stateOk hstate, fun row hrow => ?_⟩
    obtain ⟨⟨component, rowPlan⟩, hentry, rfl⟩ := run.mem_initialRows hstate
    simp only [ComponentState.initial, List.mem_map] at hrow ⊢
    obtain ⟨input, hinput, rfl⟩ := hrow
    refine ⟨rfl, run.no_lazy hentry, ?_⟩
    simp only [initialInputs] at hinput
    split at hinput
    · simp at hinput
    · rename_i mode hmode
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hinput
      exact run.preallocatedInput_size hentry hmode j
  have hcomplete := run.completeStates_eq run.initialRows_viewOk run.initialRows hrows
  simp only [initialStates]
  rw [← initialRows, ← data0_eq, hcomplete]
  rfl

/-- The balancing state generation starts from. -/
def initialBalancing : Balancing (F p) where
  states := run.initial
  demands := Demand.addInteractions [] (run.verifier ++ statesInteractions run.initial run.data0)
  interactions := (run.verifier ++ statesInteractions run.initial run.data0).length

lemma mem_initial {state : ComponentState (F p)} (hstate : state ∈ run.initial) :
    ∃ entry ∈ ens.ensemble.tables.zip run.rowPlans,
      state = { ComponentState.initial entry.1 entry.2 with
        rows := (initialInputs (ComponentState.initial entry.1 entry.2) run.hint).map fun input =>
          run.row entry.1 input none } := by
  simp only [initial, List.mem_map] at hstate
  obtain ⟨state', hstate', rfl⟩ := hstate
  obtain ⟨entry, hentry, rfl⟩ := run.mem_initialRows hstate'
  exact ⟨entry, hentry, by simp [ComponentState.initial, List.map_map, Function.comp_def]⟩

lemma initial_inv : run.Inv 0 false run.initialBalancing := by
  have hshape : run.initial.map (·.shape) = run.initialShape := by
    rw [← run.initialRows_shape]
    simp only [initial, List.map_map]
    rfl
  refine ⟨hshape, ?_, Nat.zero_le _, (fun h => absurd h (by simp)), (fun channel message => ?_),
    Demand.canonical_nil.addInteractions _, rfl, (fun channel _ => ?_),
    (fun h => absurd h (by simp))⟩
  · intro state hstate
    obtain ⟨⟨component, rowPlan⟩, hentry, rfl⟩ := run.mem_initial hstate
    unfold RowsOk
    simp only [ComponentState.initial]
    split
    · rename_i mode hmode
      simp only [initialInputs, hmode, List.map_map, List.length_map, List.length_range,
        Bool.false_eq_true, if_false, true_and]
      intro j hj
      refine ⟨preallocatedInput component mode run.hint j, ?_, ?_⟩
      · have : run.baseInput component rowPlan mode j = preallocatedInput component mode run.hint j :=
          by simp [baseInput, hj]
        rw [this]
        exact .base
      · simp [preallocatedInput]
    · rename_i mode hmode
      refine ⟨[], 0, by simp [initialInputs, hmode], fun _ => rfl,
        (fun h => absurd h (by simp)), fun _ => rfl, fun _ row hrow => absurd hrow (by simp)⟩
  · simp [initialBalancing, netOf_addInteractions]
  · simp only [initialBalancing]
    suffices h : run.answeredMsgs run.initial channel = 0 by rw [h]; exact Multiset.zero_le _
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨state, hstate, rfl⟩ := List.mem_map.mp hx
    obtain ⟨⟨component, rowPlan⟩, hentry, rfl⟩ := run.mem_initial hstate
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
    simp only [ComponentState.initial, initialInputs] at hrow ⊢
    rcases hmode : rowPlan.mode with mode | mode
    · simp [hmode] at hrow
    · rw [hmode] at hrow
      obtain ⟨input, hinput, rfl⟩ := List.mem_map.mp hrow
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hinput
      have hzero := (run.complete.preallocated component (List.of_mem_zip hentry).1 rowPlan mode
        (run.planned _ hentry) hmode run.publicInput run.proverInput run.assumptions
        run.stableData run.stableData_stable).2.1
      simp only [answeredBy, hmode]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨handler, hhandler, rfl⟩ := List.mem_map.mp hx
      split
      · split
        · simp only [row]
          rw [show (fixedPrefix component (UInt64.ofNat j) ++
            (mode.input.eval (UInt64.ofNat j) run.hint).toArray) =
            preallocatedInput component mode run.hint j from rfl,
            hzero handler hhandler j (List.mem_range.mp hj)]
          simp
        · rfl
      · rfl

/-! ### Padding -/

/-- The padding row of a component state. -/
def paddingRow (state : ComponentState (F p)) : GeneratedRow (F p) :=
  run.row state.component state.rowPlan.padding.input none

/-- The number of padding rows a state gets. -/
def padCount (state : ComponentState (F p)) : ℕ :=
  state.rowPlan.padding.targetHeight state.rows.length - state.rows.length

/-- A state padded to its target height. -/
def padOne (state : ComponentState (F p)) : ComponentState (F p) :=
  { state with rows := (state.rows ++ List.replicate (padCount state) (run.paddingRow state)) }

lemma padState_eq {view : List (ComponentState (F p))} (hview : run.ViewOk view)
    {state : ComponentState (F p)} (hok : run.StateOk state) :
    padState run.data0 run.hint view state [] = (run.padOne state,
      (List.replicate (padCount state) (run.paddingRow state)).flatMap
        (rowInteractions state · run.data0), []) := by
  have hsize : state.rowPlan.padding.input.size = state.component.rowOffset :=
    (run.planValid.row_plans _ hok.entry).padding_width
  unfold padState
  dsimp only
  split
  · rename_i hzero
    simp only [padOne, padCount] at hzero ⊢
    simp [hzero]
  · rename_i hcount
    rw [run.completeRow_eq hview hok hsize]
    rfl

lemma padStates_eq {view : List (ComponentState (F p))} (hview : run.ViewOk view) :
    ∀ states : List (ComponentState (F p)), (∀ state ∈ states, run.StateOk state) →
    padStates run.data0 run.hint view states [] = (states.map run.padOne,
      states.flatMap (fun state => (List.replicate (padCount state)
        (run.paddingRow state)).flatMap (rowInteractions state · run.data0)), [])
  | [], _ => rfl
  | state :: states, hok => by
      simp only [padStates, run.padState_eq hview (hok state (List.mem_cons_self ..)),
        padStates_eq hview states fun state hstate => hok state (List.mem_cons_of_mem _ hstate),
        List.map_cons, List.flatMap_cons]

lemma padTables_eq {states : List (ComponentState (F p))} (hview : run.ViewOk states)
    (hok : ∀ state ∈ states, run.StateOk state) :
    padTables run.data0 run.hint states = (states.map run.padOne,
      ⟨[], states.flatMap (fun state => (List.replicate (padCount state)
        (run.paddingRow state)).flatMap (rowInteractions state · run.data0))⟩) := by
  simp only [padTables, run.padStates_eq hview states hok]
  simp [define, Change.append]

lemma tablesArePadded_padOne (states : List (ComponentState (F p))) :
    tablesArePadded (states.map run.padOne) = true := by
  simp only [tablesArePadded, List.all_map, List.all_eq_true, Function.comp_apply, beq_iff_eq]
  intro state _
  simp only [padOne, padCount, List.length_append, List.length_replicate]
  have := (le_targetHeight state.rowPlan.padding state.rows.length).1
  rw [Nat.add_sub_cancel' this, targetHeight_targetHeight]

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
  obtain ⟨main, pad, hrowsEq, -, -, hmain, -⟩ := hrows
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

/-- The VM and preallocated components stay within their row bounds. -/
lemma rows_le_bound_direct (hinv : run.Inv k padded balancing) {state : ComponentState (F p)}
    (hstate : state ∈ balancing.states)
    (hdirect : state.component = run.complete.vm.component ∨
      ∃ mode, state.rowPlan.mode = .preallocated mode) :
    state.rows.length ≤ run.bound state.component.circuit.name := by
  have hok := run.stateOk_of_shape hinv.shape hstate
  obtain ⟨hpower, hminimum, -, hmode⟩ := run.bounds.row_plan state.component hok.mem state.rowPlan
    (run.planned _ hok.entry)
  have hrows := hinv.rows state hstate
  unfold RowsOk at hrows
  split at hrows
  · rename_i mode hmodeEq
    simp only [hmodeEq] at hmode
    rw [hrows.1]
    split
    · exact targetHeight_le _ hpower hmode hminimum
    · exact hmode
  · rename_i mode hmodeEq
    obtain ⟨main, pad, hrowsEq, hpad, htarget, hvm, -⟩ := hrows
    rcases hdirect with hcomponent | ⟨mode', hmode'⟩
    · rw [hrowsEq, List.length_append, List.length_replicate]
      apply padded_le hpower hminimum _ hpad htarget
      rw [hvm hcomponent, List.length_map, List.length_range, hcomponent]
      exact le_trans hinv.steps_le run.bounds.steps_le
    · rw [hmodeEq] at hmode'
      cases hmode'

/-- Every component stays within its row bound: demand-driven components answer pulls of
components of lower rank. -/
lemma rows_le_bound (hinv : run.Inv k padded balancing) :
    ∀ state ∈ balancing.states, state.rows.length ≤ run.bound state.component.circuit.name := by
  suffices h : ∀ rank, ∀ state ∈ balancing.states,
      run.complete.rank state.component.circuit.name = rank →
        state.rows.length ≤ run.bound state.component.circuit.name from
    fun state hstate => h _ state hstate rfl
  intro rank
  induction rank using Nat.strong_induction_on with
  | _ rank ih =>
  intro state hstate hrank
  have hok := run.stateOk_of_shape hinv.shape hstate
  by_cases hdirect : state.component = run.complete.vm.component ∨
      ∃ mode, state.rowPlan.mode = .preallocated mode
  · exact hinv.rows_le_bound_direct hstate hdirect
  push Not at hdirect
  obtain ⟨hcomponent, hnotPreallocated⟩ := hdirect
  obtain ⟨hpower, hminimum, -, hmode⟩ := run.bounds.row_plan state.component hok.mem state.rowPlan
    (run.planned _ hok.entry)
  have hrows := hinv.rows state hstate
  unfold RowsOk at hrows
  split at hrows
  · rename_i mode hmodeEq
    exact absurd hmodeEq (hnotPreallocated mode)
  rename_i mode hmodeEq
  simp only [hmodeEq] at hmode
  rcases hmode with hmode | hmode
  · exact absurd hmode hcomponent
  obtain ⟨main, pad, hrowsEq, hpad, htarget, -, hanswer⟩ := hrows
  rw [hrowsEq, List.length_append, List.length_replicate]
  apply padded_le hpower hminimum _ hpad htarget
  refine le_trans ?_ hmode
  have hanswers := run.answersPull_demand hok hcomponent hmodeEq
  have hchannel : mode.channel.name ≠ run.complete.vm.channel.name := fun h =>
    run.not_answersPull_vmChannel hok ((hanswers _).mpr h.symm)
  have hmain := run.card_answeredBy_ge hmodeEq hrowsEq fun row hrow => by
    obtain ⟨message, count, hcount, -, -, -, h⟩ := hanswer hcomponent row hrow
    exact ⟨message, count, hcount, h⟩
  have hstateLe : (state.rows.map fun row => run.answeredBy state row mode.channel.name).sum ≤
      run.answeredMsgs balancing.states mode.channel.name :=
    List.le_sum_of_mem (List.mem_map_of_mem (f := fun state => (state.rows.map fun row =>
      run.answeredBy state row mode.channel.name).sum) hstate)
  have hpulled := run.card_pulledMsgs_le (fun state hstate => run.stateOk_of_shape hinv.shape hstate)
    (states := balancing.states) mode.channel.name
  refine le_trans hmain (le_trans (Multiset.card_le_card hstateLe) (le_trans
    (Multiset.card_le_card (hinv.answered_le _ hchannel)) (le_trans hpulled ?_)))
  apply Nat.add_le_add_left
  rw [← run.components_eq hinv.shape, List.map_map]
  apply List.sum_le_sum
  intro other hother
  have hokOther := run.stateOk_of_shape hinv.shape hother
  simp only [Function.comp_apply]
  split
  · exact Nat.zero_le _
  rename_i hnot
  by_cases hpulls : pullsOn other.component mode.channel.name = 0
  · simp [hpulls]
  apply Nat.mul_le_mul_right
  by_cases hdirect : other.component = run.complete.vm.component ∨
      ∃ mode, other.rowPlan.mode = .preallocated mode
  · exact hinv.rows_le_bound_direct hother hdirect
  push Not at hdirect
  obtain ⟨hotherVm, hotherNotPreallocated⟩ := hdirect
  rcases hotherMode : other.rowPlan.mode with otherMode | otherMode
  · have hlt := run.complete.acyclic state.component hok.mem state.rowPlan mode
      (run.planned _ hok.entry) hmodeEq hcomponent other.component hokOther.mem other.rowPlan
      otherMode (run.planned _ hokOther.entry) hotherMode hotherVm (Nat.pos_of_ne_zero hpulls)
    exact ih _ (hrank ▸ hlt) other hother rfl
  · exact absurd hotherMode (hotherNotPreallocated otherMode)

lemma viewOk (hinv : run.Inv k padded balancing) : run.ViewOk balancing.states := by
  refine ⟨hinv.shape, fun state hstate mode hmode hheight => ?_⟩
  have hok := run.stateOk_of_shape hinv.shape hstate
  have hrows := hinv.rows state hstate
  simp only [RowsOk, hmode] at hrows
  obtain ⟨hlength, hrowsEq⟩ := hrows
  have hlength' : state.rows.length = mode.rows.toNat := by
    rw [hlength]; split <;> simp [hheight]
  refine ⟨hlength', fun j hj => ?_⟩
  obtain ⟨input, hreachable, heq⟩ := hrowsEq j hj
  have hbase := run.admissible_baseInput hok hmode j
  have hj' : j < mode.rows.toNat := hlength' ▸ hj
  rw [heq]
  refine ⟨rfl, hreachable.size_eq.trans hbase.size, fun column hcolumn => ?_⟩
  show input[column]? = _
  rw [hreachable.getElem?_eq hcolumn]
  simp [baseInput, hj']

/-- All interactions are fewer than half the field order. -/
lemma length_lt (hinv : run.Inv k padded balancing) :
    2 * (run.verifier ++ statesInteractions balancing.states run.data0).length < p := by
  have hbound := run.bounds.interactions
  refine lt_of_le_of_lt ?_ hbound
  apply Nat.mul_le_mul_left
  rw [List.length_append, length_statesInteractions]
  apply Nat.add_le_add (by simp [verifier, Operations.interactionValues])
  rw [← run.components_eq hinv.shape, List.map_map]
  apply List.sum_le_sum
  intro state hstate
  have hok := run.stateOk_of_shape hinv.shape hstate
  simp only [Function.comp_apply, hok.interactions]
  exact Nat.mul_le_mul_right _ (hinv.rows_le_bound state hstate)

/-- A pending demand is the VM's next state, the final state, or a deficit of pulls off the VM
channel. -/
lemma demand_cases (hinv : run.Inv k padded balancing) {demand : Demand (F p)}
    (hmem : demand ∈ balancing.demands) :
    (demand.channel = run.complete.vm.channel.name ∧ k < run.steps ∧ padded = false ∧
      ((demand.message = run.complete.vm.state run.publicInput k ∧ demand.multiplicity = 1) ∨
        (demand.message = run.complete.vm.final run.publicInput ∧ demand.multiplicity = -1))) ∨
    (demand.channel ≠ run.complete.vm.channel.name ∧ ∃ δ, 0 < δ ∧ 2 * δ < p ∧
      demand.multiplicity = -(δ : F p) ∧
      (run.answeredMsgs balancing.states demand.channel).count demand.message + δ =
        (run.pulledMsgs balancing.states demand.channel).count demand.message) := by
  have hnet := hinv.canonical.netOf_eq hmem
  have hne := hinv.canonical.2 demand hmem
  rw [hinv.tracks] at hnet
  by_cases hchannel : demand.channel = run.complete.vm.channel.name
  · left
    rw [hchannel, hinv.net_vm] at hnet
    have hk : k < run.steps := by
      by_contra hk
      have hsteps : k = run.steps := le_antisymm hinv.steps_le (by omega)
      rw [hsteps, run.reaches] at hnet
      exact hne (by rw [← hnet]; simp)
    refine ⟨hchannel, hk, ?_, ?_⟩
    · cases padded
      · rfl
      · exact absurd (hinv.padded_steps rfl) (by omega)
    · have hdistinct := run.distinct k hk
      by_cases hstate : demand.message = run.complete.vm.state run.publicInput k
      · refine .inl ⟨hstate, ?_⟩
        rw [← hnet]
        simp [hstate, hdistinct]
      · by_cases hfinal : demand.message = run.complete.vm.final run.publicInput
        · refine .inr ⟨hfinal, ?_⟩
          rw [← hnet]
          simp [hfinal, Ne.symm hdistinct]
        · exact absurd (by rw [← hnet]; simp [hstate, hfinal]) hne
  · right
    rw [run.net_eq_answered_sub_pulled hinv.statesOk hchannel] at hnet
    have hle := Multiset.le_iff_count.mp (hinv.answered_le _ hchannel) demand.message
    set answered := (run.answeredMsgs balancing.states demand.channel).count demand.message
    set pulled := (run.pulledMsgs balancing.states demand.channel).count demand.message
    refine ⟨hchannel, pulled - answered, ?_, ?_, ?_, by omega⟩
    · by_contra hzero
      apply hne
      rw [← hnet, show pulled = answered by omega]
      simp
    · have hcount := Multiset.count_le_card demand.message
        (run.pulledMsgs balancing.states demand.channel)
      have hcard := run.card_pulledMsgs_le_length balancing.states demand.channel
      have hlength := hinv.length_lt
      omega
    · rw [← hnet, Nat.cast_sub hle]
      ring

/-- While demand is pending, some component handles a pending demand. -/
lemma exists_handled (hinv : run.Inv k padded balancing) (hne : balancing.demands ≠ []) :
    ∃ demand ∈ balancing.demands, ∃ state ∈ balancing.states, state.handles demand = true := by
  obtain ⟨demand, hmem⟩ := List.exists_mem_of_ne_nil _ hne
  rcases hinv.demand_cases hmem with ⟨-, hk, -, -⟩ | ⟨hchannel, δ, hpos, hlt, hmult, hcount⟩
  · have hdistinct := run.distinct k hk
    have hnet : netOf balancing.demands run.complete.vm.channel.name
        (run.complete.vm.state run.publicInput k) = 1 := by
      rw [hinv.tracks, hinv.net_vm]
      simp [hdistinct]
    obtain ⟨demand', hmem', hkey⟩ := List.mem_map.mp ((hinv.canonical.mem_iff _ _).mpr
      (by rw [hnet]; exact one_ne_zero))
    simp only [Demand.key, Prod.mk.injEq] at hkey
    have hmult : demand'.multiplicity = 1 := by
      rw [← hinv.canonical.netOf_eq hmem', hkey.1, hkey.2, hnet]
    obtain ⟨vmState, hvmState, hvm⟩ := run.exists_vm_state hinv.shape
    have hok := run.stateOk_of_shape hinv.shape hvmState
    refine ⟨demand', hmem', vmState, hvmState, (run.handles_iff hok demand').mpr ?_⟩
    rw [StateOk.vm_rowPlan run hok hvm, (demand_push hmult).1, hkey.1]
    simp [Mode.handled, run.complete.vm.mode_channel, run.complete.vm.mode_direction]
  · have hpulled : demand.message ∈ run.pulledMsgs balancing.states demand.channel :=
      Multiset.count_pos.mp (by omega)
    obtain ⟨hanswers, -⟩ := run.pulled_facts hinv.statesOk hchannel hpulled
    obtain ⟨entry, hentry, hhandled, -⟩ := run.answers_entry hanswers
    obtain ⟨state, hstate, -, hcomponent, hrowPlan⟩ := run.find?_state hinv.shape hentry
    have hok := run.stateOk_of_shape hinv.shape hstate
    refine ⟨demand, hmem, state, hstate, (run.handles_iff hok demand).mpr ?_⟩
    rw [hcomponent, hrowPlan, (demand_pull hmult hpos hlt).1]
    exact hhandled

lemma interactions_lt (hinv : run.Inv k padded balancing) : balancing.interactions < p := by
  have := hinv.length_lt
  rw [hinv.interactions]
  omega

/-- The VM answers the pushed state `k` with its row. -/
lemma step_vm (hinv : run.Inv k padded balancing) {demand : Demand (F p)} {index : ℕ}
    {state : ComponentState (F p)} (hstate : balancing.states[index]? = some state)
    (hvm : state.component = run.complete.vm.component) (hk : k < run.steps)
    (hpadded : padded = false)
    (hmessage : demand.message = run.complete.vm.state run.publicInput k)
    (hmult : demand.multiplicity = 1) :
    ∃ states change, handle balancing.states demand index run.data0 run.hint = .ok (states, change) ∧
      run.Inv (k + 1) padded (balancing.apply states change) ∧
      Prod.Lex (· < ·) (· < ·) (balancing.apply states change).measure balancing.measure := by
  have hmemState := List.mem_of_getElem? hstate
  have hok := run.stateOk_of_shape hinv.shape hmemState
  have hplan := StateOk.vm_rowPlan run hok hvm
  have hmode : state.rowPlan.mode = .demand run.complete.vm.mode := by rw [hplan]
  have hrow : createDemandRow balancing.states state run.complete.vm.mode demand 1 run.data0
      run.hint = (run.vmRow k, []) := by
    unfold createDemandRow
    rw [run.completeRow_eq hinv.viewOk hok (run.demand_input_size hok.entry hmode _ _)]
    simp [vmRow, hvm, hmessage, demandOrigin, Vm.input]
  have hmutation : handleDemand balancing.states state run.complete.vm.mode demand run.data0
      run.hint = Mutation.mk { state with rows := state.rows ++ [run.vmRow k] } []
        [run.vmRow k] [] := by
    simp [handleDemand, run.complete.vm.mode_aggregation, hrow, (demand_push hmult).2]
  have hhandle := run.handle_demand hstate hmode demand (by rw [hmutation])
  rw [hmutation] at hhandle
  simp only [List.flatMap_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hhandle
  refine ⟨_, _, hhandle, ?_, ?_⟩
  · have hchanges := handle_spec _ _ _ _ _ hhandle
    have hrowsOld := hinv.rows state hmemState
    simp only [RowsOk, hmode] at hrowsOld
    obtain ⟨main, pad, hrowsEq, hpad, -, hmain, -⟩ := hrowsOld
    rw [hmain hvm, hpad hpadded, List.replicate_zero, List.append_nil] at hrowsEq
    have hfacts := run.rowFacts_vmRow hok hvm hk
    refine ⟨hchanges.1.trans hinv.shape, ?_, hk, fun h => absurd h (by simp [hpadded]),
      Balancing.tracks_apply hinv.tracks hchanges.2,
      (hinv.canonical.removeInteractions _).addInteractions _, ?_, ?_,
      fun h => absurd h (by simp [hpadded])⟩
    · intro x hx
      rcases mem_set_cases hx with rfl | ⟨j, hj, hji, rfl⟩
      · simp only [RowsOk, hmode]
        refine ⟨(List.range (k + 1)).map run.vmRow, 0, ?_, fun _ => rfl,
          fun h => absurd h (by simp [hpadded]), fun _ => rfl, fun h => absurd hvm h⟩
        simp [hrowsEq, List.range_succ]
      · have hne := run.component_ne_of_set hinv.shape hstate hj hji
        exact run.rowsOk_of_ne_vm (hvm ▸ hne) (hinv.rows _ (List.getElem_mem hj))
    · have hlength := length_statesInteractions_set hstate (state.rows ++ [run.vmRow k]) run.data0
      simp only [List.length_append, List.length_singleton, Nat.add_mul, one_mul] at hlength
      simp only [Balancing.apply, List.length_nil, Nat.sub_zero, List.length_append,
        hinv.interactions, rowInteractions, List.length_map]
      linarith
    · intro channel hchannel
      have hanswered := run.answeredMsgs_set hstate (state.rows ++ [run.vmRow k]) channel
      have hpulled := run.pulledMsgs_set hstate (state.rows ++ [run.vmRow k]) channel
      rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        hfacts.answered_zero channel hchannel (run.not_answersPull_vm hok hvm channel),
        add_zero, add_left_inj] at hanswered
      rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at hpulled
      simp only [Balancing.apply]
      rw [hanswered]
      have hold := hinv.answered_le channel hchannel
      have : run.pulledMsgs balancing.states channel ≤
          run.pulledMsgs (balancing.states.set index { state with rows := state.rows ++
            [run.vmRow k] }) channel := by
        have := le_self_add (a := run.pulledMsgs balancing.states channel +
          (state.rows.map fun row => run.pulledBy state row channel).sum)
          (b := run.pulledBy state (run.vmRow k) channel)
        rw [add_assoc, ← hpulled] at this
        exact le_of_add_le_add_right this
      exact hold.trans this
  · apply measure_lt_left hinv.interactions_lt
    simp only [Balancing.apply, List.length_nil, Nat.sub_zero]
    have hnext := run.next_ne hk
    have hname : state.component.circuit.name = run.complete.vm.component.circuit.name := by
      rw [hvm]
    have hne : netOfInteractions (rowInteractions state (run.vmRow k) run.data0)
        run.complete.vm.channel.name (run.complete.vm.state run.publicInput k) ≠ 0 := by
      rw [(run.rowFacts_vmRow hok hvm hk).vm_net]
      simp [vmNet, hname, vmRow, row, demandOrigin, Ne.symm hnext]
    obtain ⟨interaction, hmem, -⟩ := exists_of_netOfInteractions_ne_zero hne
    have := List.length_pos_of_mem hmem
    omega

/-- A deficit handled by a demand-driven component: the component is not the VM, the deficit is on
its channel, generation is not padded, and the message can be answered. -/
lemma demand_setup (hinv : run.Inv k padded balancing) {demand : Demand (F p)}
    {state : ComponentState (F p)} (hstate : state ∈ balancing.states)
    (hhandles : state.handles demand = true) {mode : DemandMode (F p)}
    (hmode : state.rowPlan.mode = .demand mode)
    (hchannel : demand.channel ≠ run.complete.vm.channel.name) {δ : ℕ} (hpos : 0 < δ)
    (hlt : 2 * δ < p) (hmult : demand.multiplicity = -(δ : F p))
    (hcount : (run.answeredMsgs balancing.states demand.channel).count demand.message + δ =
      (run.pulledMsgs balancing.states demand.channel).count demand.message) :
    state.component ≠ run.complete.vm.component ∧ demand.channel = mode.channel.name ∧
      padded = false ∧ run.Pullable mode.channel demand.message ∧
      demand.message.size = mode.channel.arity := by
  have hok := run.stateOk_of_shape hinv.shape hstate
  have hdirection := (demand_pull hmult hpos hlt).1
  have hhandled := (run.handles_iff hok demand).mp hhandles
  rw [hdirection] at hhandled
  have hvm : state.component ≠ run.complete.vm.component := fun hvm =>
    run.not_answersPull_vm hok hvm _ hhandled
  have hmodeChannel : demand.channel = mode.channel.name := by
    simp only [hmode, Mode.handled, List.mem_singleton, Prod.mk.injEq] at hhandled
    exact hhandled.1
  have hdeclared := (run.complete.demand state.component hok.mem state.rowPlan mode
    (run.planned _ hok.entry) hmode hvm).1
  have hpulled : demand.message ∈ run.pulledMsgs balancing.states demand.channel :=
    Multiset.count_pos.mp (by omega)
  obtain ⟨hpullable, hsize⟩ := (run.pulled_facts hinv.statesOk hchannel hpulled).2 mode.channel
    hdeclared hmodeChannel.symm
  refine ⟨hvm, hmodeChannel, ?_, hpullable, hsize⟩
  cases padded
  · rfl
  · exfalso
    have hequal := hinv.padded_answered rfl _ hchannel fun other hother hanswers => by
      have hokOther := run.stateOk_of_shape hinv.shape hother
      have := run.handled_unique hokOther.entry hok.entry hanswers hhandled
      simp only [Prod.mk.injEq] at this
      exact ⟨mode, by rw [this.2, hmode]⟩
    rw [hequal] at hcount
    omega

omit [Fact p.Prime] in
lemma sum_map_replicate {α : Type*} {M : Type*} [AddCommMonoid M] (f : α → M) (n : ℕ) (a : α) :
    ((List.replicate n a).map f).sum = n • f a := by
  simp [List.map_replicate, List.sum_replicate]

/-- Appending rows answering `n` times `count` occurrences of a deficit of `n * count` restores
the invariant and adds interactions. -/
lemma step_append (hinv : run.Inv k padded balancing) {index : ℕ} {state : ComponentState (F p)}
    (hstate : balancing.states[index]? = some state) {mode : DemandMode (F p)}
    (hmode : state.rowPlan.mode = .demand mode) (hvm : state.component ≠ run.complete.vm.component)
    (hpadded : padded = false) {message : Array (F p)} {n count : ℕ} (hn : 0 < n)
    (hcountPos : 0 < count) (hsize : message.size = mode.channel.arity)
    (hpullable : run.Pullable mode.channel message)
    (hperOccurrence : mode.aggregation = .perOccurrence → count = 1)
    (hchannel : mode.channel.name ≠ run.complete.vm.channel.name)
    (hdeficit : (run.answeredMsgs balancing.states mode.channel.name).count message + n * count ≤
      (run.pulledMsgs balancing.states mode.channel.name).count message) :
    let row := run.answerRow state.component mode message count
    let states := balancing.states.set index { state with rows := state.rows ++ List.replicate n row }
    let change : Change (F p) := ⟨[], (List.replicate n row).flatMap (rowInteractions state · run.data0)⟩
    Changes run.data0 balancing.states states change →
    run.Inv k padded (balancing.apply states change) ∧
      Prod.Lex (· < ·) (· < ·) (balancing.apply states change).measure balancing.measure := by
  intro row states change hchanges
  have hmemState := List.mem_of_getElem? hstate
  have hok := run.stateOk_of_shape hinv.shape hmemState
  have hfacts := run.rowFacts_answerRow hok hvm hmode hcountPos hsize hpullable
  have hanswers := run.answersPull_demand hok hvm hmode
  have hlength := length_statesInteractions_set hstate (state.rows ++ List.replicate n row) run.data0
  simp only [List.length_append, List.length_replicate, Nat.add_mul] at hlength
  have hrowLength : (rowInteractions state row run.data0).length = state.interactions.length := by
    simp [rowInteractions]
  refine ⟨⟨hchanges.1.trans hinv.shape, ?_, hinv.steps_le, hinv.padded_steps,
    Balancing.tracks_apply hinv.tracks hchanges.2,
    (hinv.canonical.removeInteractions _).addInteractions _, ?_, ?_,
    fun h => absurd h (by simp [hpadded])⟩, ?_⟩
  · intro x hx
    rcases mem_set_cases hx with rfl | ⟨j, hj, hji, rfl⟩
    · have hrowsOld := hinv.rows state hmemState
      simp only [RowsOk, hmode] at hrowsOld ⊢
      obtain ⟨main, pad, hrowsEq, hpad, -, -, hanswer⟩ := hrowsOld
      rw [hpad hpadded, List.replicate_zero, List.append_nil] at hrowsEq
      refine ⟨main ++ List.replicate n row, 0, by simp [hrowsEq], fun _ => rfl,
        fun h => absurd h (by simp [hpadded]), fun h => absurd h hvm, fun _ x hx => ?_⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact hanswer hvm x hx
      · rw [List.eq_of_mem_replicate hx]
        exact ⟨message, count, hcountPos, hsize, hpullable, hperOccurrence, rfl⟩
    · exact hinv.rows _ (List.getElem_mem hj)
  · simp only [Balancing.apply, change, states, List.length_nil, Nat.sub_zero, List.length_append,
      hinv.interactions, List.length_flatMap, List.map_replicate, List.sum_replicate, hrowLength,
      smul_eq_mul]
    linarith
  · intro channel hchannel'
    have hanswered := run.answeredMsgs_set hstate (state.rows ++ List.replicate n row) channel
    have hpulled := run.pulledMsgs_set hstate (state.rows ++ List.replicate n row) channel
    simp only [List.map_append, List.sum_append, sum_map_replicate] at hanswered hpulled
    simp only [Balancing.apply, states]
    have hold := hinv.answered_le channel hchannel'
    by_cases hmodeChannel : channel = mode.channel.name
    · subst hmodeChannel
      have hzero : run.pulledBy state row mode.channel.name = 0 := by
        simp [pulledBy, (hanswers _).mpr rfl]
      rw [hzero, smul_zero, add_zero, add_left_inj] at hpulled
      have hrowAnswered : run.answeredBy state row mode.channel.name =
          Multiset.replicate count message := by
        simp [answeredBy, hmode, row, answerRow, Run.row, demandOrigin]
      rw [hrowAnswered] at hanswered
      have hAnswered : run.answeredMsgs (balancing.states.set index
          { state with rows := state.rows ++ List.replicate n row }) mode.channel.name =
          run.answeredMsgs balancing.states mode.channel.name +
            n • Multiset.replicate count message := by
        apply add_right_cancel (b := (state.rows.map fun row =>
          run.answeredBy state row mode.channel.name).sum)
        rw [hanswered]
        abel
      rw [hAnswered, hpulled, Multiset.le_iff_count]
      intro message'
      rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_replicate]
      split_ifs with hmessage
      · subst hmessage
        simpa using hdeficit
      · simpa using Multiset.le_iff_count.mp hold message'
    · have hzero : run.answeredBy state row channel = 0 :=
        hfacts.answered_zero channel hchannel' fun h => hmodeChannel ((hanswers _).mp h)
      rw [hzero, smul_zero, add_zero, add_left_inj] at hanswered
      rw [hanswered]
      refine hold.trans ?_
      have := le_self_add (a := run.pulledMsgs balancing.states channel +
        (state.rows.map fun row => run.pulledBy state row channel).sum)
        (b := n • run.pulledBy state row channel)
      rw [add_assoc, ← hpulled] at this
      exact le_of_add_le_add_right this
  · apply measure_lt_left hinv.interactions_lt
    simp only [Balancing.apply, change, List.length_nil, Nat.sub_zero, List.length_flatMap,
      List.map_replicate, List.sum_replicate, hrowLength, smul_eq_mul]
    have hne : netOfInteractions (rowInteractions state row run.data0) mode.channel.name message ≠ 0 := by
      rw [hfacts.answered_net _ hchannel ((hanswers _).mpr rfl)]
      simp only [answeredBy, hmode, answerRow, Run.row, demandOrigin, if_true,
        Multiset.count_replicate_self]
      exact_mod_cast (show (count : F p) ≠ 0 from by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have := Nat.le_of_dvd hcountPos hdvd
        have hcard := Multiset.count_le_card message (run.pulledMsgs balancing.states mode.channel.name)
        have hbound := run.card_pulledMsgs_le_length balancing.states mode.channel.name
        have hlen := hinv.length_lt
        nlinarith)
    obtain ⟨interaction, hmem, -⟩ := exists_of_netOfInteractions_ne_zero hne
    have := List.length_pos_of_mem hmem
    rw [hrowLength] at this
    have : 0 < n * state.interactions.length := Nat.mul_pos hn this
    omega

lemma createDemandRow_eq (hinv : run.Inv k padded balancing) {state : ComponentState (F p)}
    (hstate : state ∈ balancing.states) {mode : DemandMode (F p)}
    (hmode : state.rowPlan.mode = .demand mode) (demand : Demand (F p)) (count : ℕ) :
    createDemandRow balancing.states state mode demand count run.data0 run.hint =
      (run.answerRow state.component mode demand.message count, []) := by
  have hok := run.stateOk_of_shape hinv.shape hstate
  unfold createDemandRow
  rw [run.completeRow_eq hinv.viewOk hok (run.demand_input_size hok.entry hmode _ _)]
  rfl

/-- A demand-driven component answers a deficit with one row per occurrence, or with one row for
a message it has not answered yet. -/
lemma step_new (hinv : run.Inv k padded balancing) {demand : Demand (F p)} {index : ℕ}
    {state : ComponentState (F p)} (hstate : balancing.states[index]? = some state)
    (hhandles : state.handles demand = true) {mode : DemandMode (F p)}
    (hmode : state.rowPlan.mode = .demand mode)
    (hnew : mode.aggregation = .perOccurrence ∨ (mode.aggregation = .byMessage ∧
      state.rows.zipIdx.findSome? (fun (row, index) => row.origin.bind fun origin =>
        if sameOrigin origin mode demand then some (row, origin, index) else none) = none))
    (hchannel : demand.channel ≠ run.complete.vm.channel.name) {δ : ℕ} (hpos : 0 < δ)
    (hlt : 2 * δ < p) (hmult : demand.multiplicity = -(δ : F p))
    (hcount : (run.answeredMsgs balancing.states demand.channel).count demand.message + δ =
      (run.pulledMsgs balancing.states demand.channel).count demand.message) :
    ∃ states change, handle balancing.states demand index run.data0 run.hint = .ok (states, change) ∧
      run.Inv k padded (balancing.apply states change) ∧
      Prod.Lex (· < ·) (· < ·) (balancing.apply states change).measure balancing.measure := by
  have hmemState := List.mem_of_getElem? hstate
  obtain ⟨hvm, hmodeChannel, hpadded, hpullable, hsize⟩ :=
    hinv.demand_setup hmemState hhandles hmode hchannel hpos hlt hmult hcount
  have hdemandCount := (demand_pull hmult hpos hlt).2
  rw [hmodeChannel] at hcount hchannel
  rcases hnew with hperOccurrence | ⟨hbyMessage, hnone⟩
  · have hmutation : handleDemand balancing.states state mode demand run.data0 run.hint =
        Mutation.mk { state with rows := (state.rows ++
          List.replicate δ (run.answerRow state.component mode demand.message 1)) } []
          (List.replicate δ (run.answerRow state.component mode demand.message 1)) [] := by
      simp [handleDemand, hperOccurrence, hinv.createDemandRow_eq hmemState hmode, hdemandCount]
    have hhandle := run.handle_demand hstate hmode demand (by rw [hmutation])
    rw [hmutation] at hhandle
    refine ⟨_, _, hhandle, hinv.step_append hstate hmode hvm hpadded hpos one_pos hsize hpullable
      (fun _ => rfl) hchannel (by omega) (handle_spec _ _ _ _ _ hhandle)⟩
  · have hmutation : handleDemand balancing.states state mode demand run.data0 run.hint =
        Mutation.mk { state with rows := (state.rows ++
          List.replicate 1 (run.answerRow state.component mode demand.message δ)) } []
          (List.replicate 1 (run.answerRow state.component mode demand.message δ)) [] := by
      simp [handleDemand, hbyMessage, hnone, hinv.createDemandRow_eq hmemState hmode,
        hdemandCount]
    have hhandle := run.handle_demand hstate hmode demand (by rw [hmutation])
    rw [hmutation] at hhandle
    refine ⟨_, _, hhandle, hinv.step_append hstate hmode hvm hpadded one_pos hpos hsize hpullable
      (fun h => absurd (hbyMessage ▸ h) (by simp)) hchannel (by omega)
      (handle_spec _ _ _ _ _ hhandle)⟩

/-- An update changing the net of one channel message from `-δ` to zero shortens the canonical
demand list. -/
lemma length_apply_of_update {balancing : Balancing (F p)} {states : List (ComponentState (F p))}
    {change : Change (F p)} (hcanonical : Demand.Canonical balancing.demands) {channel : String}
    {message : Array (F p)} {δ : F p} (hδ : δ ≠ 0)
    (hnet : netOf balancing.demands channel message = -δ)
    (hchange : ∀ channel' message', netOfInteractions change.added channel' message' -
        netOfInteractions change.removed channel' message' =
      if channel' = channel ∧ message' = message then δ else 0) :
    (balancing.apply states change).demands.length + 1 = balancing.demands.length := by
  have hcanonical' : Demand.Canonical (balancing.apply states change).demands :=
    (hcanonical.removeInteractions _).addInteractions _
  have hnetApply : ∀ channel' message', netOf (balancing.apply states change).demands channel'
      message' = netOf balancing.demands channel' message' +
        if channel' = channel ∧ message' = message then δ else 0 := by
    intro channel' message'
    rw [← hchange]
    simp only [Balancing.apply, netOf_addInteractions, netOf_removeInteractions]
    abel
  apply hcanonical.length_succ hcanonical' (channel := channel) (message := message)
    (by rw [hnet]; exact neg_ne_zero.mpr hδ)
  intro channel' message'
  rw [hnetApply]
  by_cases hkey : channel' = channel ∧ message' = message
  · obtain ⟨rfl, rfl⟩ := hkey
    simp [hnet]
  · rw [if_neg hkey, add_zero]
    constructor
    · intro h
      exact ⟨h, fun heq => hkey (by simpa using heq)⟩
    · exact fun h => h.1

/-- Rows whose side nets agree on a channel their component does not answer pull the same
messages on it. -/
lemma pulledBy_eq (hinv : run.Inv k padded balancing) {state : ComponentState (F p)}
    (hstate : state ∈ balancing.states) (hrows : state.rows ≠ []) {row row' : GeneratedRow (F p)}
    (hfacts : run.RowFacts state row) (hfacts' : run.RowFacts state row') {channel : String}
    (hchannel : channel ≠ run.complete.vm.channel.name) (hnot : ¬AnswersPull state channel)
    (hnet : ∀ message, netOfInteractions (rowInteractions state row run.data0) channel message =
      netOfInteractions (rowInteractions state row' run.data0) channel message) :
    run.pulledBy state row channel = run.pulledBy state row' channel := by
  have hlengthState : state.interactions.length ≤
      (run.verifier ++ statesInteractions balancing.states run.data0).length := by
    rw [List.length_append, length_statesInteractions]
    have : state.rows.length * state.interactions.length ≤
        (balancing.states.map fun state => state.rows.length * state.interactions.length).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun state : ComponentState (F p) =>
        state.rows.length * state.interactions.length) hstate)
    have hpos : 0 < state.rows.length := List.length_pos_of_ne_nil hrows
    nlinarith
  have hbound := hinv.length_lt
  ext message
  simp only [pulledBy, hnot, if_false]
  have h1 := run.rowFacts_net hfacts hchannel message
  have h2 := run.rowFacts_net hfacts' hchannel message
  rw [hnet message, h2, hfacts.answered_zero _ hchannel hnot,
    hfacts'.answered_zero _ hchannel hnot] at h1
  simp only [pulledBy, hnot, if_false, Multiset.count_zero, Nat.cast_zero, zero_sub,
    neg_inj] at h1
  have hle : ∀ row, (pullsOf (rowInteractions state row run.data0) channel).count message <
      p := by
    intro row
    have hcount := Multiset.count_le_card message
      (pullsOf (rowInteractions state row run.data0) channel)
    have hcard := card_pullsOf_le (rowInteractions state row run.data0) channel
    have hlen : (rowInteractions state row run.data0).length = state.interactions.length := by
      simp [rowInteractions]
    omega
  have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp h1
  rw [Nat.mod_eq_of_lt (hle _), Nat.mod_eq_of_lt (hle _)] at this
  exact this.symm

/-- A by-message component answers a deficit of a message it has a row for by raising that row's
count. -/
lemma step_update (hinv : run.Inv k padded balancing) {demand : Demand (F p)} {index : ℕ}
    {state : ComponentState (F p)} (hstate : balancing.states[index]? = some state)
    (hdemand : demand ∈ balancing.demands) (hhandles : state.handles demand = true)
    {mode : DemandMode (F p)} (hmode : state.rowPlan.mode = .demand mode)
    (hbyMessage : mode.aggregation = .byMessage) {row₀ : GeneratedRow (F p)}
    {origin : Origin (F p)} {position : ℕ}
    (hfound : state.rows.zipIdx.findSome? (fun (row, index) => row.origin.bind fun origin =>
        if sameOrigin origin mode demand then some (row, origin, index) else none) =
      some (row₀, origin, position))
    (hchannel : demand.channel ≠ run.complete.vm.channel.name) {δ : ℕ} (hpos : 0 < δ)
    (hlt : 2 * δ < p) (hmult : demand.multiplicity = -(δ : F p))
    (hcount : (run.answeredMsgs balancing.states demand.channel).count demand.message + δ =
      (run.pulledMsgs balancing.states demand.channel).count demand.message) :
    ∃ states change, handle balancing.states demand index run.data0 run.hint = .ok (states, change) ∧
      run.Inv k padded (balancing.apply states change) ∧
      Prod.Lex (· < ·) (· < ·) (balancing.apply states change).measure balancing.measure := by
  have hmemState := List.mem_of_getElem? hstate
  have hok := run.stateOk_of_shape hinv.shape hmemState
  obtain ⟨hvm, hmodeChannel, hpadded, hpullable, hsize⟩ :=
    hinv.demand_setup hmemState hhandles hmode hchannel hpos hlt hmult hcount
  have hdemandCount := (demand_pull hmult hpos hlt).2
  have hanswers := run.answersPull_demand hok hvm hmode
  -- the row found for the message
  obtain ⟨position', row', hrow', hg⟩ := getElem?_of_findSome?_zipIdx hfound
  rcases horigin : row'.origin with _ | origin'
  · simp [horigin] at hg
  simp only [horigin, Option.bind_some] at hg
  split at hg
  swap
  · simp at hg
  · rename_i hsame
    simp only [Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl, rfl⟩ := hg
    have hrowsOld := hinv.rows state hmemState
    simp only [RowsOk, hmode] at hrowsOld
    obtain ⟨main, pad, hrowsEq, hpad, -, -, hanswer⟩ := hrowsOld
    rw [hpad hpadded, List.replicate_zero, List.append_nil] at hrowsEq
    have hrowMem : row' ∈ main := hrowsEq ▸ List.mem_of_getElem? hrow'
    obtain ⟨message₀, count₀, hcount₀, hsize₀, hpullable₀, -, hrowEq⟩ := hanswer hvm row' hrowMem
    have horiginEq : origin' = demandOrigin mode message₀ count₀ := by
      rw [hrowEq] at horigin
      simpa [answerRow, Run.row] using horigin.symm
    have hmessage : message₀ = demand.message := by
      simp only [sameOrigin, horiginEq, demandOrigin, Bool.and_eq_true, beq_iff_eq] at hsame
      exact hsame.2
    subst hmessage
    have hposition : position' < state.rows.length := (List.getElem?_eq_some_iff.mp hrow').1
    set updated := run.answerRow state.component mode demand.message (count₀ + δ)
    have hmutation : handleDemand balancing.states state mode demand run.data0 run.hint =
        Mutation.mk { state with rows := state.rows.set position' updated } [row'] [updated] [] := by
      simp [handleDemand, hbyMessage, hfound, hinv.createDemandRow_eq hmemState hmode,
        hdemandCount, horiginEq, demandOrigin, updated]
    have hhandle := run.handle_demand hstate hmode demand (by rw [hmutation])
    rw [hmutation] at hhandle
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hhandle
    refine ⟨_, _, hhandle, ?_⟩
    have hchanges := handle_spec _ _ _ _ _ hhandle
    have hfacts₀ := run.rowFacts_answerRow hok hvm hmode hcount₀ hsize₀ hpullable₀
    have hfactsU := run.rowFacts_answerRow hok hvm hmode (count := count₀ + δ) (by omega) hsize
      hpullable
    rw [← hrowEq] at hfacts₀
    have hinputSize := run.demand_input_size hok.entry hmode
    have hindependent : ∀ channel ≠ mode.channel.name, ∀ message,
        netOfInteractions (rowInteractions state row' run.data0) channel message =
          netOfInteractions (rowInteractions state updated run.data0) channel message := by
      intro channel hne message
      rw [hrowEq]
      simp only [updated, answerRow]
      rw [run.rowInteractions_row hok.interactions hok.mem (hinputSize _ _) _ run.stableData_stable,
        run.rowInteractions_row hok.interactions hok.mem (hinputSize _ _) _ run.stableData_stable]
      exact (run.complete.demand state.component hok.mem state.rowPlan mode
        (run.planned _ hok.entry) hmode hvm).2.2.2.2 hbyMessage demand.message count₀ (count₀ + δ)
        _ _ (run.honestEnv_row hok.mem (hinputSize _ _) run.stableData)
        (run.honestEnv_row hok.mem (hinputSize _ _) run.stableData) rfl rfl channel hne message
    have hanswered₀ : run.answeredBy state row' mode.channel.name =
        Multiset.replicate count₀ demand.message := by
      simp [hrowEq, answeredBy, hmode, answerRow, Run.row, demandOrigin]
    have hansweredU : run.answeredBy state updated mode.channel.name =
        Multiset.replicate (count₀ + δ) demand.message := by
      simp [updated, answeredBy, hmode, answerRow, Run.row, demandOrigin]
    have hlengthRow : ∀ row, (rowInteractions state row run.data0).length =
        state.interactions.length := by simp [rowInteractions]
    have hrowsNe : state.rows ≠ [] := List.ne_nil_of_mem (List.mem_of_getElem? hrow')
    constructor
    · refine ⟨hchanges.1.trans hinv.shape, ?_, hinv.steps_le, hinv.padded_steps,
        Balancing.tracks_apply hinv.tracks hchanges.2,
        (hinv.canonical.removeInteractions _).addInteractions _, ?_, ?_,
        fun h => absurd h (by simp [hpadded])⟩
      · intro x hx
        rcases mem_set_cases hx with rfl | ⟨j, hj, hji, rfl⟩
        · simp only [RowsOk, hmode]
          refine ⟨state.rows.set position' updated, 0, by simp, fun _ => rfl,
            fun h => absurd h (by simp [hpadded]), fun h => absurd h hvm, fun _ x hx => ?_⟩
          rcases List.mem_or_eq_of_mem_set hx with hx | rfl
          · exact hanswer hvm x (hrowsEq ▸ hx)
          · exact ⟨demand.message, count₀ + δ, by omega, hsize, hpullable,
              fun h => absurd (hbyMessage ▸ h) (by simp), rfl⟩
        · exact hinv.rows _ (List.getElem_mem hj)
      · have hlength := length_statesInteractions_set hstate (state.rows.set position' updated)
          run.data0
        simp only [List.length_set] at hlength
        simp only [Balancing.apply, List.length_append, hinv.interactions, hlengthRow]
        omega
      · intro channel hchannel'
        have hanswered := run.answeredMsgs_set hstate (state.rows.set position' updated) channel
        have hpulled := run.pulledMsgs_set hstate (state.rows.set position' updated) channel
        have hrowAnswered := sum_map_set_add (fun row => run.answeredBy state row channel)
          state.rows position' hposition updated
        have hrowPulled := sum_map_set_add (fun row => run.pulledBy state row channel)
          state.rows position' hposition updated
        have hrow'' : state.rows[position'] = row' := (List.getElem?_eq_some_iff.mp hrow').2
        rw [hrow''] at hrowAnswered hrowPulled
        simp only [Balancing.apply]
        have hold := hinv.answered_le channel hchannel'
        by_cases hmodeChannelEq : channel = mode.channel.name
        · subst hmodeChannelEq
          have hzero : ∀ row, run.pulledBy state row mode.channel.name = 0 := by
            intro row
            simp [pulledBy, (hanswers _).mpr rfl]
          simp only [hzero, List.map_const', List.sum_replicate, smul_zero, add_zero] at hpulled
          rw [hanswered₀, hansweredU, Multiset.replicate_add, ← add_assoc,
            add_right_comm _ (Multiset.replicate count₀ demand.message)] at hrowAnswered
          have hrows' := add_right_cancel hrowAnswered
          rw [hrows', ← add_assoc] at hanswered
          have hAnswered : run.answeredMsgs (balancing.states.set index
              { state with rows := state.rows.set position' updated }) mode.channel.name =
              run.answeredMsgs balancing.states mode.channel.name +
                Multiset.replicate δ demand.message := by
            apply add_right_cancel (b := (state.rows.map fun row =>
              run.answeredBy state row mode.channel.name).sum)
            rw [hanswered]
            abel
          rw [hAnswered, hpulled, Multiset.le_iff_count]
          intro message'
          rw [Multiset.count_add, Multiset.count_replicate]
          rw [hmodeChannel] at hcount
          split_ifs with hmessage
          · subst hmessage
            omega
          · simpa using Multiset.le_iff_count.mp hold message'
        · have hnot : ¬AnswersPull state channel := fun h => hmodeChannelEq ((hanswers _).mp h)
          rw [hfacts₀.answered_zero _ hchannel' hnot, hfactsU.answered_zero _ hchannel' hnot,
            add_zero, add_zero] at hrowAnswered
          rw [← hrowAnswered, add_left_inj] at hanswered
          rw [hinv.pulledBy_eq hmemState hrowsNe hfacts₀ hfactsU hchannel' hnot
            (hindependent channel hmodeChannelEq), add_left_inj] at hrowPulled
          rw [← hrowPulled, add_left_inj] at hpulled
          rw [hanswered, hpulled]
          exact hold
    · apply measure_lt_right
      · simp only [Balancing.apply, hlengthRow]
        omega
      · have hδ : (δ : F p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd
          have := Nat.le_of_dvd hpos hdvd
          omega
        have hlength := length_apply_of_update (states := balancing.states.set index
          { state with rows := state.rows.set position' updated })
          (change := ⟨rowInteractions state row' run.data0, rowInteractions state updated run.data0⟩)
          hinv.canonical hδ (by rw [hinv.canonical.netOf_eq hdemand, hmult]) ?_
        · omega
        intro channel' message'
        by_cases hchannelEq : channel' = demand.channel
        · subst hchannelEq
          rw [hmodeChannel] at hchannel ⊢
          rw [hfactsU.answered_net _ hchannel ((hanswers _).mpr rfl),
            hfacts₀.answered_net _ hchannel ((hanswers _).mpr rfl)]
          rw [show run.answeredBy state (run.answerRow state.component mode demand.message
            (count₀ + δ)) mode.channel.name = Multiset.replicate (count₀ + δ) demand.message from
            hansweredU, hanswered₀]
          simp only [Multiset.count_replicate, true_and]
          by_cases hm : message' = demand.message
          · subst hm
            simp
          · simp [hm, Ne.symm hm]
        · rw [hmodeChannel] at hchannelEq
          rw [hindependent channel' hchannelEq message', sub_self, if_neg (fun h => hchannelEq
            (h.1.trans hmodeChannel))]

/-- A preallocated component answers a deficit by raising the handler column of the row whose
handled interaction carries the message. -/
lemma step_preallocated (hinv : run.Inv k padded balancing) {demand : Demand (F p)} {index : ℕ}
    {state : ComponentState (F p)} (hstate : balancing.states[index]? = some state)
    (hdemand : demand ∈ balancing.demands) (hhandles : state.handles demand = true)
    {mode : PreallocatedMode (F p)} (hmode : state.rowPlan.mode = .preallocated mode)
    (hchannel : demand.channel ≠ run.complete.vm.channel.name) {δ : ℕ} (hpos : 0 < δ)
    (hlt : 2 * δ < p) (hmult : demand.multiplicity = -(δ : F p))
    (hcount : (run.answeredMsgs balancing.states demand.channel).count demand.message + δ =
      (run.pulledMsgs balancing.states demand.channel).count demand.message) :
    ∃ states change, handle balancing.states demand index run.data0 run.hint = .ok (states, change) ∧
      run.Inv k padded (balancing.apply states change) ∧
      Prod.Lex (· < ·) (· < ·) (balancing.apply states change).measure balancing.measure := by
  have hmemState := List.mem_of_getElem? hstate
  have hok := run.stateOk_of_shape hinv.shape hmemState
  have hdirection := (demand_pull hmult hpos hlt).1
  have hdemandCount := (demand_pull hmult hpos hlt).2
  have hobligation := run.complete.preallocated state.component hok.mem state.rowPlan mode
    (run.planned _ hok.entry) hmode run.publicInput run.proverInput run.assumptions run.stableData
    run.stableData_stable
  have hnodup := run.handled_nodup hok.entry
  simp only [hmode, Mode.handled] at hnodup
  -- the handler of the demand
  have hhandled := (run.handles_iff hok demand).mp hhandles
  rw [hdirection, hmode] at hhandled
  simp only [Mode.handled, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at hhandled
  obtain ⟨handler, hhandler, interaction, hinteraction, hname, -⟩ := hhandled
  obtain ⟨interaction', hinteraction', hdeclared, hrowsWith, hfacts⟩ :=
    hobligation.2.2.2.2 handler hhandler
  rw [hinteraction] at hinteraction'
  cases hinteraction'
  -- the message is pullable and some row carries it
  have hpulled : demand.message ∈ run.pulledMsgs balancing.states demand.channel :=
    Multiset.count_pos.mp (by omega)
  obtain ⟨hpullable, hsize⟩ := (run.pulled_facts hinv.statesOk hchannel hpulled).2
    interaction.channel hdeclared hname
  obtain ⟨row₀, hrow₀, hrowMessage⟩ := hrowsWith ⟨demand.message, hsize⟩
    (hpullable _ run.stableData_stable _ rfl)
  have hrowsOk := hinv.rows state hmemState
  simp only [RowsOk, hmode] at hrowsOk
  obtain ⟨hlength, hrowsEq⟩ := hrowsOk
  have hlengthGe : mode.rows.toNat ≤ state.rows.length := by
    rw [hlength]
    split
    · exact (le_targetHeight _ _).1
    · exact le_rfl
  obtain ⟨input₀, hreachable₀, hrowEq₀⟩ := hrowsEq row₀ (by omega)
  have hbase₀ := run.admissible_baseInput hok hmode row₀
  have hbaseEq : run.baseInput state.component state.rowPlan mode row₀ =
      preallocatedInput state.component mode run.hint row₀ := by
    simp [baseInput, hrow₀]
  have hmessage₀ : (interaction.eval (Environment.fromArray (state.rows[row₀]'(by omega)).values
      run.data0)).msg = demand.message := by
    rw [hrowEq₀]
    have hreach := run.msg_reachable hok hmode hinteraction hreachable₀ hbase₀
    rw [show interaction.eval (Environment.fromArray (run.row state.component input₀ none).values
      run.data0) = interaction.eval (run.rowEnv state.component input₀ run.stableData).toEnvironment
      by apply interaction_eval_congr; rfl, hreach]
    rw [hbaseEq] at hbase₀ ⊢
    exact hrowMessage _ (run.honestEnv_row hok.mem hbase₀.size _) rfl rfl
  have hpush : interaction.assumeGuarantees = false :=
    (hfacts _ _ (run.honestEnv_row hok.mem hbase₀.size _) rfl rfl
      (hbase₀.assumptions _ run.stableData_stable)).1
  have hhandles' : handler.handles state demand = true := by
    simp [PreallocatedHandler.handles, hok.interactions, hinteraction, hname, hdirection,
      handlerDirection, hpush]
  obtain ⟨⟨handler₁, position, row⟩, hfind⟩ := findPreallocatedRow_isSome hhandler hhandles'
    (List.getElem?_eq_getElem (by omega)) (hok.interactions ▸ hinteraction) hmessage₀
  obtain ⟨hhandler₁, hhandles₁, hrow, interaction₁, hinteraction₁, hmessage⟩ :=
    findPreallocatedRow_some hfind
  rw [hok.interactions] at hinteraction₁
  have hsame : handler₁ = handler := by
    apply filterMap_nodup_unique hnodup hhandler₁ hhandler (b := (demand.channel, Direction.pull))
    · simp only [PreallocatedHandler.handles, hok.interactions, hinteraction₁, Bool.and_eq_true,
        beq_iff_eq, hdirection] at hhandles₁
      rw [hinteraction₁]
      simp [hhandles₁.1, hhandles₁.2]
    · rw [hinteraction]
      simp [hname, handlerDirection, hpush]
  subst handler₁
  rw [hinteraction] at hinteraction₁
  cases hinteraction₁
  have hposition : position < state.rows.length := (List.getElem?_eq_some_iff.mp hrow).1
  obtain ⟨input, hreachable, hrowEq⟩ := hrowsEq position hposition
  have hrowIs : row = run.row state.component input none := by
    rw [← hrowEq]
    exact ((List.getElem?_eq_some_iff.mp hrow).2).symm
  subst hrowIs
  have hadmissible := run.admissible_of_reachable hok hmode hreachable
    (run.admissible_baseInput hok hmode position)
  set value : F p := (input[handler.column]?.getD 0) + FiniteField.fromNat demand.count
  set input' := input.set! handler.column value
  have hreachable' : Reachable mode.handlers (run.baseInput state.component state.rowPlan mode
      position) input' := hreachable.set handler hhandler value
  have hadmissible' := run.admissible_of_reachable hok hmode hreachable'
    (run.admissible_baseInput hok hmode position)
  set updated := run.row state.component input' none
  have hupdated : completeRow balancing.states [] state input' run.data0 run.hint none
      (run.row state.component input none).undefined = (updated, []) :=
    run.completeRow_eq hinv.viewOk hok hadmissible'.size none
  have hmutation : handlePreallocated balancing.states state mode.handlers demand run.data0 run.hint =
      some (Mutation.mk { state with rows := state.rows.set position updated }
        [run.row state.component input none] [updated] []) := by
    simp only [handlePreallocated, hfind]
    rw [show (run.row state.component input none).input = input from rfl]
    rw [hupdated]
  have hhandle := run.handle_preallocated hstate hmode hmutation rfl
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hhandle
  refine ⟨_, _, hhandle, ?_⟩
  have hchanges := handle_spec _ _ _ _ _ hhandle
  have hhonest := run.honestEnv_row hok.mem hadmissible.size run.stableData
  have hhonest' := run.honestEnv_row hok.mem hadmissible'.size run.stableData
  obtain ⟨-, hmult₀, hset⟩ := hfacts input _ hhonest rfl rfl
    (hadmissible.assumptions _ run.stableData_stable)
  obtain ⟨hmessageSame, hother⟩ := hset value _ hhonest' rfl rfl
  have hmult₁ := (hfacts input' _ hhonest' rfl rfl
    (hadmissible'.assumptions _ run.stableData_stable)).2.1
  have hcolumn : handler.column < input.size := by
    rw [hadmissible.size]
    exact (((run.planValid.row_plans _ hok.entry).preallocated mode hmode).2 handler hhandler).2.2
  have hvalue : input'[handler.column]?.getD 0 = value := by
    simp [input', hcolumn]
  rw [hvalue] at hmult₁
  set env₀ := run.rowEnv state.component input run.stableData
  set env₁ := run.rowEnv state.component input' run.stableData
  have hrowInts₀ : rowInteractions state (run.row state.component input none) run.data0 =
      interactionsIn state.component env₀.toEnvironment :=
    run.rowInteractions_row hok.interactions hok.mem hadmissible.size none run.stableData_stable
  have hrowInts₁ : rowInteractions state updated run.data0 =
      interactionsIn state.component env₁.toEnvironment :=
    run.rowInteractions_row hok.interactions hok.mem hadmissible'.size none run.stableData_stable
  have hindexLt : handler.interaction < (interactionsIn state.component env₀.toEnvironment).length := by
    simp only [interactionsIn, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hinteraction).1
  have hL₀ : (interactionsIn state.component env₀.toEnvironment)[handler.interaction] =
      interaction.eval env₀.toEnvironment := by
    simp [interactionsIn, (List.getElem?_eq_some_iff.mp hinteraction).2]
  have hL : interactionsIn state.component env₁.toEnvironment =
      (interactionsIn state.component env₀.toEnvironment).set handler.interaction
        (interaction.eval env₁.toEnvironment) := by
    rw [eq_set_of_agree (by simp [interactionsIn]) hindexLt hother]
    congr 1
    simp [interactionsIn, (List.getElem?_eq_some_iff.mp hinteraction).2]
  have hmessage₀ : (interaction.eval env₀.toEnvironment).msg = demand.message := by
    rw [← hmessage]
    congr 1
    apply interaction_eval_congr
    rfl
  have hmessage₁ : (interaction.eval env₁.toEnvironment).msg = demand.message :=
    hmessageSame.trans hmessage₀
  have hcountEq : FiniteField.fromNat demand.count = (δ : F p) := by
    rw [hdemandCount]; rfl
  have hdiff : ∀ channel' message',
      netOfInteractions (rowInteractions state updated run.data0) channel' message' -
        netOfInteractions (rowInteractions state (run.row state.component input none) run.data0)
          channel' message' =
      if channel' = demand.channel ∧ message' = demand.message then (δ : F p) else 0 := by
    intro channel' message'
    rw [hrowInts₁, hrowInts₀, hL, netOfInteractions_set _ hindexLt, hL₀]
    simp only [contribution, AbstractInteraction.eval_channel, hname, hmessage₀, hmessage₁,
      hmult₀, hmult₁, value, hcountEq]
    by_cases hkey : demand.channel = channel' ∧ demand.message = message'
    · obtain ⟨rfl, rfl⟩ := hkey
      simp only [and_self, if_true]
      ring
    · rw [if_neg hkey, if_neg hkey, if_neg fun h => hkey ⟨h.1.symm, h.2.symm⟩]
      ring
  -- what the row and its update answer
  have hanswered₀ := run.answeredBy_preallocated hok hmode hadmissible hhandler hinteraction
  have hanswered₁ := run.answeredBy_preallocated hok hmode hadmissible' hhandler hinteraction
  rw [hname, hmessage₀] at hanswered₀
  rw [hname, hmessage₁, hvalue] at hanswered₁
  have hrowMem : run.row state.component input none ∈ state.rows := List.mem_of_getElem? hrow
  have hold := hinv.answered_le _ hchannel
  have hvalBound : (input[handler.column]?.getD 0).val + δ < p := by
    have h1 : (input[handler.column]?.getD 0).val ≤
        (run.answeredMsgs balancing.states demand.channel).count demand.message := by
      have hle : run.answeredBy state (run.row state.component input none) demand.channel ≤
          run.answeredMsgs balancing.states demand.channel :=
        le_trans (List.le_sum_of_mem (List.mem_map_of_mem (f := fun row =>
          run.answeredBy state row demand.channel) hrowMem))
          (List.le_sum_of_mem (List.mem_map_of_mem (f := fun state => (state.rows.map fun row =>
            run.answeredBy state row demand.channel).sum) hmemState))
      have := Multiset.count_le_of_le demand.message hle
      rwa [hanswered₀, Multiset.count_replicate_self] at this
    have h2 := Multiset.count_le_card demand.message (run.pulledMsgs balancing.states demand.channel)
    have h3 := run.card_pulledMsgs_le_length balancing.states demand.channel
    have h4 := hinv.length_lt
    omega
  have hvalValue : value.val = (input[handler.column]?.getD 0).val + δ := by
    simp only [value, hcountEq]
    rw [ZMod.val_add_of_lt (by rw [ZMod.val_natCast_of_lt (by omega)]; exact hvalBound),
      ZMod.val_natCast_of_lt (by omega)]
  rw [hvalValue, Multiset.replicate_add] at hanswered₁
  -- other channels see the same row
  have hanswersChannel : AnswersPull state demand.channel := by
    rw [AnswersPull, hmode, ← hdirection]
    exact (run.handles_iff hok demand).mp hhandles |> fun h => by rwa [hmode] at h
  have hAnsweredOther : ∀ channel, channel ≠ demand.channel →
      run.answeredBy state updated channel =
        run.answeredBy state (run.row state.component input none) channel := by
    intro channel hchannel'
    simp only [answeredBy, hmode]
    congr 1
    apply List.map_congr_left
    intro handler' hhandler'
    rw [hok.interactions]
    split
    · rename_i interaction' hinteraction'
      split_ifs with hname'
      · have hne : handler'.interaction ≠ handler.interaction := by
          intro heq
          rw [heq, hinteraction] at hinteraction'
          cases hinteraction'
          exact hchannel' (hname'.symm.trans hname)
        have hsameInteraction := hother handler'.interaction hne
        simp only [interactionsIn, List.getElem?_map, hinteraction', Option.map_some,
          Option.some.injEq] at hsameInteraction
        obtain ⟨interaction'', hinteraction'', -, -, hfacts'⟩ :=
          hobligation.2.2.2.2 handler' hhandler'
        rw [hinteraction'] at hinteraction''
        cases hinteraction''
        have hmultSame : input'[handler'.column]?.getD 0 = input[handler'.column]?.getD 0 := by
          rw [← (hfacts' input' _ hhonest' rfl rfl
              (hadmissible'.assumptions _ run.stableData_stable)).2.1,
            ← (hfacts' input _ hhonest rfl rfl
              (hadmissible.assumptions _ run.stableData_stable)).2.1, hsameInteraction]
        have hmsgSame : (interaction'.eval (Environment.fromArray updated.values run.data0)).msg =
            (interaction'.eval (Environment.fromArray (run.row state.component input none).values
              run.data0)).msg := by
          rw [show interaction'.eval (Environment.fromArray updated.values run.data0) =
              interaction'.eval env₁.toEnvironment by apply interaction_eval_congr; rfl,
            show interaction'.eval (Environment.fromArray (run.row state.component input none).values
              run.data0) = interaction'.eval env₀.toEnvironment by apply interaction_eval_congr; rfl,
            hsameInteraction]
        simp only [updated, Run.row] at hmsgSame ⊢
        rw [hmultSame, hmsgSame]
      · rfl
    · rfl
  have hPulledOther : ∀ channel, channel ≠ demand.channel →
      channel ≠ run.complete.vm.channel.name →
      run.pulledBy state updated channel =
        run.pulledBy state (run.row state.component input none) channel := by
    intro channel hchannel' hvm'
    by_cases hnot : AnswersPull state channel
    · simp [pulledBy, hnot]
    · refine (hinv.pulledBy_eq hmemState (List.ne_nil_of_mem hrowMem)
        (run.rowFacts_preallocated hok hmode hadmissible)
        (run.rowFacts_preallocated hok hmode hadmissible') hvm' hnot fun message' => ?_).symm
      have := hdiff channel message'
      rw [if_neg fun h => hchannel' h.1] at this
      exact (sub_eq_zero.mp this).symm
  have hlengthRow : ∀ row, (rowInteractions state row run.data0).length =
      state.interactions.length := by simp [rowInteractions]
  have hrowAt : state.rows[position] = run.row state.component input none :=
    (List.getElem?_eq_some_iff.mp hrow).2
  have hsameOther : ∀ channel, channel ≠ demand.channel → channel ≠ run.complete.vm.channel.name →
      run.answeredMsgs (balancing.states.set index
        { state with rows := state.rows.set position updated }) channel =
        run.answeredMsgs balancing.states channel ∧
      run.pulledMsgs (balancing.states.set index
        { state with rows := state.rows.set position updated }) channel =
        run.pulledMsgs balancing.states channel := by
    intro channel hchannelEq hchannel'
    have hanswered := run.answeredMsgs_set hstate (state.rows.set position updated) channel
    have hpulled := run.pulledMsgs_set hstate (state.rows.set position updated) channel
    have hrowAnswered := sum_map_set_add (fun row => run.answeredBy state row channel)
      state.rows position hposition updated
    have hrowPulled := sum_map_set_add (fun row => run.pulledBy state row channel)
      state.rows position hposition updated
    rw [hrowAt] at hrowAnswered hrowPulled
    rw [hAnsweredOther _ hchannelEq, add_left_inj] at hrowAnswered
    rw [← hrowAnswered, add_left_inj] at hanswered
    rw [hPulledOther _ hchannelEq hchannel', add_left_inj] at hrowPulled
    rw [← hrowPulled, add_left_inj] at hpulled
    exact ⟨hanswered, hpulled⟩
  have hindex : index < balancing.states.length := (List.getElem?_eq_some_iff.mp hstate).1
  constructor
  · refine ⟨hchanges.1.trans hinv.shape, ?_, hinv.steps_le, hinv.padded_steps,
      Balancing.tracks_apply hinv.tracks hchanges.2,
      (hinv.canonical.removeInteractions _).addInteractions _, ?_, ?_, ?_⟩
    · intro x hx
      rcases mem_set_cases hx with rfl | ⟨j, hj, hji, rfl⟩
      · simp only [RowsOk, hmode]
        refine ⟨by rw [List.length_set]; exact hlength, fun j' hj' => ?_⟩
        by_cases hj'' : j' = position
        · subst hj''
          exact ⟨input', hreachable', by simp [updated]⟩
        · rw [List.length_set] at hj'
          obtain ⟨input'', hreachable'', heq⟩ := hrowsEq j' hj'
          exact ⟨input'', hreachable'', by rw [List.getElem_set_ne (Ne.symm hj'')]; exact heq⟩
      · exact hinv.rows _ (List.getElem_mem hj)
    · have hlength := length_statesInteractions_set hstate (state.rows.set position updated)
        run.data0
      simp only [List.length_set] at hlength
      simp only [Balancing.apply, List.length_append, hinv.interactions, hlengthRow]
      omega
    · intro channel hchannel'
      have hanswered := run.answeredMsgs_set hstate (state.rows.set position updated) channel
      have hpulled := run.pulledMsgs_set hstate (state.rows.set position updated) channel
      have hrowAnswered := sum_map_set_add (fun row => run.answeredBy state row channel)
        state.rows position hposition updated
      have hrowPulled := sum_map_set_add (fun row => run.pulledBy state row channel)
        state.rows position hposition updated
      rw [hrowAt] at hrowAnswered hrowPulled
      simp only [Balancing.apply]
      have hold' := hinv.answered_le channel hchannel'
      by_cases hchannelEq : channel = demand.channel
      · subst hchannelEq
        have hzero : ∀ row, run.pulledBy state row demand.channel = 0 := by
          intro row
          simp [pulledBy, hanswersChannel]
        simp only [hzero, List.map_const', List.sum_replicate, smul_zero, add_zero] at hpulled
        rw [hanswered₁, hanswered₀, ← add_assoc, add_right_comm _ (Multiset.replicate _ _)]
          at hrowAnswered
        have hrows' := add_right_cancel hrowAnswered
        rw [hrows', ← add_assoc] at hanswered
        have hAnswered : run.answeredMsgs (balancing.states.set index
            { state with rows := state.rows.set position updated }) demand.channel =
            run.answeredMsgs balancing.states demand.channel +
              Multiset.replicate δ demand.message := by
          apply add_right_cancel (b := (state.rows.map fun row =>
            run.answeredBy state row demand.channel).sum)
          rw [hanswered]
          abel
        rw [hAnswered, hpulled, Multiset.le_iff_count]
        intro message'
        rw [Multiset.count_add, Multiset.count_replicate]
        split_ifs with hmessage'
        · subst hmessage'
          omega
        · simpa using Multiset.le_iff_count.mp hold' message'
      · obtain ⟨hanswered', hpulled'⟩ := hsameOther channel hchannelEq hchannel'
        rw [hanswered', hpulled']
        exact hold'
    · intro hpadded channel hchannel' hall
      have hgetState : (balancing.states.set index
          { state with rows := state.rows.set position updated })[index]'(by simpa using hindex) =
          { state with rows := state.rows.set position updated } := List.getElem_set_self ..
      have hnewMem : { state with rows := state.rows.set position updated } ∈
          balancing.states.set index { state with rows := state.rows.set position updated } :=
        List.mem_iff_getElem.mpr ⟨index, by simpa using hindex, hgetState⟩
      have hne : channel ≠ demand.channel := by
        rintro rfl
        obtain ⟨mode', hmode'⟩ := hall _ hnewMem hanswersChannel
        simp only at hmode'
        rw [hmode] at hmode'
        cases hmode'
      obtain ⟨hanswered', hpulled'⟩ := hsameOther channel hne hchannel'
      simp only [Balancing.apply]
      rw [hanswered', hpulled']
      apply hinv.padded_answered hpadded channel hchannel'
      intro other hother hanswersOther
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hother
      by_cases hji : j = index
      · subst hji
        obtain ⟨_, hstateEq⟩ := List.getElem?_eq_some_iff.mp hstate
        rw [hstateEq] at hanswersOther ⊢
        exact hall { state with rows := state.rows.set position updated } hnewMem hanswersOther
      · have hmem : balancing.states[j] ∈ balancing.states.set index
            { state with rows := state.rows.set position updated } := by
          rw [← List.getElem_set_ne (Ne.symm hji) (l := balancing.states)
            (a := { state with rows := state.rows.set position updated }) (by simpa using hj)]
          exact List.getElem_mem _
        exact hall _ hmem hanswersOther
  · apply measure_lt_right
    · simp only [Balancing.apply, hlengthRow]
      omega
    · have hδ : (δ : F p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have := Nat.le_of_dvd hpos hdvd
        omega
      have hlength := length_apply_of_update (states := balancing.states.set index
        { state with rows := state.rows.set position updated })
        (change := ⟨rowInteractions state (run.row state.component input none) run.data0,
          rowInteractions state updated run.data0⟩)
        hinv.canonical hδ (by rw [hinv.canonical.netOf_eq hdemand, hmult]) hdiff
      omega

/-- Every handled demand is handled with progress, keeping the invariant. -/
lemma step (hinv : run.Inv k padded balancing) {demand : Demand (F p)} {index : ℕ}
    (hfind : findAction balancing.states balancing.demands = some (demand, index)) :
    ∃ states change k', handle balancing.states demand index run.data0 run.hint =
      .ok (states, change) ∧ run.Inv k' padded (balancing.apply states change) ∧
      Prod.Lex (· < ·) (· < ·) (balancing.apply states change).measure balancing.measure := by
  obtain ⟨hdemand, state, hstate, hhandles⟩ := findAction_some hfind
  have hmemState := List.mem_of_getElem? hstate
  have hok := run.stateOk_of_shape hinv.shape hmemState
  rcases hinv.demand_cases hdemand with
    ⟨hchannel, hk, hpadded, ⟨hmessage, hmult⟩ | ⟨-, hmult⟩⟩ | ⟨hchannel, δ, hpos, hlt, hmult, hcount⟩
  · have hhandled := (run.handles_iff hok demand).mp hhandles
    rw [(demand_push hmult).1, hchannel] at hhandled
    have hvmHandled : (run.complete.vm.channel.name, Direction.push) ∈
        (({ mode := .demand run.complete.vm.mode, padding := run.complete.vm.padding } :
          RowPlan (F p)).mode.handled run.complete.vm.component) := by
      simp [Mode.handled, run.complete.vm.mode_channel, run.complete.vm.mode_direction]
    have hvm : state.component = run.complete.vm.component :=
      congrArg Prod.fst (run.handled_unique hok.entry run.vm_entry hhandled hvmHandled)
    obtain ⟨states, change, hhandle, hinv', hlt⟩ :=
      hinv.step_vm hstate hvm hk hpadded hmessage hmult
    exact ⟨states, change, k + 1, hhandle, hinv', hlt⟩
  · exfalso
    have hp : 2 * 1 < p := by
      have hnet := hinv.canonical.netOf_eq hdemand
      rw [hinv.tracks, hmult] at hnet
      obtain ⟨interaction, hmem, -⟩ := exists_of_netOfInteractions_ne_zero
        (hnet ▸ neg_ne_zero.mpr one_ne_zero)
      have := List.length_pos_of_mem hmem
      have := hinv.length_lt
      omega
    have hhandled := (run.handles_iff hok demand).mp hhandles
    rw [(demand_pull (δ := 1) (by simpa using hmult) one_pos hp).1, hchannel] at hhandled
    exact run.not_answersPull_vmChannel hok hhandled
  · have hdirection := (demand_pull hmult hpos hlt).1
    rcases hmode : state.rowPlan.mode with mode | mode
    · rcases haggregation : mode.aggregation
      · obtain ⟨states, change, hhandle, hinv', hlt'⟩ := hinv.step_new hstate hhandles hmode
          (.inl haggregation) hchannel hpos hlt hmult hcount
        exact ⟨states, change, k, hhandle, hinv', hlt'⟩
      · rcases hfound : state.rows.zipIdx.findSome? (fun (row, index) => row.origin.bind
            fun origin => if sameOrigin origin mode demand then some (row, origin, index) else none)
          with _ | ⟨row₀, origin, position⟩
        · obtain ⟨states, change, hhandle, hinv', hlt'⟩ := hinv.step_new hstate hhandles hmode
            (.inr ⟨haggregation, hfound⟩) hchannel hpos hlt hmult hcount
          exact ⟨states, change, k, hhandle, hinv', hlt'⟩
        · obtain ⟨states, change, hhandle, hinv', hlt'⟩ := hinv.step_update hstate hdemand hhandles
            hmode haggregation hfound hchannel hpos hlt hmult hcount
          exact ⟨states, change, k, hhandle, hinv', hlt'⟩
    · obtain ⟨states, change, hhandle, hinv', hlt'⟩ := hinv.step_preallocated hstate hdemand
        hhandles hmode hchannel hpos hlt hmult hcount
      exact ⟨states, change, k, hhandle, hinv', hlt'⟩

/-- Once demand is settled, the VM has run all its steps. -/
lemma steps_of_settled (hinv : run.Inv k padded balancing) (hsettled : balancing.demands = []) :
    k = run.steps := by
  by_contra hne
  have hk : k < run.steps := lt_of_le_of_ne hinv.steps_le hne
  have hnet := hinv.tracks run.complete.vm.channel.name (run.complete.vm.state run.publicInput k)
  rw [hinv.net_vm, hsettled] at hnet
  simp [run.distinct k hk] at hnet

/-- Once demand is settled, every message is answered as often as it is pulled. -/
lemma answered_eq_of_settled (hinv : run.Inv k padded balancing)
    (hsettled : balancing.demands = []) {channel : String}
    (hchannel : channel ≠ run.complete.vm.channel.name) :
    run.answeredMsgs balancing.states channel = run.pulledMsgs balancing.states channel := by
  ext message
  have hnet := hinv.tracks channel message
  rw [run.net_eq_answered_sub_pulled hinv.statesOk hchannel, hsettled, netOf_nil] at hnet
  have hle := Multiset.le_iff_count.mp (hinv.answered_le _ hchannel) message
  have hcount := Multiset.count_le_card message (run.pulledMsgs balancing.states channel)
  have hcard := run.card_pulledMsgs_le_length balancing.states channel
  have hlength := hinv.length_lt
  have heq := (ZMod.natCast_eq_natCast_iff' _ _ p).mp (sub_eq_zero.mp hnet.symm)
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq

lemma tablesArePadded_of_padded (hinv : run.Inv k true balancing) :
    tablesArePadded balancing.states = true := by
  simp only [tablesArePadded, List.all_eq_true, beq_iff_eq]
  intro state hstate
  have hrows := hinv.rows state hstate
  unfold RowsOk at hrows
  split at hrows
  · rw [hrows.1, if_pos rfl, targetHeight_targetHeight]
  · obtain ⟨main, pad, hrowsEq, -, htarget, -, -⟩ := hrows
    rw [hrowsEq, List.length_append, List.length_replicate, htarget rfl, targetHeight_targetHeight]

/-- Padding rows add no answers. -/
lemma answeredBy_paddingRow (hinv : run.Inv k padded balancing) {state : ComponentState (F p)}
    (hstate : state ∈ balancing.states) {channel : String}
    (hchannel : channel ≠ run.complete.vm.channel.name) :
    run.answeredBy state (run.paddingRow state) channel = 0 := by
  have hok := run.stateOk_of_shape hinv.shape hstate
  rcases hmode : state.rowPlan.mode with mode | mode
  · simp [answeredBy, hmode, paddingRow, Run.row]
  have hpadding := run.complete.padding state.component hok.mem state.rowPlan
    (run.planned _ hok.entry) run.publicInput run.proverInput run.assumptions run.stableData
    run.stableData_stable
  have hsize : state.rowPlan.padding.input.size = state.component.rowOffset :=
    (run.planValid.row_plans _ hok.entry).padding_width
  have hadmissible : run.Admissible state.component state.rowPlan.padding.input :=
    ⟨hsize, fun data hstable => (run.complete.padding state.component hok.mem state.rowPlan
      (run.planned _ hok.entry) run.publicInput run.proverInput run.assumptions data hstable).1⟩
  by_cases hanswers : AnswersPull state channel
  · have hhandled := hanswers
    simp only [AnswersPull, hmode, Mode.handled, List.mem_filterMap, Option.map_eq_some_iff,
      Prod.mk.injEq] at hhandled
    obtain ⟨handler, hhandler, interaction, hinteraction, hname, -⟩ := hhandled
    rw [paddingRow, ← hname, run.answeredBy_preallocated hok hmode hadmissible hhandler hinteraction]
    obtain ⟨interaction', hinteraction', -, -, hfacts⟩ :=
      (run.complete.preallocated state.component hok.mem state.rowPlan mode
        (run.planned _ hok.entry) hmode run.publicInput run.proverInput run.assumptions
        run.stableData run.stableData_stable).2.2.2.2 handler hhandler
    rw [hinteraction] at hinteraction'
    cases hinteraction'
    have hhonest := run.honestEnv_row hok.mem hsize run.stableData
    obtain ⟨hpush, hmult, -⟩ := hfacts _ _ hhonest rfl rfl
      (hadmissible.assumptions _ run.stableData_stable)
    have hside := hpadding.2 _ hhonest rfl rfl (interaction.eval
      (run.rowEnv state.component state.rowPlan.padding.input run.stableData).toEnvironment)
      (List.mem_map.mpr ⟨interaction, List.mem_of_getElem? hinteraction, rfl⟩)
    rcases hside with hzero | ⟨⟨hpull, -⟩, -⟩
    · rw [← hmult, hzero]
      simp
    · rw [hpull] at hpush
      cases hpush
  · exact (run.rowFacts_preallocated hok hmode hadmissible).answered_zero channel hchannel hanswers

omit [Fact p.Prime] in
lemma sum_map_add' {α : Type*} {M : Type*} [AddCommMonoid M] (values : List α) (f g : α → M) :
    (values.map fun x => f x + g x).sum = (values.map f).sum + (values.map g).sum := by
  induction values with
  | nil => simp
  | cons head rest ih => simp [ih]; abel

lemma answeredMsgs_pad (hinv : run.Inv k padded balancing) {channel : String}
    (hchannel : channel ≠ run.complete.vm.channel.name) :
    run.answeredMsgs (balancing.states.map run.padOne) channel =
      run.answeredMsgs balancing.states channel := by
  simp only [answeredMsgs, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro state hstate
  simp only [padOne, List.map_append, List.sum_append, sum_map_replicate]
  rw [show run.answeredBy { state with rows := (state.rows ++ List.replicate (padCount state)
    (run.paddingRow state)) } (run.paddingRow state) channel = 0 from
    hinv.answeredBy_paddingRow hstate hchannel, smul_zero, add_zero]
  rfl

lemma pulledMsgs_pad (channel : String) :
    run.pulledMsgs (balancing.states.map run.padOne) channel =
      run.pulledMsgs balancing.states channel + (balancing.states.map fun state =>
        padCount state • run.pulledBy state (run.paddingRow state) channel).sum := by
  simp only [pulledMsgs, List.map_map, Function.comp_def, add_assoc]
  congr 1
  rw [← sum_map_add']
  congr 1
  apply List.map_congr_left
  intro state _
  simp only [padOne, List.map_append, List.sum_append, sum_map_replicate]
  rfl

/-- After settling demand, padding every component keeps the invariant, now padded. -/
lemma pad (hinv : run.Inv k false balancing) (hsettled : balancing.demands = []) :
    run.Inv run.steps true (balancing.apply (balancing.states.map run.padOne)
      ⟨[], balancing.states.flatMap (fun state => (List.replicate (padCount state)
        (run.paddingRow state)).flatMap (rowInteractions state · run.data0))⟩) := by
  have hk := hinv.steps_of_settled hsettled
  subst hk
  have hok : ∀ state ∈ balancing.states, run.StateOk state := fun state hstate =>
    run.stateOk_of_shape hinv.shape hstate
  have hchanges := padTables_spec run.data0 run.hint balancing.states
  rw [run.padTables_eq hinv.viewOk hok] at hchanges
  refine ⟨hchanges.1.trans hinv.shape, ?_, le_rfl, fun _ => rfl,
    Balancing.tracks_apply hinv.tracks hchanges.2,
    (hinv.canonical.removeInteractions _).addInteractions _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨state, hstate, rfl⟩ := List.mem_map.mp hx
    have hrows := hinv.rows state hstate
    rcases hmode : state.rowPlan.mode with mode | mode
    · simp only [RowsOk, hmode] at hrows
      simp only [RowsOk, padOne, hmode]
      obtain ⟨main, pad, hrowsEq, hpad, -, hvm, hanswer⟩ := hrows
      rw [hpad trivial, List.replicate_zero, List.append_nil] at hrowsEq
      refine ⟨main, padCount state, by rw [hrowsEq]; rfl, fun h => absurd h (by simp), fun _ => ?_,
        hvm, hanswer⟩
      simp only [padCount, hrowsEq]
      exact Nat.add_sub_cancel' (le_targetHeight _ _).1
    · simp only [RowsOk, hmode, Bool.false_eq_true, if_false] at hrows
      simp only [RowsOk, padOne, hmode, if_true]
      obtain ⟨hlength, hrowsEq⟩ := hrows
      refine ⟨?_, fun j hj => ?_⟩
      · rw [List.length_append, List.length_replicate, padCount, hlength]
        exact Nat.add_sub_cancel' (le_targetHeight _ _).1
      · by_cases hjrows : j < state.rows.length
        · obtain ⟨input, hreachable, heq⟩ := hrowsEq j hjrows
          exact ⟨input, hreachable, by rw [List.getElem_append_left hjrows]; exact heq⟩
        · refine ⟨state.rowPlan.padding.input, ?_, ?_⟩
          · have : run.baseInput state.component state.rowPlan mode j =
                state.rowPlan.padding.input := by
              simp [baseInput, show ¬ j < mode.rows.toNat by omega]
            rw [this]
            exact .base
          · rw [List.getElem_append_right (by omega), List.getElem_replicate]
            rfl
  · simp only [Balancing.apply, List.length_nil, Nat.sub_zero, List.length_append,
      hinv.interactions, length_statesInteractions, List.length_flatMap, List.map_map,
      Function.comp_def, padOne, List.length_replicate, rowInteractions, List.length_map,
      Nat.add_mul, List.map_replicate, List.sum_replicate, smul_eq_mul]
    rw [sum_map_add']
    ring
  · intro channel hchannel
    simp only [Balancing.apply]
    rw [hinv.answeredMsgs_pad hchannel, pulledMsgs_pad (run := run) (balancing := balancing)]
    exact le_trans (hinv.answered_le channel hchannel) le_self_add
  · intro _ channel hchannel hall
    simp only [Balancing.apply]
    rw [hinv.answeredMsgs_pad hchannel, pulledMsgs_pad (run := run) (balancing := balancing),
      hinv.answered_eq_of_settled hsettled hchannel]
    suffices h : ∀ state ∈ balancing.states, run.pulledBy state (run.paddingRow state) channel = 0 by
      rw [List.sum_eq_zero, add_zero]
      intro x hx
      obtain ⟨state, hstate, rfl⟩ := List.mem_map.mp hx
      rw [h state hstate, smul_zero]
    intro state hstate
    have hokState := hok state hstate
    unfold pulledBy
    split
    · rfl
    apply Multiset.eq_zero_of_forall_notMem
    intro message hmessage
    obtain ⟨interaction, hmem, hname, -, hmult, -⟩ := mem_pullsOf hmessage
    have hsize : state.rowPlan.padding.input.size = state.component.rowOffset :=
      (run.planValid.row_plans _ hokState.entry).padding_width
    rw [paddingRow, run.rowInteractions_row hokState.interactions hokState.mem hsize none
      run.stableData_stable] at hmem
    have hside := (run.complete.padding state.component hokState.mem state.rowPlan
      (run.planned _ hokState.entry) run.publicInput run.proverInput run.assumptions run.stableData
      run.stableData_stable).2 _ (run.honestEnv_row hokState.mem hsize _) rfl rfl interaction hmem
    rcases hside with hzero | ⟨-, -, hanswered⟩
    · rw [hmult] at hzero
      exact neg_ne_zero.mpr one_ne_zero hzero
    obtain ⟨entry, hentry, hhandled, hpreallocated⟩ := run.answers_entry hanswered
    obtain ⟨mode, hmode⟩ := hpreallocated rfl
    obtain ⟨other, hother, -, hcomponent, hrowPlan⟩ := run.find?_state hinv.shape hentry
    have hanswers : AnswersPull (run.padOne other) channel := by
      show (channel, Direction.pull) ∈ other.rowPlan.mode.handled other.component
      rw [hcomponent, hrowPlan, ← hname]
      exact hhandled
    obtain ⟨mode', hmode'⟩ := hall (run.padOne other) (List.mem_map_of_mem hother) hanswers
    simp only [padOne] at hmode'
    rw [hrowPlan, hmode] at hmode'
    cases hmode'

end Inv

/-- From an invariant state, balancing succeeds and settles all demand. -/
theorem balance_ok {padded : Bool} (balancing : Balancing (F p)) :
    ∀ k, run.Inv k padded balancing → ∃ k' balanced,
      balance run.data0 run.hint balancing = .ok balanced ∧ run.Inv k' padded balanced ∧
        balanced.demands = [] := by
  fun_induction balance run.data0 run.hint balancing with
  | case1 balancing hempty =>
      intro k hinv
      exact ⟨k, balancing, rfl, hinv, List.isEmpty_iff.mp hempty⟩
  | case2 balancing hempty hbound =>
      intro k hinv
      exact absurd hinv.interactions_lt (by simpa [FiniteField.char] using hbound)
  | case3 balancing hempty hbound hnone =>
      intro k hinv
      obtain ⟨result, hresult⟩ := findAction_isSome
        (hinv.exists_handled (by simpa using hempty))
      rw [hnone] at hresult
      cases hresult
  | case4 balancing hempty hbound demand index hfind error herror =>
      intro k hinv
      obtain ⟨states, change, k', hhandle, -⟩ := hinv.step hfind
      rw [hhandle] at herror
      cases herror
  | case5 balancing hempty hbound demand index hfind states change hhandle next hlt ih =>
      intro k hinv
      obtain ⟨states', change', k', hhandle', hinv', -⟩ := hinv.step hfind
      rw [hhandle] at hhandle'
      cases hhandle'
      exact ih k' hinv'
  | case6 balancing hempty hbound demand index hfind states change hhandle next hnot =>
      intro k hinv
      obtain ⟨states', change', k', hhandle', -, hlt'⟩ := hinv.step hfind
      rw [hhandle] at hhandle'
      cases hhandle'
      exact absurd hlt' hnot

end Run

end Air.Flat.WitnessGeneration
