module

public import Clean.Circuit.Basic
public import Clean.Circuit.Subcircuit

/-! # Recovering physical interactions across subcircuit boundaries

Channel declarations eliminate unrelated interactions. Exact interaction lists can
be recovered from exposed channels or the bundled child's main definition while
retaining Clean's formal subcircuit proof boundary.
-/

@[expose] public section

namespace InteractionRecovery

open Circuit Operations

variable {F : Type} [FiniteField F]

/-- A lawful subcircuit emits nothing on a channel absent from both sides of its declared
interface. -/
lemma interactionsWith_subcircuit_eq_nil_of_channelsLawful {n : ℕ}
    (subcircuit : Subcircuit F n) (channel : RawChannel F) (ops : Operations F)
    (h_g : channel ∉ subcircuit.channelsWithGuarantees)
    (h_r : channel ∉ subcircuit.channelsWithRequirements)
    (h_lawful : subcircuit.ChannelsLawful) :
    interactionsWith channel (.subcircuit subcircuit :: ops) = interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, List.filter_eq_nil_iff.mpr ?_, List.nil_append]
  intro i hi hci
  have hci' : i.channel = channel := by
    classical
    exact of_decide_eq_true hci
  have hmem : channel ∈ FlatOperation.channels subcircuit.ops.toFlat := by
    rw [FlatOperation.channels, ← hci']; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact (List.mem_append.mp (h_lawful.2.2 hmem)).elim h_g h_r

/-- **A formal subcircuit emits nothing on a channel it does not declare.** If `channel` is in
neither `circuit.channelsWithGuarantees` nor `circuit.channelsWithRequirements`, then the subcircuit
it produces contributes no interaction on `channel`, so it drops out of
`interactionsWith channel`. -/
lemma interactionsWith_formalSubcircuit_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output) (channel : RawChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops)
      = interactionsWith channel ops := by
  refine interactionsWith_subcircuit_eq_nil_of_channelsLawful _ _ _ ?_ ?_
    (FormalCircuit.toSubcircuit_channelsLawful (circuit := circuit) (n := n) (input_var := input))
  · rw [FormalCircuit.toSubcircuit_channelsWithGuarantees]
    exact h_g
  · rw [FormalCircuit.toSubcircuit_channelsWithRequirements]
    exact h_r

/-- General-formal-circuit companion to `interactionsWith_formalSubcircuit_eq_nil`. -/
lemma interactionsWith_generalSubcircuit_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops)
      = interactionsWith channel ops := by
  refine interactionsWith_subcircuit_eq_nil_of_channelsLawful _ _ _ ?_ ?_
    (GeneralFormalCircuit.toSubcircuit_channelsLawful
      (circuit := circuit) (n := n) (input_var := input))
  · rw [GeneralFormalCircuit.toSubcircuit_channelsWithGuarantees]
    exact h_g
  · rw [GeneralFormalCircuit.toSubcircuit_channelsWithRequirements]
    exact h_r

/-- Formal-assertion companion to `interactionsWith_formalSubcircuit_eq_nil`. -/
lemma interactionsWith_assertionSubcircuit_eq_nil {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (channel : RawChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit n input) :: ops)
      = interactionsWith channel ops := by
  refine interactionsWith_subcircuit_eq_nil_of_channelsLawful _ _ _ ?_ ?_
    (FormalAssertion.toSubcircuit_channelsLawful
      (circuit := circuit) (n := n) (input_var := input))
  · rw [FormalAssertion.toSubcircuit_channelsWithGuarantees]
    exact h_g
  · rw [FormalAssertion.toSubcircuit_channelsWithRequirements]
    exact h_r

/-- Reuse a child general circuit's exposed interaction when it is composed as a subcircuit. -/
lemma interactionsWith_generalSubcircuit_eq_of_mem_exposed
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (exposed : ExposedChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_exposed : exposed ∈ circuit.exposedChannels input n) :
    interactionsWith exposed.channel (.subcircuit (circuit.toSubcircuit n input) :: ops) =
      exposed.interactions ++ interactionsWith exposed.channel ops := by
  rw [interactionsWith_subcircuit, GeneralFormalCircuit.toSubcircuit_interactions]
  change interactionsWith exposed.channel ((circuit.main input).operations n) ++
    interactionsWith exposed.channel ops = _
  rw [circuit.interactionsWith_eq_of_mem_exposedChannels input n exposed h_exposed]

/-- Singleton-exposure form of `interactionsWith_generalSubcircuit_eq_of_mem_exposed`. -/
lemma interactionsWith_generalSubcircuit_eq_of_singleton_exposure
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (exposed : ExposedChannel F)
    {n : ℕ} (input : Var Input F) (ops : Operations F)
    (h_exposed : circuit.exposedChannels input n = [exposed]) :
    interactionsWith exposed.channel (.subcircuit (circuit.toSubcircuit n input) :: ops) =
      exposed.interactions ++ interactionsWith exposed.channel ops := by
  refine interactionsWith_generalSubcircuit_eq_of_mem_exposed circuit exposed input ops ?_
  rw [h_exposed]; exact List.mem_singleton_self exposed

/-- Transport an exact single-interaction projection of a bundled child's `main` across
its subcircuit boundary. -/
lemma interactionsWith_generalSubcircuit_of_main_exact {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ) (ops : Operations F)
    (interaction : AbstractInteraction F)
    (main_exact : ((circuit.main input).operations offset).interactionsWith channel =
      [interaction]) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit offset input) :: ops) =
      interaction :: interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, GeneralFormalCircuit.toSubcircuit_interactions]
  change interactionsWith channel ((circuit.main input).operations offset) ++
      interactionsWith channel ops = _
  rw [main_exact, List.singleton_append]

/-- List form of `interactionsWith_generalSubcircuit_of_main_exact`, for an arbitrary list
of interactions emitted on the channel. -/
lemma interactionsWith_generalSubcircuit_of_main_exact_list {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ) (ops : Operations F)
    (interactions : List (AbstractInteraction F))
    (main_exact : ((circuit.main input).operations offset).interactionsWith channel =
      interactions) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit offset input) :: ops) =
      interactions ++ interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, GeneralFormalCircuit.toSubcircuit_interactions]
  change interactionsWith channel ((circuit.main input).operations offset) ++
      interactionsWith channel ops = _
  rw [main_exact]

/-- Formal-assertion companion of `interactionsWith_generalSubcircuit_of_main_exact_list`. -/
lemma interactionsWith_assertionSubcircuit_of_main_exact {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ) (ops : Operations F)
    (interactions : List (AbstractInteraction F))
    (main_exact : ((circuit.main input).operations offset).interactionsWith channel =
      interactions) :
    interactionsWith channel (.subcircuit (circuit.toSubcircuit offset input) :: ops) =
      interactions ++ interactionsWith channel ops := by
  rw [interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions]
  change interactionsWith channel ((circuit.main input).operations offset) ++
      interactionsWith channel ops = _
  rw [main_exact]

/-- A circuit's `main` emits nothing on a channel outside its declared interface.
This follows from `ElaboratedCircuit.channels_subset` and matches the form left by
`circuit_norm` after reducing a formal subcircuit. -/
lemma interactionsWith_main_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ)
    (h : channel ∉ circuit.channels) :
    interactionsWith channel ((circuit.main input).operations offset) = [] := by
  rw [interactionsWith]
  apply List.filter_eq_nil_iff.mpr
  intro i hi hci
  have hci' : i.channel = channel := by
    classical
    exact of_decide_eq_true hci
  have hmem : channel ∈ ((circuit.main input).operations offset).channels := by
    rw [Operations.channels, ← hci']; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact h (circuit.channels_subset input offset hmem)

open Classical in
/-- Raw filtered-interaction form of channel exclusion for a formal assertion.
This matches the expression left by `circuit_norm` for assertion subcircuits. -/
lemma filter_interactions_formalAssertion_eq_nil {Input : TypeMap} [ProvableType Input]
    (circuit : FormalAssertion F Input) (channel : RawChannel F) {n : ℕ} (input : Var Input F)
    (h_g : channel ∉ circuit.channelsWithGuarantees)
    (h_r : channel ∉ circuit.channelsWithRequirements) :
    (FlatOperation.interactions (circuit.toSubcircuit n input).ops.toFlat).filter
      (fun i => i.channel = channel) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro i hi hci
  have hci' : i.channel = channel := by
    classical
    exact of_decide_eq_true hci
  have hsub := (FormalAssertion.toSubcircuit_channelsLawful (circuit := circuit) (n := n)
    (input_var := input)).2.2
  rw [FormalAssertion.toSubcircuit_channelsWithGuarantees,
    FormalAssertion.toSubcircuit_channelsWithRequirements] at hsub
  have hmem : channel ∈ FlatOperation.channels (circuit.toSubcircuit n input).ops.toFlat := by
    rw [FlatOperation.channels, ← hci']; exact List.mem_map.mpr ⟨i, hi, rfl⟩
  exact (List.mem_append.mp (hsub hmem)).elim h_g h_r

/-- `.2`-projection form of `interactionsWith_main_eq_nil`, matching the unfolding of
`Circuit.operations` by `circuit_norm`. The caller supplies the channel-exclusion premise. -/
lemma interactionsWith_main_snd_eq_nil {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuitBase F Input Output) (channel : RawChannel F)
    (input : Var Input F) (offset : ℕ)
    (h : channel ∉ circuit.channels) :
    interactionsWith channel (circuit.main input offset).2 = [] :=
  interactionsWith_main_eq_nil circuit channel input offset h

end InteractionRecovery
