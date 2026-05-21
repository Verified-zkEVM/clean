import Clean.Circuit.Explicit

variable {F : Type} [Field F] {α β : Type} {n : ℕ}

section
variable {Input Output : TypeMap}

structure FormalCircuitBase (F : Type) (Input Output : TypeMap)
    [Field F] [CircuitType Input] [CircuitType Output] where
  name : String := "anonymous"
  main : Var Input F → Circuit F (Var Output F)
  elaborated : ElaboratedCircuit F Input Output main := by first | infer_instance | infer_elaborated_circuit

namespace FormalCircuitBase
variable [CircuitType Input] [CircuitType Output]

abbrev output (self : FormalCircuitBase F Input Output) (input : Var Input F) (offset : ℕ) : Var Output F :=
  self.elaborated.output input offset

abbrev localLength (self : FormalCircuitBase F Input Output) (input : Var Input F) : ℕ :=
  self.elaborated.localLength input

abbrev channelsWithGuarantees (self : FormalCircuitBase F Input Output) : List (RawChannel F) :=
  self.elaborated.channelsWithGuarantees

abbrev channelsWithRequirements (self : FormalCircuitBase F Input Output) : List (RawChannel F) :=
  self.elaborated.channelsWithRequirements

abbrev exposedChannels (self : FormalCircuitBase F Input Output) (input : Var Input F) (offset : ℕ) : List (ExposedChannel F) :=
  self.elaborated.exposedChannels input offset

theorem localLength_eq (self : FormalCircuitBase F Input Output) (input : Var Input F) (offset : ℕ) :
  (self.main input).localLength offset = self.localLength input :=
  self.elaborated.localLength_eq input offset

theorem channelsLawful (self : FormalCircuitBase F Input Output) : ElaboratedCircuit.ChannelsLawful self.main
    self.channelsWithGuarantees self.channelsWithRequirements self.exposedChannels :=
  self.elaborated.channelsLawful

theorem subcircuitsConsistent (self : FormalCircuitBase F Input Output) (input : Var Input F) (offset : ℕ) :
   ((self.main input).operations offset).SubcircuitsConsistent offset :=
  self.elaborated.subcircuitsConsistent input offset
end FormalCircuitBase

section
variable [ProvableType Input] [ProvableType Output]

@[circuit_norm]
def Soundness (F : Type) [Field F] (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (Assumptions : Input F → Prop) (Spec : Input F → Output F → Prop) :=
  -- for all environments that determine witness assignments
  ∀ offset : ℕ, ∀ env : Environment F,
  -- for all inputs that satisfy the assumptions
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- if the constraints hold
  ConstraintsHold.Soundness env (main input_var |>.operations offset) →
  -- the spec holds on the input and output
  let output := eval env (ElaboratedCircuit.output main input_var offset)
  Spec input output ∧
  Operations.Requirements env (main input_var |>.operations offset)

@[circuit_norm]
def Completeness (F : Type) [Field F] (main : Var Input F → Circuit F (Var Output F))
    (Assumptions : Input F → Prop) :=
  -- for all prover environments which use the default witness generators for local variables
  ∀ offset : ℕ, ∀ env : ProverEnvironment F, ∀ input_var : Var Input F,
  env.UsesLocalWitnessesCompleteness offset (main input_var |>.operations offset) →
  -- for all inputs that satisfy the assumptions
  ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- the constraints hold
  ConstraintsHold.Completeness env (main input_var |>.operations offset)

/--
`FormalCircuit` is the main object that encapsulates correctness of a circuit.

It requires you to provide
- a spec, which is a relationship between inputs and outputs
- assumptions, which are the conditions that must hold for the circuit to make sense
- a proof of _soundness_: assumptions ∧ constraints → spec, for any witnesses
- a proof of _completeness_: assumptions → constraints, using some witnesses that exist

Note that soundness and completeness, taken together, show that the spec will hold for _all_ inputs.
This means that, when viewed as a black box, the circuit acts similar to a function. The assumptions act as
preconditions, and the spec acts as the postcondition.
-/
structure FormalCircuit (F : Type) [Field F] (Input Output : TypeMap) [ProvableType Input] [ProvableType Output]
    extends base : FormalCircuitBase F Input Output where
  Assumptions (_ : Input F) : Prop := True
  Spec : Input F → Output F → Prop
  soundness : Soundness F base.main Assumptions Spec
  completeness : Completeness F base.main Assumptions

/--
`DeterministicFormalCircuit` extends `FormalCircuit` with an explicit uniqueness constraint.
This ensures that for any input satisfying the assumptions, the specification uniquely determines the output.
Use this class when you want to formally guarantee that constraints uniquely determine the output,
preventing ambiguity in deterministic circuits.
-/
structure DeterministicFormalCircuit (F : Type) [Field F] (Input Output : TypeMap) [ProvableType Input] [ProvableType Output]
    extends circuit : FormalCircuit F Input Output where
  uniqueness : ∀ (input : Input F) (out1 out2 : Output F),
    circuit.Assumptions input → circuit.Spec input out1 → circuit.Spec input out2 → out1 = out2

@[circuit_norm]
def FormalAssertion.Soundness (F : Type) [Field F] (main : Var Input F → Circuit F Unit)
    (Assumptions : Input F → Prop) (Spec : Input F → Prop) :=
  -- for all environments that determine witness assignments
  ∀ offset : ℕ, ∀ env : Environment F,
  -- for all inputs that satisfy the assumptions
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  Assumptions input →
  -- if the constraints hold
  ConstraintsHold.Soundness env (main input_var |>.operations offset) →
  -- the spec holds on the input
  Spec input ∧
  Operations.Requirements env (main input_var |>.operations offset)

@[circuit_norm]
def FormalAssertion.Completeness (F : Type) [Field F] (main : Var Input F → Circuit F Unit)
    (Assumptions : Input F → Prop) (Spec : Input F → Prop) :=
  -- for all prover environments which use the default witness generators for local variables
  ∀ offset, ∀ env : ProverEnvironment F, ∀ input_var : Var Input F,
  env.UsesLocalWitnessesCompleteness offset (main input_var |>.operations offset) →
  -- for all inputs that satisfy the assumptions AND the spec
  ∀ input : Input F, eval env input_var = input →
  Assumptions input → Spec input →
  -- the constraints hold
  ConstraintsHold.Completeness env (main input_var |>.operations offset)

/--
`FormalAssertion` models a subcircuit that is "assertion-like":
- it doesn't return anything
- by design, it does not have `FormalCircuit`'s completeness. `FormalAssertion` further constrains its inputs.

The notion of _soundness_ is the same as for `FormalCircuit`: assumptions ∧ constraints → spec.

However, the _completeness_ statement is weaker: assumptions ∧ spec → constraints.

Given assumptions, the constraints might not be satisfiable and the spec must be an equivalent reformulation
of the constraints.
(In the case of `FormalCircuit`, given assumptions, the constraints are always satisfiable and the spec can be
strictly weaker than the constraints.)
-/
structure FormalAssertion (F : Type) (Input : TypeMap) [Field F] [ProvableType Input]
    extends base : FormalCircuitBase F Input unit where
  Assumptions (input : Input F) : Prop := True
  Spec : Input F → Prop
  soundness : FormalAssertion.Soundness F base.main Assumptions Spec
  completeness : FormalAssertion.Completeness F base.main Assumptions Spec

@[circuit_norm]
def GeneralFormalCircuit.Soundness (F : Type) [Field F]
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (Assumptions : Input F → ProverData F → Prop)
    (Spec : Input F → Output F → ProverData F → Prop) :=
  -- for all environments that determine witness assignments
  ∀ offset : ℕ, ∀ env : Environment F,
  -- for all inputs that satisfy the assumptions
  ∀ input_var : Var Input F, ∀ input : Input F, eval env input_var = input →
  Assumptions input env.data →
  -- if the constraints hold
  ConstraintsHold.Soundness env (main input_var |>.operations offset) →
  -- the spec holds on the input and output
  let output := eval env (ElaboratedCircuit.output main input_var offset)
  Spec input output env.data ∧
  Operations.Requirements env (main input_var |>.operations offset)

@[circuit_norm]
def GeneralFormalCircuit.Completeness (F : Type) [Field F]
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (ProverAssumptions : Input F → ProverData F → ProverHint F → Prop)
    (ProverSpec : Input F → Output F → ProverHint F → Prop) :=
  -- for all prover environments which use the default witness generators for local variables
  ∀ offset : ℕ, ∀ env : ProverEnvironment F, ∀ input_var : Var Input F,
  env.UsesLocalWitnessesCompleteness offset (main input_var |>.operations offset) →
  -- for all inputs that satisfy the "honest prover" assumptions
  ∀ input : Input F, eval env input_var = input →
  ProverAssumptions input env.data env.hint →
  -- the constraints hold
  ConstraintsHold.Completeness env (main input_var |>.operations offset) ∧
  -- and, if given, the prover spec holds
  ProverSpec input (eval env (ElaboratedCircuit.output main input_var offset)) env.hint

/--
`GeneralFormalCircuit` is the most general model of formal circuits, needed in cases where the circuit is a
_mix_ of "assertion-like" and "function-like". It allows you flexibility in specifying separate statements
to be proved in the soundness and completeness proofs, by
- only using the `Assumptions` and `Spec` in the soundness statement
- having separate `ProverAssumptions` and `ProverSpec` for the completeness statement
i.e. the two statements are not "coupled".

For example, take the `toBits n` circuit, which outputs the `n`-bit decomposition of the input.
To do so, the circuit, as a side effect, constrains the input to be representable in `n` bits.
Consequently, the input being `n` bits is a necessary assumption _for completeness_. However, _for soundness_,
this assumption is not needed as the circuit adds that constraint itself. Using `FormalCircuit` would unnecessarily
add the range assumption to the soundness statement, thus making the circuit hard to use
(in particular, not usable as a bit range check, because it already _requires_ the bit range assumption).
-/
structure GeneralFormalCircuit (F : Type) (Input Output : TypeMap) [Field F] [ProvableType Input] [ProvableType Output]
    extends base : FormalCircuitBase F Input Output where
  /-- the statement to be assumed for soundness -/
  Assumptions : Input F → ProverData F → Prop := fun _ _ => True
  /-- the statement to be proved for soundness. -/
  Spec : Input F → Output F → ProverData F → Prop

  /-- the statement to be assumed for completeness -/
  ProverAssumptions : Input F → ProverData F → ProverHint F → Prop := fun _ _ _ => True
  /-- auxiliary statement to be proved for completeness, alongside the constraints -/
  ProverSpec : Input F → Output F → ProverHint F → Prop := fun _ _ _ => True

  soundness : GeneralFormalCircuit.Soundness F base.main Assumptions Spec
  completeness : GeneralFormalCircuit.Completeness F base.main ProverAssumptions ProverSpec

@[circuit_norm]
def GeneralFormalCircuit.WithHint.Soundness (F : Type) [Field F]
    [CircuitType Input] [CircuitType Output]
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (Assumptions : Value Input F → ProverData F → Prop)
    (Spec : Value Input F → Value Output F → ProverData F → Prop) :=
  -- for all environments that determine witness assignments
  ∀ offset : ℕ, ∀ env : Environment F,
  -- for all inputs that satisfy the assumptions (verifier view — hints erased)
  ∀ input_var : Var Input F, ∀ input : Value Input F,
  eval env input_var = input →
  Assumptions input env.data →
  -- if the constraints hold
  ConstraintsHold.Soundness env (main input_var |>.operations offset) →
  -- the spec holds on the input and output
  let output := eval env (ElaboratedCircuit.output main input_var offset)
  Spec input output env.data ∧
  Operations.Requirements env (main input_var |>.operations offset)

@[circuit_norm]
def GeneralFormalCircuit.WithHint.Completeness (F : Type) [Field F]
    [CircuitType Input] [CircuitType Output]
    (main : Var Input F → Circuit F (Var Output F)) [ElaboratedCircuit F Input Output main]
    (ProverAssumptions : ProverValue Input F → ProverData F → ProverHint F → Prop)
    (ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop) :=
  -- for all prover environments which use the default witness generators for local variables
  ∀ offset : ℕ, ∀ env : ProverEnvironment F, ∀ input_var : Var Input F,
  env.UsesLocalWitnessesCompleteness offset (main input_var |>.operations offset) →
  -- for all inputs that satisfy the "honest prover" assumptions (prover view — hints visible)
  ∀ input : ProverValue Input F, eval env input_var = input →
  ProverAssumptions input env.data env.hint →
  -- the constraints hold
  ConstraintsHold.Completeness env (main input_var |>.operations offset) ∧
  -- and, if given, the prover spec holds
  ProverSpec input (eval env (ElaboratedCircuit.output main input_var offset)) env.hint

/--
Hint-aware variant of `GeneralFormalCircuit` for schemas whose prover and
verifier views differ.
-/
structure GeneralFormalCircuit.WithHint (F : Type) (Input Output : TypeMap) [Field F]
  [CircuitType Input] [CircuitType Output]
    extends base : FormalCircuitBase F Input Output where
  /-- the statement to be assumed for soundness (verifier view — hints erased) -/
  Assumptions : Value Input F → ProverData F → Prop := fun _ _ => True
  /-- the statement to be proved for soundness (verifier view). -/
  Spec : Value Input F → Value Output F → ProverData F → Prop

  /-- the statement to be assumed for completeness (prover view — hints visible) -/
  ProverAssumptions : ProverValue Input F → ProverData F → ProverHint F → Prop := fun _ _ _ => True
  /-- auxiliary statement to be proved for completeness, alongside the constraints (prover view) -/
  ProverSpec : ProverValue Input F → ProverValue Output F → ProverHint F → Prop := fun _ _ _ => True

  soundness : GeneralFormalCircuit.WithHint.Soundness F base.main Assumptions Spec
  completeness : GeneralFormalCircuit.WithHint.Completeness F base.main ProverAssumptions ProverSpec

@[circuit_norm]
def GeneralFormalCircuit.toWithHint {F : Type} [Field F] {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit F Input Output) :
    GeneralFormalCircuit.WithHint F Input Output where
  base := circuit.base
  Assumptions input data := circuit.Assumptions input data
  Spec input output data := circuit.Spec input output data
  ProverAssumptions input data hint := circuit.ProverAssumptions input data hint
  ProverSpec input output hint := circuit.ProverSpec input output hint
  soundness := by
    simpa only [GeneralFormalCircuit.WithHint.Soundness,
      CircuitType.eval_verifier, CircuitType.value_of_provableType]
      using circuit.soundness
  completeness := by
    simpa only [GeneralFormalCircuit.WithHint.Completeness,
      CircuitType.eval_prover, CircuitType.proverValue_of_provableType]
      using circuit.completeness

@[circuit_norm]
def GeneralFormalCircuit.channels (circuit : GeneralFormalCircuit F Input Output) :=
  circuit.channelsWithGuarantees ++ circuit.channelsWithRequirements

@[circuit_norm]
def GeneralFormalCircuit.WithHint.channels
    [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) :=
  circuit.channelsWithGuarantees ++ circuit.channelsWithRequirements
end

namespace FormalCircuitBase
variable [CircuitType Input] [CircuitType Output]

-- named projections of ChannelsLawful fields

theorem subcircuitChannelsWithGuarantees_subset_channelsWithGuarantees
  (circuit : FormalCircuitBase F Input Output) :
  ∀ input_var offset,
    ((circuit.main input_var).operations offset).subcircuitChannelsWithGuarantees ⊆
      circuit.channelsWithGuarantees := by
  intro input_var offset
  exact (circuit.channelsLawful input_var offset).1

theorem inChannelsOrGuarantees_channelsWithGuarantees
  (circuit : FormalCircuitBase F Input Output) :
  ∀ input_var offset env,
    ((circuit.main input_var).operations offset).InChannelsOrGuarantees
      circuit.channelsWithGuarantees env := by
  intro input_var offset env
  exact (circuit.channelsLawful input_var offset).2.1 env

theorem subcircuitChannelsWithRequirements_subset_channelsWithRequirements
    (circuit : FormalCircuitBase F Input Output) :
    ∀ input_var offset,
      ((circuit.main input_var).operations offset).subcircuitChannelsWithRequirements ⊆
        circuit.channelsWithRequirements := by
  intro input_var offset
  exact (circuit.channelsLawful input_var offset).2.2.1

theorem inChannelsOrRequirements_channelsWithRequirements
  (circuit : FormalCircuitBase F Input Output) :
  ∀ input_var offset env,
    ((circuit.main input_var).operations offset).InChannelsOrRequirements
      circuit.channelsWithRequirements env := by
  intro input_var offset env
  exact (circuit.channelsLawful input_var offset).2.2.2.1 env

theorem mem_channelsWithGuarantees_or_mem_channelsWithRequirements_of_mem_shallowChannels
  (circuit : FormalCircuitBase F Input Output) :
  ∀ input_var offset,
    let ops := (circuit.main input_var).operations offset
    ∀ channel ∈ ops.shallowChannels,
      channel ∈ circuit.channelsWithGuarantees ∨ channel ∈ circuit.channelsWithRequirements :=
  fun input_var offset => (circuit.channelsLawful input_var offset).2.2.2.2.1

theorem interactionsWith_eq_of_mem_exposedChannels (circuit : FormalCircuitBase F Input Output) :
  ∀ input_var offset,
    let ops := (circuit.main input_var).operations offset
    ∀ exposed ∈ circuit.exposedChannels input_var offset,
      ops.interactionsWith exposed.channel = exposed.interactions :=
  fun input_var offset => (circuit.channelsLawful input_var offset).2.2.2.2.2.1

theorem subcircuitChannelsLawful (circuit : FormalCircuitBase F Input Output) :
    ∀ input offset, ((circuit.main input).operations offset).SubcircuitChannelsLawful :=
  fun input offset => (circuit.channelsLawful input offset).2.2.2.2.2.2

@[circuit_norm]
def channels (circuit : FormalCircuitBase F Input Output) :=
  circuit.channelsWithGuarantees ++ circuit.channelsWithRequirements
end FormalCircuitBase
end
section
variable {F : Type} {Input Output : TypeMap} [Field F] [ProvableType Output] [ProvableType Input]

-- theorem about relationship between FormalCircuit and GeneralFormalCircuit

/--
`FormalCircuit.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` a generalization of
`FormalCircuit`. The idea is to make `FormalCircuit.Assumption` available in the soundness
by assuming it within `GeneralFormalCircuit.Spec`.
-/
@[circuit_norm]
def FormalCircuit.isGeneralFormalCircuit
    (orig : FormalCircuit F Input Output) : GeneralFormalCircuit F Input Output where
  base := orig.base
  Assumptions i _ := orig.Assumptions i
  Spec i o _ := orig.Spec i o
  ProverAssumptions i _ _ := orig.Assumptions i
  soundness := by
    intro offset env input_var input h_input h_assumptions h_holds
    exact orig.soundness offset env input_var input h_input h_assumptions h_holds
  completeness := by
    intro offset env input_var h_env input h_input h_assumptions
    exact ⟨orig.completeness offset env input_var h_env input h_input h_assumptions, trivial⟩

/--
`FormalAssertion.isGeneralFormalCircuit` explains how `GeneralFormalCircuit` is a generalization of
`FormalAssertion`.  The idea is to make `FormalAssertion.Spec` available in the completeness
by putting it within `GeneralFormalCircuit.Assumption`.
-/
@[circuit_norm]
def FormalAssertion.isGeneralFormalCircuit
    (orig : FormalAssertion F Input) : GeneralFormalCircuit F Input unit where
  base := orig.base
  Assumptions i _ := orig.Assumptions i
  Spec i _ _ := orig.Spec i
  ProverAssumptions i _ _ := orig.Assumptions i ∧ orig.Spec i
  soundness := by
    intro offset env input_var input h_input h_assumptions h_holds
    exact orig.soundness offset env input_var input h_input h_assumptions h_holds
  completeness := by
    intro offset env input_var h_env input h_input h_assumptions
    exact ⟨orig.completeness offset env input_var h_env input h_input h_assumptions.1 h_assumptions.2, trivial⟩

namespace FormalCircuitBase
omit [ProvableType Output] [ProvableType Input] in
theorem in_channels_or_guarantees_full
  [CircuitType Input] [CircuitType Output]
  (circuit : FormalCircuitBase F Input Output)
  (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    circuit.main input_var |>.operations n
    |>.InChannelsOrGuaranteesFull circuit.channelsWithGuarantees env := by
  have h_sublist := circuit.subcircuitChannelsWithGuarantees_subset_channelsWithGuarantees input_var n
  have h_guarantees_iff := circuit.inChannelsOrGuarantees_channelsWithGuarantees input_var n
  have h_lawful := circuit.subcircuitChannelsLawful input_var n
  generalize h_channels : circuit.channelsWithGuarantees = channels at *
  generalize h_ops : (circuit.main input_var).operations n = ops at *
  simp only [Operations.InChannelsOrGuaranteesFull, Operations.inChannelsOrGuarantees_iff_forall_mem,
    Operations.forall_interactions_iff, Operations.subcircuitChannelsWithGuarantees_subset_iff_forall,
    Operations.subcircuitChannelsLawful_iff_forall] at *
  simp_all only [implies_true, true_and]
  intro ⟨n, s⟩ s_mem i i_mem
  have h_guarantees_iff := (h_lawful ⟨n, s⟩ s_mem).1 env
  rw [FlatOperation.inChannelsOrGuarantees_iff_forall_mem] at h_guarantees_iff
  specialize h_guarantees_iff i i_mem
  tauto

omit [ProvableType Output] [ProvableType Input] in
theorem in_channels_or_requirements_full
  [CircuitType Input] [CircuitType Output]
  (circuit : FormalCircuitBase F Input Output)
  (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    circuit.main input_var |>.operations n
    |>.InChannelsOrRequirementsFull circuit.channelsWithRequirements env := by
  have h_sublist := circuit.subcircuitChannelsWithRequirements_subset_channelsWithRequirements input_var n
  have h_requirements_iff := circuit.inChannelsOrRequirements_channelsWithRequirements input_var n
  have h_lawful := circuit.subcircuitChannelsLawful input_var n
  generalize h_channels : circuit.channelsWithRequirements = channels at *
  generalize h_ops : (circuit.main input_var).operations n = ops at *
  simp only [Operations.InChannelsOrRequirementsFull, Operations.inChannelsOrRequirements_iff_forall_mem,
    Operations.forall_interactions_iff, Operations.subcircuitChannelsWithRequirements_subset_iff_forall,
    Operations.subcircuitChannelsLawful_iff_forall] at *
  simp_all only [implies_true, true_and]
  intro ⟨n, s⟩ s_mem i i_mem
  have h_requirements_iff := (h_lawful ⟨n, s⟩ s_mem).2.1 env
  rw [FlatOperation.inChannelsOrRequirements_iff_forall_mem] at h_requirements_iff
  specialize h_requirements_iff i i_mem
  tauto
end FormalCircuitBase

theorem Operations.guarantees_of_not_mem (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrGuaranteesFull channels env →
    ∀ channel, channel ∉ channels → ops.ChannelGuarantees channel env := by
  simp only [circuit_norm]
  intro h_in_or_guars channel h_not_mem i i_mem h_eq
  specialize h_in_or_guars i i_mem
  rw [h_eq] at h_in_or_guars
  tauto

theorem Operations.requirements_of_not_mem (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrRequirementsFull channels env →
    ∀ channel, channel ∉ channels → ops.ChannelRequirements channel env := by
  simp only [circuit_norm]
  intro h_in_or_reqs channel h_not_mem i i_mem h_eq
  specialize h_in_or_reqs i i_mem
  rw [h_eq] at h_in_or_reqs
  tauto

theorem GeneralFormalCircuit.requirements_of_not_mem
  (circuit : GeneralFormalCircuit F Input Output) (channel : RawChannel F)
  (input_var : Var Input F) (n : ℕ) (env : Environment F)
  (h_not_mem : channel ∉ circuit.channelsWithRequirements) :
    circuit.main input_var |>.operations n
    |>.ChannelRequirements channel env := by
  apply Operations.requirements_of_not_mem
  apply circuit.in_channels_or_requirements_full
  assumption

theorem Operations.guarantees_iff (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrGuaranteesFull channels env →
    (ops.FullGuarantees env ↔
      ∀ channel ∈ channels, ops.ChannelGuarantees channel env) := by
  simp only [circuit_norm]
  intro h_in_or_guars
  constructor
  · tauto
  intro h_guars i hi
  specialize h_in_or_guars i hi
  tauto

theorem GeneralFormalCircuit.guarantees_iff'
  (circuit : GeneralFormalCircuit F Input Output) (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    (circuit.main input_var |>.operations n).FullGuarantees env ↔
      ∀ channel ∈ circuit.channelsWithGuarantees, (circuit.main input_var |>.operations n).ChannelGuarantees channel env := by
  apply Operations.guarantees_iff
  apply circuit.in_channels_or_guarantees_full

theorem Operations.requirements_iff (ops : Operations F)
  (channels : List (RawChannel F)) (env : Environment F) :
    ops.InChannelsOrRequirementsFull channels env →
    (ops.FullRequirements env ↔
      ∀ channel ∈ channels, ops.ChannelRequirements channel env) := by
  simp only [circuit_norm]
  intro h_in_or_reqs
  constructor
  · tauto
  intro h_reqs i hi
  specialize h_in_or_reqs i hi
  tauto

theorem GeneralFormalCircuit.requirements_iff'
  (circuit : GeneralFormalCircuit F Input Output) (input_var : Var Input F) (n : ℕ) (env : Environment F) :
    (circuit.main input_var |>.operations n).FullRequirements env ↔
      ∀ channel ∈ circuit.channelsWithRequirements, (circuit.main input_var |>.operations n).ChannelRequirements channel env := by
  apply Operations.requirements_iff
  apply circuit.in_channels_or_requirements_full

theorem Operations.channels_subset {ops : Operations F} :
    ops.SubcircuitChannelsLawful →
    ops.channels ⊆ ops.shallowChannels ++
      ops.subcircuitChannelsWithGuarantees ++ ops.subcircuitChannelsWithRequirements := by
  intro h_lawful
  simp only [List.subset_def, channels, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [forall_interactions_iff, shallowChannels_eq_interactions_map]
  rw [Operations.subcircuitChannelsLawful_iff_forall] at h_lawful
  constructor
  · intro i i_mem; simp; left; use i
  intro ⟨ n, s ⟩ s_mem
  have h_all := (h_lawful ⟨n, s⟩ s_mem).2.2
  simp only [FlatOperation.channels, List.subset_def, List.mem_map, List.mem_append,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h_all
  simp only [subcircuitChannelsWithGuarantees_eq_subcircuits_map,
    subcircuitChannelsWithRequirements_eq_subcircuits_map, List.append_assoc, List.mem_append,
    List.mem_map, List.mem_flatten, PSigma.exists, ↓existsAndEq, and_true]
  intro i i_mem
  right
  specialize h_all i i_mem
  rcases h_all
  · left; use n, s
  · right; use n, s

omit [ProvableType Output] [ProvableType Input] in
theorem FormalCircuitBase.channels_subset
  [CircuitType Input] [CircuitType Output]
  (circuit : FormalCircuitBase F Input Output) (input_var : Var Input F) (n : ℕ) :
    ((circuit.main input_var).operations n).channels ⊆ circuit.channels := by
  have shallowChannels_subset := circuit.mem_channelsWithGuarantees_or_mem_channelsWithRequirements_of_mem_shallowChannels input_var n
  have channelsWithGuarantees_subset := circuit.subcircuitChannelsWithGuarantees_subset_channelsWithGuarantees input_var n
  have channelsWithRequirements_subset := circuit.subcircuitChannelsWithRequirements_subset_channelsWithRequirements input_var n
  simp only at *
  set ops := (circuit.main input_var).operations n
  trans ops.shallowChannels ++ ops.subcircuitChannelsWithGuarantees ++ ops.subcircuitChannelsWithRequirements
  apply Operations.channels_subset
  exact circuit.subcircuitChannelsLawful input_var n
  simp_all only [channels, List.append_assoc, List.append_subset, List.subset_append_of_subset_left,
    List.subset_append_of_subset_right, and_self, and_true]
  simp only [List.subset_def, List.mem_append]
  tauto
end
