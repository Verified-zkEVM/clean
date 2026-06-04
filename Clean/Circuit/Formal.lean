import Clean.Circuit.Explicit

variable {F : Type} [Field F] {α β : Type} {n : ℕ}

section
variable {Input Output : TypeMap}

@[explicit_circuit_unfold_type]
structure FormalCircuitBase (F : Type) (Input Output : TypeMap)
    [Field F] [CircuitType Input] [CircuitType Output] where
  name : String := "anonymous"
  main : Var Input F → Circuit F (Var Output F)
  elaborated : ElaboratedCircuit F Input Output main := by
    first | infer_instance | elaborate_circuit

  /-- optionally, you can expose the interactions with any channel in full detail -/
  exposedChannels : Var Input F → ℕ → List (ExposedChannel F) := fun _ _ => []
  exposedChannels_eq : ∀ input offset,
    ((main input).operations offset).ExposedChannelsLawful (exposedChannels input offset) := by
    dsimp only [Operations.ExposedChannelsLawful]
    try dsimp only [main]
    simp only [circuit_norm, seval]
    try first | ac_rfl | trivial | tauto

attribute [circuit_norm] FormalCircuitBase.elaborated FormalCircuitBase.exposedChannels

namespace FormalCircuitBase
variable [CircuitType Input] [CircuitType Output]
variable {name : String} {main : Var Input F → Circuit F (Var Output F)}
  {elaborated : ElaboratedCircuit F Input Output main}
  {exposedChannels : Var Input F → ℕ → List (ExposedChannel F)}
  {exposedChannels_eq : ∀ input offset,
    ((main input).operations offset).ExposedChannelsLawful (exposedChannels input offset)}

@[explicit_circuit_norm]
def output (self : FormalCircuitBase F Input Output) (input : Var Input F) (offset : ℕ) : Var Output F :=
  self.elaborated.output input offset

@[circuit_norm]
lemma output_def (input : Var Input F) (offset : ℕ) :
  ({name, main, elaborated, exposedChannels, exposedChannels_eq} : FormalCircuitBase F Input Output).output input offset =
    elaborated.output input offset := rfl

@[explicit_circuit_norm]
def localLength (self : FormalCircuitBase F Input Output) (input : Var Input F) : ℕ :=
  self.elaborated.localLength input

@[circuit_norm]
lemma localLength_def (input : Var Input F) :
  ({name, main, elaborated, exposedChannels, exposedChannels_eq} : FormalCircuitBase F Input Output).localLength input =
    elaborated.localLength input := rfl

@[explicit_circuit_norm]
def channelsWithGuarantees (self : FormalCircuitBase F Input Output) : List (RawChannel F) :=
  self.elaborated.channelsWithGuarantees

@[circuit_norm]
lemma channelsWithGuarantees_def :
  ({name, main, elaborated, exposedChannels, exposedChannels_eq} : FormalCircuitBase F Input Output).channelsWithGuarantees =
    elaborated.channelsWithGuarantees := rfl

@[explicit_circuit_norm]
def channelsWithRequirements (self : FormalCircuitBase F Input Output) : List (RawChannel F) :=
  self.elaborated.channelsWithRequirements

@[circuit_norm]
lemma channelsWithRequirements_def :
  ({name, main, elaborated, exposedChannels, exposedChannels_eq} : FormalCircuitBase F Input Output).channelsWithRequirements =
    elaborated.channelsWithRequirements := rfl

theorem localLength_eq (self : FormalCircuitBase F Input Output) (input : Var Input F) (offset : ℕ) :
  (self.main input).localLength offset = self.localLength input :=
  self.elaborated.localLength_eq input offset

theorem channelsLawful (self : FormalCircuitBase F Input Output) : ElaboratedCircuit.ChannelsLawful self.main
    self.channelsWithGuarantees self.channelsWithRequirements :=
  self.elaborated.channelsLawful

theorem subcircuitsConsistent (self : FormalCircuitBase F Input Output) (input : Var Input F) (offset : ℕ) :
   ((self.main input).operations offset).SubcircuitsConsistent offset :=
  self.elaborated.subcircuitsConsistent input offset
end FormalCircuitBase

section
variable [ProvableType Input] [ProvableType Output]

@[circuit_norm]
def Soundness (F : Type) [Field F] (main : Var Input F → Circuit F (Var Output F))
    [elaborated : ElaboratedCircuit F Input Output main]
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
@[explicit_circuit_unfold_type]
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
@[explicit_circuit_unfold_type]
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
@[explicit_circuit_unfold_type]
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
@[explicit_circuit_unfold_type]
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
  fun input_var offset => circuit.exposedChannels_eq input_var offset

theorem subcircuitChannelsLawful (circuit : FormalCircuitBase F Input Output) :
    ∀ input offset, ((circuit.main input).operations offset).SubcircuitChannelsLawful :=
  fun input offset => (circuit.channelsLawful input offset).2.2.2.2.2

@[circuit_norm]
def channels (circuit : FormalCircuitBase F Input Output) :=
  circuit.channelsWithGuarantees ++ circuit.channelsWithRequirements
end FormalCircuitBase
end
