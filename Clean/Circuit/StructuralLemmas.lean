import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Theorems

variable {F : Type} [FiniteField F]
  {Input Mid Output : TypeMap} [ProvableType Input] [ProvableType Mid] [ProvableType Output]

namespace FormalCircuit
instance (circuit : FormalCircuit F Input Output) : ElaboratedCircuit F Input Output circuit.main :=
  circuit.elaborated

/--
Concatenate two FormalCircuits into a single FormalCircuit.

This combinator requires:
- A compatibility proof that the first circuit's spec implies the second circuit's assumptions
- A proof that circuit1's output is independent of the offset (h_output_stable)

The composite circuit:
- Has the assumptions of the first circuit
- Has a spec stating that there exists an intermediate value such that both component specs hold
-/
def concat
    (circuit1 : FormalCircuit F Input Mid)
    (circuit2 : FormalCircuit F Mid Output)
    (h_compat : ∀ input mid, circuit1.Assumptions input → circuit1.Spec input mid → circuit2.Assumptions mid)
    (h_localLength_stable : ∀ mid mid', circuit2.localLength mid = circuit2.localLength mid') :
      FormalCircuit F Input Output where
  main := (circuit1 · >>= circuit2)
  elaborated := .fromExplicit (by infer_explicit_circuits) <| by
    constructor <;> simp +instances [explicit_circuit_norm, circuit_norm]
    · intro a n m
      apply h_localLength_stable
  channelsWithRequirements := circuit1.channelsWithRequirements ++ circuit2.channelsWithRequirements
  Assumptions := circuit1.Assumptions
  Spec input output := ∃ mid, circuit1.Spec input mid ∧ circuit2.Spec mid output
  soundness := by
    simp only [circuit_norm]
    aesop
  completeness := by
    simp only [circuit_norm]
    aesop
  -- Manual: generic construction over abstract child circuits. The tactic's grind close
  -- cannot instantiate `output_of_input_eq` here — the goal spells the child metadata as raw
  -- structure projections (`circuit1.elaborated.1`), which defeats e-matching even when the
  -- lemma is hinted — and the offset bounds need `h_localLength_stable` applied at specific
  -- output instantiations.
  computableWitnesses := by
    simp only [circuit_norm]
    intros n input env env'
    refine ⟨⟨?_, ?_⟩, ?_⟩
    -- circuit1's witnesses are computable directly from the shared input agreement
    · intro h_input_agrees
      exact circuit1.toSubcircuit_computableWitnesses h_input_agrees
    -- circuit2's witnesses need circuit1's *output* to only access below its offset
    · intro h_input_agrees
      apply circuit2.toSubcircuit_computableWitnesses_onlyAccessedBelow
      exact circuit1.output_onlyAccessedBelow (fun _ => h_input_agrees)
    -- the composite output agrees, chaining circuit1's then circuit2's output
    · intro h_input_agrees h_agrees
      refine circuit2.output_of_input_eq
        (circuit1.output_of_input_eq h_input_agrees ?_) ?_
      -- the composite `localLength` reduces to `ll₁ + ll₂`, then the offset bounds are `omega`-able
      · exact ProverEnvironment.agreesBelow_of_le h_agrees
          (by simp +instances only [circuit_norm, explicit_circuit_norm]; omega)
      · refine ProverEnvironment.agreesBelow_of_le h_agrees ?_
        have hs := h_localLength_stable (circuit1.output input n) (circuit1.output input 0)
        simp +instances only [circuit_norm, explicit_circuit_norm] at hs ⊢
        omega

@[circuit_norm]
lemma concat_assumptions (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    (c1.concat c2 p0 p1).Assumptions = c1.Assumptions := by
  simp only [concat]

@[circuit_norm]
lemma concat_localLength (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 inp :
  (c1.concat c2 p0 p1).localLength inp =
    c1.localLength inp + c2.localLength (c1.output inp 0) := by
  simp +instances only [concat, circuit_norm, explicit_circuit_norm]

@[circuit_norm]
lemma concat_localLength' (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 inp :
  ElaboratedCircuit.localLength (c1.concat c2 p0 p1).main inp =
    c1.localLength inp + c2.localLength (c1.output inp 0) := by
  simp +instances only [concat, circuit_norm, explicit_circuit_norm]

@[circuit_norm]
lemma concat_channelsWithGuarantees (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    (c1.concat c2 p0 p1).channelsWithGuarantees = c1.channelsWithGuarantees ++ c2.channelsWithGuarantees := by
  simp +instances only [explicit_circuit_norm, concat]

@[circuit_norm]
lemma concat_channelsWithGuarantees' (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    ElaboratedCircuit.channelsWithGuarantees (c1.concat c2 p0 p1).main =
      c1.channelsWithGuarantees ++ c2.channelsWithGuarantees := by
  simp +instances only [explicit_circuit_norm, concat]

/--
Weaken the specification of a FormalCircuit.

This combinator takes a FormalCircuit with a strong specification and produces
a new FormalCircuit with a weaker specification. This is useful when:
- You have a circuit that proves more than you need
- You want to compose circuits where the specs don't match exactly
- You need to adapt a specific circuit to a more general interface

The requirements are:
- The assumptions remain the same
- The stronger spec and the assumption imply the weaker spec
-/
def weakenSpec (circuit : FormalCircuit F Input Output)
    (WeakerSpec : Input F → Output F → Prop)
    (h_spec_implication : ∀ input output,
      circuit.Assumptions input →
      circuit.Spec input output →
      WeakerSpec input output) :
    FormalCircuit F Input Output where
  main := circuit.main
  elaborated := circuit.elaborated
  channelsWithRequirements := circuit.channelsWithRequirements
  requirementsChannelsLawful := circuit.requirementsChannelsLawful
  computableWitnesses := circuit.computableWitnesses
  Assumptions := circuit.Assumptions
  Spec := WeakerSpec
  soundness := by
    intro offset env input_var input h_eval h_assumptions h_holds
    -- Use the original circuit's soundness
    have h_strong_spec := circuit.soundness offset env input_var input h_eval h_assumptions h_holds
    -- Apply the implication to get the weaker spec
    exact ⟨h_spec_implication input _ h_assumptions h_strong_spec.1, h_strong_spec.2⟩
  completeness := by
    -- Completeness is preserved since we use the same elaborated circuit
    -- and the same assumptions
    exact circuit.completeness

@[circuit_norm] lemma weakenSpec_assumptions
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).Assumptions = c.Assumptions := by
  simp only [weakenSpec]

@[circuit_norm] lemma weakenSpec_localLength
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) :
    (c.weakenSpec WeakerSpec h_spec_implication).localLength input = c.localLength input := by
  rfl

@[circuit_norm] lemma weakenSpec_localLength'
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) :
    ElaboratedCircuit.localLength (c.weakenSpec WeakerSpec h_spec_implication).main input = c.localLength input := by
  rfl

@[circuit_norm] lemma weakenSpec_output
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) (offset : Nat) :
    (c.weakenSpec WeakerSpec h_spec_implication).output input offset = c.output input offset := by
  rfl

@[circuit_norm] lemma weakenSpec_output'
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication
    (input : Var Input F) (offset : Nat) :
    ElaboratedCircuit.output (c.weakenSpec WeakerSpec h_spec_implication).main input offset = c.output input offset := by
  rfl

@[circuit_norm] lemma weakenSpec_channelsWithGuarantees
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).channelsWithGuarantees = c.channelsWithGuarantees := rfl

@[circuit_norm] lemma weakenSpec_channelsWithGuarantees'
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    ElaboratedCircuit.channelsWithGuarantees (c.weakenSpec WeakerSpec h_spec_implication).main = c.channelsWithGuarantees := rfl

@[circuit_norm] lemma weakenSpec_channelsWithRequirements
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).channelsWithRequirements = c.channelsWithRequirements := by
  simp only [weakenSpec]
end FormalCircuit

namespace GeneralFormalCircuit
/--
Weaken the specification of a GeneralFormalCircuit.
-/
def weakenSpec (circuit : GeneralFormalCircuit F Input Output)
    (WeakerSpec : Input F → Output F → ProverData F → Prop)
    (h_spec_implication : ∀ input output data,
      circuit.Spec input output data → WeakerSpec input output data) :
    GeneralFormalCircuit F Input Output where
  main := circuit.main
  elaborated := circuit.elaborated
  channelsWithRequirements := circuit.channelsWithRequirements
  requirementsChannelsLawful := circuit.requirementsChannelsLawful
  computableWitnesses := circuit.computableWitnesses
  Assumptions := circuit.Assumptions
  Spec := WeakerSpec
  ProverAssumptions := circuit.ProverAssumptions
  ProverSpec := circuit.ProverSpec
  soundness := by
    intro offset env input_var input h_eval h_assumptions h_holds
    have h_strong_spec := circuit.soundness offset env input_var input h_eval h_assumptions h_holds
    exact ⟨ h_spec_implication input _ _ h_strong_spec.1, h_strong_spec.2 ⟩
  completeness := circuit.completeness

@[circuit_norm]
lemma weakenSpec_assumptions (c : GeneralFormalCircuit F Input Output)
    (WeakerSpec : Input F → Output F → ProverData F → Prop)
    h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).Assumptions = c.Assumptions := by
  simp only [GeneralFormalCircuit.weakenSpec]
end GeneralFormalCircuit
