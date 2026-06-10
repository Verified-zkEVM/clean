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
    constructor <;> simp [explicit_circuit_norm]
    · intro a n m
      apply h_localLength_stable
  Assumptions := circuit1.Assumptions
  Spec input output := ∃ mid, circuit1.Spec input mid ∧ circuit2.Spec mid output
  soundness := by
    simp only [circuit_norm]
    aesop
  completeness := by
    simp only [circuit_norm]
    aesop

@[circuit_norm]
lemma concat_assumptions (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    (c1.concat c2 p0 p1).Assumptions = c1.Assumptions := by
  simp only [concat]

@[circuit_norm]
lemma concat_localLength (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 inp :
  (c1.concat c2 p0 p1).localLength inp =
    c1.localLength inp + c2.localLength (c1.output inp 0) := by
  simp only [concat, circuit_norm, id_eq]

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

@[circuit_norm]
lemma weakenSpec_assumptions
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).Assumptions = c.Assumptions := by
  simp only [weakenSpec]

@[circuit_norm]
lemma weakenSpec_channelsWithRequirements
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).channelsWithRequirements = c.channelsWithRequirements := by
  simp only [FormalCircuitBase.channelsWithRequirements, weakenSpec]
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
