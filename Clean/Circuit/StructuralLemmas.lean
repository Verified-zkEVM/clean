import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Theorems

/--
Concatenate two FormalCircuits into a single FormalCircuit.

This combinator requires:
- A compatibility proof that the first circuit's spec implies the second circuit's assumptions
- A proof that circuit1's output is independent of the offset (h_output_stable)

The composite circuit:
- Has the assumptions of the first circuit
- Has a spec stating that there exists an intermediate value such that both component specs hold
-/
def FormalCircuit.concat
    {F : Type} [Field F]
    {Input Mid Output : TypeMap} [ProvableType Input] [ProvableType Mid] [ProvableType Output]
    (circuit1 : FormalCircuit F Input Mid)
    (circuit2 : FormalCircuit F Mid Output)
    (h_compat : ∀ input mid, circuit1.Assumptions input → circuit1.Spec input mid → circuit2.Assumptions mid)
    (h_localLength_stable : ∀ mid mid', circuit2.localLength mid = circuit2.localLength mid') :
    FormalCircuit F Input Output := {
  elaborated := {
    main := (circuit1 · >>= circuit2)
    localLength input := circuit1.localLength input + circuit2.localLength (circuit1.output input 0)
    localLength_eq := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.localLength, circuit_norm]
      -- We need to show that circuit2.localLength at different offsets is the same
      -- This requires that circuit2.localLength is stable (doesn't depend on its input)
      congr 1
      apply h_localLength_stable
    output input offset :=
      circuit2.output (circuit1.output input offset) (offset + circuit1.localLength input)
    output_eq := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.output, circuit_norm]
    localAdds_eq := by
      intro input env offset
      simp [Circuit.bind_def, circuit_norm, Operations.collectAdds]
      constructor
      · rfl
      · rfl
  }
  Assumptions := circuit1.Assumptions
  Spec input output := ∃ mid, circuit1.Spec input mid ∧ circuit2.Spec mid output
  soundness := by
    simp only [Soundness]
    intros
    rename_i h_hold
    simp only [Circuit.bind_def, circuit_norm] at h_hold
    aesop
  completeness := by
    simp only [circuit_norm]
    aesop
}

@[circuit_norm]
lemma FormalCircuit.concat_assumptions {F Input Mid Output} [Field F] [ProvableType Input] [ProvableType Mid] [ProvableType Output]
    (c1 : FormalCircuit F Input Mid) (c2 : FormalCircuit F Mid Output) p0 p1 :
    (c1.concat c2 p0 p1).Assumptions = c1.Assumptions := by
  simp only [FormalCircuit.concat]

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
def FormalCircuit.weakenSpec
    {F : Type} [Field F]
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F Input Output)
    (WeakerSpec : Input F → Output F → Prop)
    (h_spec_implication : ∀ input output,
      circuit.Assumptions input →
      circuit.Spec input output →
      WeakerSpec input output) :
    FormalCircuit F Input Output := {
  elaborated := circuit.elaborated
  Assumptions := circuit.Assumptions
  Spec := WeakerSpec
  soundness := by
    intro offset env input_var input h_eval h_assumptions h_holds
    -- Use the original circuit's soundness
    have h_strong_spec := circuit.soundness offset env input_var input h_eval h_assumptions h_holds
    -- Apply the implication to get the weaker spec
    exact h_spec_implication input _ h_assumptions h_strong_spec
  completeness := by
    -- Completeness is preserved since we use the same elaborated circuit
    -- and the same assumptions
    exact circuit.completeness
}

@[circuit_norm]
lemma FormalCircuit.weakenSpec_assumptions {F Input Output} [Field F] [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit F Input Output) (WeakerSpec : Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).Assumptions = c.Assumptions := by
  simp only [FormalCircuit.weakenSpec]
