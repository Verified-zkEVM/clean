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
    {F : Type} [Field F] {sentences : PropertySet F} {order : SentenceOrder sentences}
    {Input Mid Output : TypeMap} [ProvableType Input] [ProvableType Mid] [ProvableType Output]
    (circuit1 : FormalCircuit F sentences order Input Mid)
    (circuit2 : FormalCircuit F sentences order Mid Output)
    (h_compat : ∀ checked input mid, circuit1.Assumptions input → circuit1.Spec checked input mid → circuit2.Assumptions mid)
    (h_localLength_stable : ∀ mid mid', circuit2.localLength mid = circuit2.localLength mid') :
    FormalCircuit F sentences order Input Output := {
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
  }
  Assumptions := circuit1.Assumptions
  Spec checked input output := ∃ mid, circuit1.Spec checked input mid ∧ circuit2.Spec checked mid output
  soundness := by
    simp only [Soundness]
    intros
    rename_i h_hold
    simp only [Circuit.bind_def, circuit_norm] at h_hold
    aesop
  completeness := by
    simp only [circuit_norm]
    aesop
  spec_monotonic := by
    rintro checked₁ checked₂ input output h_sub ⟨mid, h1, h2⟩
    use mid
    exact ⟨circuit1.spec_monotonic _ _ _ _ h_sub h1, circuit2.spec_monotonic _ _ _ _ h_sub h2⟩
}

@[circuit_norm]
lemma FormalCircuit.concat_assumptions {F : Type} [Field F] {sentences : PropertySet F} {order : SentenceOrder sentences}
    {Input Mid Output : TypeMap} [ProvableType Input] [ProvableType Mid] [ProvableType Output]
    (c1 : FormalCircuit F sentences order Input Mid) (c2 : FormalCircuit F sentences order Mid Output) p0 p1 :
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
    {F : Type} [Field F] {sentences : PropertySet F} {order : SentenceOrder sentences}
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit F sentences order Input Output)
    (WeakerSpec : CheckedYields sentences → Input F → Output F → Prop)
    (h_spec_implication : ∀ checked input output,
      circuit.Assumptions input →
      circuit.Spec checked input output →
      WeakerSpec checked input output)
    (h_weaker_spec_monotonic : ∀ (checked₁ checked₂ : CheckedYields sentences) (input : Input F) (output : Output F),
      checked₁ ⊆ checked₂ → WeakerSpec checked₂ input output → WeakerSpec checked₁ input output) :
    FormalCircuit F sentences order Input Output := {
  elaborated := circuit.elaborated
  Assumptions := circuit.Assumptions
  Spec := WeakerSpec
  soundness := by
    intro offset env yields checked input_var input h_eval h_assumptions h_holds
    -- Use the original circuit's soundness
    have h_strong_spec := circuit.soundness offset env yields checked input_var input h_eval h_assumptions h_holds
    -- Apply the implication to get the weaker spec
    exact h_spec_implication checked input _ h_assumptions h_strong_spec
  completeness := by
    -- Completeness is preserved since we use the same elaborated circuit
    -- and the same assumptions
    intro offset env yields input_var h_env_completeness input h_eval h_assumptions
    exact circuit.completeness offset env yields input_var h_env_completeness input h_eval h_assumptions
  spec_monotonic := by
    intros checked₁ checked₂ input output h_sub h_orig
    exact h_weaker_spec_monotonic checked₁ checked₂ input output h_sub h_orig
}

@[circuit_norm]
lemma FormalCircuit.weakenSpec_assumptions {F : Type} [Field F] {sentences : PropertySet F} {order : SentenceOrder sentences}
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit F sentences order Input Output) (WeakerSpec : CheckedYields sentences → Input F → Output F → Prop) h_spec_implication h_weaker_spec_monotonic :
    (c.weakenSpec WeakerSpec h_spec_implication h_weaker_spec_monotonic).Assumptions = c.Assumptions := by
  simp only [FormalCircuit.weakenSpec]
