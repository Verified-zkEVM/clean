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
    (circuit1 : FormalCircuit order Input Mid)
    (circuit2 : FormalCircuit order Mid Output)
    (h_compat : ∀ checked input mid, circuit1.Assumptions input → circuit1.Spec checked input mid → circuit2.Assumptions mid)
    (h_localLength_stable : ∀ mid mid', circuit2.localLength mid = circuit2.localLength mid') :
    FormalCircuit order Input Output := {
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
    intros offset env yields checked input_var input h_eval h_assumptions h_hold
    simp only [Circuit.bind_def, circuit_norm] at h_hold
    rcases h_hold with ⟨ h_hold1, h_hold2 ⟩
    specialize h_hold1 (by simp_all)
    rcases h_hold1 with ⟨ h_hold1_yield, h_hold1_spec ⟩
    specialize h_compat _ _ _ (by simp_all) h_hold1_spec
    specialize h_hold2 h_compat
    rcases h_hold2 with ⟨ h_hold2_yield, h_hold2_spec ⟩
    constructor
    · intro s h_s
      simp only [circuit_norm] at h_s
      simp only [Nat.add_zero, Set.union_empty, Set.mem_union] at h_s
      cases h_s
      · apply h_hold1_yield
        rename_i h_s
        simp only [circuit_norm, FormalCircuit.toSubcircuit] at h_s
        assumption
      · apply h_hold2_yield
        rename_i h_s
        simp only [circuit_norm, FormalCircuit.toSubcircuit] at h_s
        assumption
    · exists (eval env (circuit1.elaborated.output input_var offset))
      aesop

  completeness := by
    simp only [circuit_norm]
    aesop
}

@[circuit_norm]
lemma FormalCircuit.concat_assumptions {F : Type} [Field F] {sentences : PropertySet F} {order : SentenceOrder sentences}
    {Input Mid Output : TypeMap} [ProvableType Input] [ProvableType Mid] [ProvableType Output]
    (c1 : FormalCircuit order Input Mid) (c2 : FormalCircuit order Mid Output) p0 p1 :
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
    (circuit : FormalCircuit order Input Output)
    (WeakerSpec : CheckedYields sentences → Input F → Output F → Prop)
    (h_spec_implication : ∀ checked input output,
      circuit.Assumptions input →
      circuit.Spec checked input output →
      WeakerSpec checked input output) :
    FormalCircuit order Input Output := {
  elaborated := circuit.elaborated
  Assumptions := circuit.Assumptions
  Spec := WeakerSpec
  soundness := by
    intro offset env yields checked input_var input h_eval h_assumptions h_holds
    -- Use the original circuit's soundness
    have ⟨h_yields, h_strong_spec⟩ := circuit.soundness offset env yields checked input_var input h_eval h_assumptions h_holds
    -- Apply the implication to get the weaker spec
    exact ⟨h_yields, h_spec_implication checked input _ h_assumptions h_strong_spec⟩
  completeness := by
    -- Completeness is preserved since we use the same elaborated circuit
    -- and the same assumptions
    intro offset env yields input_var h_env_completeness input h_eval h_assumptions
    exact circuit.completeness offset env yields input_var h_env_completeness input h_eval h_assumptions
}

@[circuit_norm]
lemma FormalCircuit.weakenSpec_assumptions {F : Type} [Field F] {sentences : PropertySet F} {order : SentenceOrder sentences}
    {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : FormalCircuit order Input Output) (WeakerSpec : CheckedYields sentences → Input F → Output F → Prop) h_spec_implication :
    (c.weakenSpec WeakerSpec h_spec_implication).Assumptions = c.Assumptions := by
  simp only [FormalCircuit.weakenSpec]
