import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Theorems

namespace Circuit

variable {F : Type} [Field F]
variable {Input Mid Output : TypeMap} [ProvableType Input] [ProvableType Mid] [ProvableType Output]

/--
Structural soundness lemma for elaborated circuits that consist of preparation followed by a subcircuit call.

This lemma allows proving soundness of a composite circuit by:
1. Proving that the preparation phase produces values that satisfy the subcircuit's assumptions
2. Proving that when the subcircuit's spec holds, it implies the overall circuit's spec

This is useful for circuits like BLAKE3's ApplyRounds where the main computation delegates to
a subcircuit (like Round) after some initial setup.
-/
theorem soundness_with_subcircuit
    (elaborated : ElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop)
    (Spec : Input F → Output F → Prop)
    (subcircuit : FormalCircuit F Mid Output)
    (prepare : Var Input F → Circuit F (Var Mid F))
    (h_main_eq : ∀ input, elaborated.main input = prepare input >>= fun mid => subcircuit mid)
    (h_output_eq : ∀ input offset, elaborated.output input offset =
      subcircuit.output ((prepare input).output offset) (offset + (prepare input).localLength offset))
    (h_spec_implication : ∀ input mid output,
      Assumptions input →
      subcircuit.Assumptions mid →
      subcircuit.Spec mid output →
      Spec input output)
    (h_prepare_spec : ∀ offset env input_var input,
      eval env input_var = input →
      Assumptions input →
      ConstraintsHold.Soundness env (prepare input_var |>.operations offset) →
      let mid := eval env (prepare input_var |>.output offset)
      subcircuit.Assumptions mid) :
    Soundness F elaborated Assumptions Spec := by
  intro offset env input_var input h_eval h_assumptions h_holds

  -- Rewrite using the main equation
  rw [h_main_eq] at h_holds
  simp only [Circuit.bind_def, circuit_norm] at h_holds

  -- Extract constraints for prepare and subcircuit
  obtain ⟨h_holds_prepare, h_holds_subcircuit⟩ := h_holds

  -- Get the intermediate values
  let mid_var := (prepare input_var).output offset
  let mid := eval env mid_var
  let prepare_len := (prepare input_var).localLength offset

  -- Prove the subcircuit assumptions hold
  have h_mid_assumptions : subcircuit.Assumptions mid := by
    apply h_prepare_spec offset env input_var input h_eval h_assumptions h_holds_prepare

  -- The subcircuit soundness gives us the spec
  simp only [subcircuit_norm, FormalCircuit.toSubcircuit] at h_holds_subcircuit

  -- Apply subcircuit soundness
  have h_subcircuit_spec : subcircuit.Spec mid (eval env (subcircuit.output mid_var (offset + prepare_len))) := by
    exact h_holds_subcircuit h_mid_assumptions

  -- Use the output equation
  rw [h_output_eq]

  -- Apply the spec implication
  apply h_spec_implication input mid _ h_assumptions h_mid_assumptions h_subcircuit_spec

/--
Structural soundness lemma for composing two FormalCircuits.

This lemma allows proving soundness of a composite circuit that consists of
two FormalCircuits executed in sequence, where:
1. The first circuit transforms Input to Mid
2. The second circuit transforms Mid to Output
3. The spec of the composite relates Input to Output

This is useful for circuits that naturally decompose into two sequential stages.
-/
theorem soundness_compose_circuits
    (elaborated : ElaboratedCircuit F Input Output)
    (Assumptions : Input F → Prop)
    (Spec : Input F → Output F → Prop)
    (circuit1 : FormalCircuit F Input Mid)
    (circuit2 : FormalCircuit F Mid Output)
    (h_main_eq : ∀ input, elaborated.main input = circuit1 input >>= circuit2)
    (h_output_eq : ∀ input offset, elaborated.output input offset =
      circuit2.output (circuit1.output input offset) (offset + circuit1.localLength input))
    (h_assumptions_implication : ∀ input,
      Assumptions input → circuit1.Assumptions input)
    (h_mid_assumptions : ∀ input mid,
      Assumptions input →
      circuit1.Spec input mid →
      circuit2.Assumptions mid)
    (h_spec_composition : ∀ input mid output,
      Assumptions input →
      circuit1.Spec input mid →
      circuit2.Spec mid output →
      Spec input output) :
    Soundness F elaborated Assumptions Spec := by
  intro offset env input_var input h_eval h_assumptions h_holds

  -- Rewrite using the main equation
  rw [h_main_eq] at h_holds
  simp only [Circuit.bind_def, circuit_norm] at h_holds

  -- Extract constraints for circuit1 and circuit2
  obtain ⟨h_holds_circuit1, h_holds_circuit2⟩ := h_holds

  -- Get intermediate values
  let mid_var := circuit1.output input_var offset
  let mid := eval env mid_var
  let circuit1_len := circuit1.localLength input_var

  -- Circuit1 assumptions hold
  have h_circuit1_assumptions : circuit1.Assumptions input := by
    apply h_assumptions_implication input h_assumptions

  -- Apply circuit1 soundness
  simp only [subcircuit_norm, FormalCircuit.toSubcircuit] at h_holds_circuit1
  have h_circuit1_spec : circuit1.Spec input mid := by
    have h_eq : eval env input_var = input := h_eval
    have h_mid_eq : eval env (circuit1.output input_var offset) = mid := rfl
    rw [h_eq, h_mid_eq] at h_holds_circuit1
    exact h_holds_circuit1 h_circuit1_assumptions

  -- Circuit2 assumptions hold
  have h_circuit2_assumptions : circuit2.Assumptions mid := by
    apply h_mid_assumptions input mid h_assumptions h_circuit1_spec

  -- Apply circuit2 soundness
  simp only [subcircuit_norm, FormalCircuit.toSubcircuit] at h_holds_circuit2
  have h_circuit2_spec : circuit2.Spec mid (eval env (circuit2.output mid_var (offset + circuit1_len))) := by
    exact h_holds_circuit2 h_circuit2_assumptions

  -- Use the output equation
  rw [h_output_eq]

  -- Apply the spec composition
  apply h_spec_composition input mid _ h_assumptions h_circuit1_spec h_circuit2_spec

/--
Concatenate two FormalCircuits into a single FormalCircuit.

This combinator requires:
- A compatibility proof that the first circuit's spec implies the second circuit's assumptions
- A proof that circuit1's output is independent of the offset (h_output_stable)

The composite circuit:
- Has the assumptions of the first circuit
- Has a spec stating that there exists an intermediate value such that both component specs hold

Note: The completeness proof is left as sorry due to complexity of witness generation.
-/
def FormalCircuit.concat
    (circuit1 : FormalCircuit F Input Mid)
    (circuit2 : FormalCircuit F Mid Output)
    (h_compat : ∀ input mid, circuit1.Assumptions input → circuit1.Spec input mid → circuit2.Assumptions mid)
    (h_localLength_stable : ∀ mid mid', circuit2.localLength mid = circuit2.localLength mid') :
    FormalCircuit F Input Output := {
  elaborated := {
    main := fun input => circuit1 input >>= circuit2
    localLength := fun input => circuit1.localLength input + circuit2.localLength (circuit1.output input 0)
    localLength_eq := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.localLength, circuit_norm]
      -- We need to show that circuit2.localLength at different offsets is the same
      -- This requires that circuit2.localLength is stable (doesn't depend on its input)
      congr 1
      apply h_localLength_stable
    output := fun input offset =>
      circuit2.output (circuit1.output input offset) (offset + circuit1.localLength input)
    output_eq := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.output, circuit_norm]
    subcircuitsConsistent := by
      intro input offset
      simp only [Circuit.bind_def, Circuit.operations, circuit_norm]
      ring
  }
  Assumptions := circuit1.Assumptions
  Spec := fun input output => ∃ mid, circuit1.Spec input mid ∧ circuit2.Spec mid output
  soundness := by
    apply soundness_compose_circuits (Mid := Mid)
    · intro; rfl
    · intro input offset
      simp only [ElaboratedCircuit.output]
    · intro input h; exact h
    · intro input mid h_assumptions h_spec1
      exact h_compat input mid h_assumptions h_spec1
    · intro input mid output h_input h_spec1 h_spec2
      exact ⟨mid, h_spec1, h_spec2⟩
  completeness := by
    simp only [circuit_norm]
    rintro offset env input_var ⟨ use1, use2 ⟩ input h_input asm1
    constructor
    · simp only [subcircuit_norm, h_input, asm1]
    · simp only [subcircuit_norm]
      apply h_compat
      · apply asm1
      · simp only [subcircuit_norm] at use1
        simp only [h_input] at use1
        apply use1
        assumption
}

/--
Weaken the specification of a FormalCircuit.

This combinator takes a FormalCircuit with a strong specification and produces
a new FormalCircuit with a weaker specification. This is useful when:
- You have a circuit that proves more than you need
- You want to compose circuits where the specs don't match exactly
- You need to adapt a specific circuit to a more general interface

The requirements are:
- The assumptions remain the same or can be strengthened
- The stronger spec implies the weaker spec
-/
def FormalCircuit.weakenSpec
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

end Circuit
