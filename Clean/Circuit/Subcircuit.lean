import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F : Type} [Field F] [DecidableEq F]

namespace FlatOperation
open Circuit (ConstraintsHold.Completeness ConstraintsHold)

lemma constraintsHold_cons : ∀ {op : FlatOperation F}, ∀ {ops : List (FlatOperation F)}, ∀ {env : Environment F},
    ConstraintsHoldFlat env (op :: ops) ↔ ConstraintsHoldFlat env [op] ∧ ConstraintsHoldFlat env ops := by
  intro op ops env
  constructor <;> (
    rintro h
    dsimp only [ConstraintsHoldFlat] at h
    split at h
    <;> simp_all only [ConstraintsHoldFlat, and_self])

lemma constraintsHold_append : ∀ {a b: List (FlatOperation F)}, ∀ {env : Environment F},
    ConstraintsHoldFlat env (a ++ b) ↔ ConstraintsHoldFlat env a ∧ ConstraintsHoldFlat env b := by
  intro a b env
  induction a with
  | nil => rw [List.nil_append]; tauto
  | cons op ops ih =>
    constructor
    · intro h
      rw [List.cons_append] at h
      obtain ⟨ h_op, h_rest ⟩ := constraintsHold_cons.mp h
      obtain ⟨ h_ops, h_b ⟩ := ih.mp h_rest
      exact ⟨ constraintsHold_cons.mpr ⟨ h_op, h_ops ⟩, h_b ⟩
    · rintro ⟨ h_a, h_b ⟩
      obtain ⟨ h_op, h_ops ⟩ := constraintsHold_cons.mp h_a
      have h_rest := ih.mpr ⟨ h_ops, h_b ⟩
      exact constraintsHold_cons.mpr ⟨ h_op, h_rest ⟩
end FlatOperation

@[circuit_norm]
lemma Operations.toNested_toFlat (ops : Operations F) {name : String} :
    (NestedOperations.nested ⟨ name, ops.toNested ⟩).toFlat = ops.toFlat := by
  induction ops using Operations.induct
  <;> simp_all [toNested, toFlat, NestedOperations.toFlat]

variable {α β: TypeMap} [ProvableType α] [ProvableType β]

section
open Circuit
open FlatOperation (constraintsHold_cons constraintsHold_append)

/--
Consistency theorem which proves that flattened constraints are equivalent to the
constraints created from the inductive `Operations` type, using flat constraints for subcircuits.
-/
theorem Circuit.constraintsHold_toFlat_iff : ∀ {ops : Operations F}, ∀ {env : Environment F},
    ConstraintsHoldFlat env ops.toFlat ↔ ConstraintsHold env ops := by
  intro ops env
  induction ops using Operations.induct with
  | empty => trivial
  -- we can handle all non-empty cases at once
  | witness | assert | lookup | subcircuit | interact =>
    dsimp only [Operations.toFlat]
    try rw [constraintsHold_cons]
    try rw [constraintsHold_append]
    simp_all only [ConstraintsHold, ConstraintsHoldFlat, and_true, true_and]

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def FormalCircuit.toSubcircuit (circuit : FormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have imply_soundness : ∀ env : Environment F,
    let input := eval env input_var
    let output := eval env (circuit.output input_var n)
    ConstraintsHoldFlat env nestedOps.toFlat → circuit.Assumptions input → circuit.Spec input output := by
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env input output h_holds (as : circuit.Assumptions input)
    rw [ops.toNested_toFlat] at h_holds
    show circuit.Spec input output

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    suffices h: ConstraintsHold.Soundness env ops by
      exact circuit.soundness n env input_var input rfl as h

    -- so we just need to go from flattened constraints to constraints
    guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env ops.toFlat
    apply can_replace_soundness
    exact constraintsHold_toFlat_iff.mp h_holds

  have implied_by_completeness : ∀ env : Environment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.Assumptions (eval env input_var) → ConstraintsHoldFlat env nestedOps.toFlat := by
    -- we are given that the assumptions are true
    intro env h_env
    let input := eval env input_var
    intro (as : circuit.Assumptions input)
    rw [ops.toNested_toFlat] at h_env ⊢

    have h_env : env.UsesLocalWitnesses n ops := by
      guard_hyp h_env : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n
      rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
      exact h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

    -- by completeness of the circuit, this means we can make the constraints hold
    have h_holds := circuit.completeness n env input_var h_env_completeness input rfl as

    -- so we just need to go from constraints to flattened constraints
    apply constraintsHold_toFlat_iff.mpr
    exact can_replace_completeness h_consistent h_env h_holds

  {
    ops := nestedOps,
    Soundness env := circuit.Assumptions (eval env input_var) →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    Completeness env := circuit.Assumptions (eval env input_var),
    UsesLocalWitnesses env := circuit.Assumptions (eval env input_var) →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    localLength := circuit.localLength input_var

    imply_soundness
    implied_by_completeness
    imply_usesLocalWitnesses := by
      intro env h_env as
      -- by completeness, the constraints hold
      have h_holds := implied_by_completeness env h_env as
      -- by soundness, this implies the spec
      exact imply_soundness env h_holds as

    localLength_eq := by
      rw [ops.toNested_toFlat, ←circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    guarantees_iff := sorry
    requirements_iff := sorry
  }

/--
Theorem and implementation that allows us to take a formal assertion and use it as a subcircuit.
-/
def FormalAssertion.toSubcircuit (circuit : FormalAssertion F β)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  {
    ops := nestedOps,
    Soundness env := circuit.Assumptions (eval env input_var) → circuit.Spec (eval env input_var),
    Completeness env := circuit.Assumptions (eval env input_var) ∧ circuit.Spec (eval env input_var),
    UsesLocalWitnesses _ := True,
    localLength := circuit.localLength input_var

    imply_soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env h_holds
      let input : β F := eval env input_var
      rintro (as : circuit.Assumptions input)
      show circuit.Spec input
      rw [ops.toNested_toFlat] at h_holds

      -- by soundness of the circuit, the spec is satisfied if only the constraints hold
      suffices h: ConstraintsHold.Soundness env ops by
        exact circuit.soundness n env input_var input rfl as h

      -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env ops.toFlat
      apply can_replace_soundness
      exact constraintsHold_toFlat_iff.mp h_holds

    implied_by_completeness := by
      -- we are given that the assumptions and the spec are true
      intro env h_env h_completeness

      let input := eval env input_var
      have as : circuit.Assumptions input ∧ circuit.Spec input := h_completeness
      rw [ops.toNested_toFlat] at h_env ⊢

      have h_env : env.UsesLocalWitnesses n ops := by
        guard_hyp h_env : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n
        rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
        exact h_env
      have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds := circuit.completeness n env input_var h_env_completeness input rfl as.left as.right

      -- so we just need to go from constraints to flattened constraints
      apply constraintsHold_toFlat_iff.mpr
      exact can_replace_completeness h_consistent h_env h_holds

    imply_usesLocalWitnesses := by intros; exact trivial

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    guarantees_iff := sorry
    requirements_iff := sorry
  }

/--
Theorem and implementation that allows us to take a formal circuit and use it as a subcircuit.
-/
def GeneralFormalCircuit.toSubcircuit (circuit : GeneralFormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have imply_soundness : ∀ env : Environment F,
      let input := eval env input_var
      let output := eval env (circuit.output input_var n)
      ConstraintsHoldFlat env nestedOps.toFlat → circuit.Spec input output env.data := by
    intro env input output h_holds
    rw [ops.toNested_toFlat] at h_holds
    apply circuit.soundness n env input_var input rfl
    apply can_replace_soundness
    exact constraintsHold_toFlat_iff.mp h_holds

  have implied_by_completeness : ∀ env : Environment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.Assumptions (eval env input_var) env.data → ConstraintsHoldFlat env nestedOps.toFlat := by
    intro env h_env assumptions
    set input := eval env input_var
    rw [ops.toNested_toFlat] at h_env ⊢
    rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env
    rw [constraintsHold_toFlat_iff]
    apply can_replace_completeness h_consistent h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    apply circuit.completeness n env input_var h_env_completeness input rfl assumptions

  {
    ops := nestedOps,
    Soundness env := circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data,
    Completeness env := circuit.Assumptions (eval env input_var) env.data,
    UsesLocalWitnesses env := circuit.Assumptions (eval env input_var) env.data →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data,
    localLength := circuit.localLength input_var

    imply_soundness
    implied_by_completeness
    imply_usesLocalWitnesses env h_env assumptions :=
      -- constraints hold by completeness, which implies the spec by soundness
      implied_by_completeness env h_env assumptions |> imply_soundness env

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    guarantees_iff := sorry
    requirements_iff := sorry
  }

lemma FlatOperation.channelGuarantees_of_guarantees
  {env : Environment F} {ops : List (FlatOperation F)} {channel : RawChannel F} :
    FlatOperation.Guarantees env ops → FlatOperation.ChannelGuarantees channel env ops := by
  induction ops using FlatOperation.induct <;> simp_all [circuit_norm]

lemma FlatOperation.channelGuarantees_toFlat_of_channelGuarantees
  {env : Environment F} {ops : Operations F} {channel : RawChannel F} :
    FlatOperation.ChannelGuarantees channel env ops.toFlat → ops.ChannelGuarantees channel env := by
  induction ops using Operations.induct <;> simp_all [circuit_norm, Operations.toFlat]

-- TODO this is not done, if we really decide to have a variant of constraints-hold with interactions,
-- then we need to change the Subcircuit structure to include them as well
def FormalCircuitWithInteractions.toSubcircuit (circuit : FormalCircuitWithInteractions F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have imply_soundness : ∀ env : Environment F,
      let input := eval env input_var
      let output := eval env (circuit.output input_var n)
      ConstraintsHoldFlat env nestedOps.toFlat → circuit.Spec input output env := by
    intro env input output h_holds
    rw [ops.toNested_toFlat] at h_holds
    -- TODO proper proofs here
    replace h_holds := constraintsHold_toFlat_iff.mp h_holds
    have h_holds_magic : ops.ConstraintsHold env :=
      by sorry
    have can_replace_soundness_magic :
      ops.ConstraintsHold env ↔
      ConstraintsHoldWithInteractions.Soundness env ops := by
      sorry
    have ⟨ h, _ ⟩ := circuit.soundness n env input_var input rfl (can_replace_soundness_magic.mp h_holds_magic)
    exact h

  have implied_by_completeness : ∀ env : Environment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.Assumptions (eval env input_var) env → ConstraintsHoldFlat env nestedOps.toFlat := by
    intro env h_env assumptions
    set input := eval env input_var
    rw [ops.toNested_toFlat] at h_env ⊢
    rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env
    rw [constraintsHold_toFlat_iff]
    apply can_replace_completeness h_consistent h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    stop
    apply circuit.completeness n env input_var h_env_completeness input rfl assumptions

  {
    ops := nestedOps,
    Soundness env := circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env,
    Completeness env := circuit.Assumptions (eval env input_var) env,
    UsesLocalWitnesses env := circuit.Assumptions (eval env input_var) env →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env,
    localLength := circuit.localLength input_var
    localAdds env := circuit.localAdds (eval env input_var) n env

    imply_soundness
    implied_by_completeness
    imply_usesLocalWitnesses env h_env assumptions :=
      -- constraints hold by completeness, which implies the spec by soundness
      implied_by_completeness env h_env assumptions |> imply_soundness env

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    channelsWithGuarantees := circuit.channelsWithGuarantees
    channelsWithRequirements := circuit.channelsWithRequirements

    guarantees_iff := by
      intro env
      -- one direction is trivial
      constructor
      · simp only [List.forall_iff_forall_mem]
        intro h_guarantees channel h_mem_channel
        apply FlatOperation.channelGuarantees_of_guarantees
        assumption
      have h_goal := circuit.guarantees_iff input_var n env
      rw [ops.toNested_toFlat] at *
      simp only [List.forall_iff_forall_mem] at *
      have h_ops : (circuit.main input_var).operations n = ops := rfl
      simp only [h_ops] at h_goal
      intro h_channel_guarantees_flat
      suffices h_full_guarantees : ops.FullGuarantees env by
        simp only [FlatOperation.Guarantees]
        rw [FlatOperation.forAll_toFlat_iff]
        exact h_full_guarantees
      generalize ops = ops at *
      clear imply_soundness implied_by_completeness h_consistent h_ops
      obtain ⟨ h_sublist, h_guarantees_iff ⟩ := h_goal
      have h_channel_guarantees : ∀ c ∈ circuit.channelsWithGuarantees, ops.ChannelGuarantees c env := by
        intro c h_mem
        apply FlatOperation.channelGuarantees_toFlat_of_channelGuarantees
        exact h_channel_guarantees_flat c h_mem
      rw [←h_guarantees_iff] at h_channel_guarantees
      clear h_guarantees_iff
      induction ops using Operations.induct with
      | empty => simp_all [circuit_norm]
      | witness | assert | lookup => simp_all [circuit_norm, Operations.toFlat]
      | interact i ops ih =>
        simp only [Operations.FullGuarantees, Operations.forAllNoOffset]
        show _ ∧ Operations.FullGuarantees env ops
        change _ ∧ Operations.Guarantees env ops at h_channel_guarantees
        simp_all [circuit_norm, Operations.toFlat]
      | subcircuit s ops ih =>
        simp only [Operations.FullGuarantees, Operations.forAllNoOffset]
        show _ ∧ Operations.FullGuarantees env ops
        rw [s.guarantees_iff env, List.forall_iff_forall_mem]
        have s_sublist : s.channelsWithGuarantees ⊆ circuit.channelsWithGuarantees := by
          simp_all [circuit_norm]
        have ops_sublist : ops.subcircuitChannelsWithGuarantees ⊆ circuit.channelsWithGuarantees := by
          simp_all [circuit_norm]
        simp only [Operations.toFlat, FlatOperation.ChannelGuarantees, FlatOperation.forAllNoOffset,
          List.forall_append] at h_channel_guarantees_flat
        change ∀ c ∈ circuit.channelsWithGuarantees,
          FlatOperation.ChannelGuarantees c env _ ∧ FlatOperation.ChannelGuarantees c env _
        at h_channel_guarantees_flat
        constructor
        · intro channel h_mem_channel
          have : channel ∈ circuit.channelsWithGuarantees := s_sublist h_mem_channel
          exact (h_channel_guarantees_flat channel this).left
        simp_all [circuit_norm]
    -- same proof as above, might want to extract common logic
    requirements_iff := by sorry
  }
end

/-- Include a subcircuit. -/
@[circuit_norm]
def subcircuit (circuit : FormalCircuit F β α) (b : Var β F) : Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

/-- Include an assertion subcircuit. -/
@[circuit_norm]
def assertion (circuit : FormalAssertion F β) (b : Var β F) : Circuit F Unit :=
  fun offset =>
    let subcircuit := circuit.toSubcircuit offset b
    ((), [.subcircuit subcircuit])

/-- Include a general subcircuit. -/
@[circuit_norm]
def subcircuitWithAssertion (circuit : GeneralFormalCircuit F β α) (b : Var β F) : Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

/-- Include an assertion changing multiset subcircuit. -/
@[circuit_norm]
def subcircuitWithInteractions (circuit : FormalCircuitWithInteractions F β α) (b : Var β F) : Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

-- we'd like to use subcircuits like functions

instance : CoeFun (FormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuit circuit input

instance : CoeFun (FormalAssertion F β) (fun _ => Var β F → Circuit F Unit) where
  coe circuit input := assertion circuit input

instance : CoeFun (GeneralFormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuitWithAssertion circuit input

instance : CoeFun (FormalCircuitWithInteractions F β α)
    (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuitWithInteractions circuit input

namespace Circuit
variable {α β: TypeMap} [ProvableType α] [ProvableType β]

/-- The local length of a subcircuit is derived from the original formal circuit -/
lemma subcircuit_localLength_eq (circuit : FormalCircuit F β α) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma assertion_localLength_eq (circuit : FormalAssertion F β) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma subcircuitWithAssertion_localLength_eq (circuit : GeneralFormalCircuit F β α) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl

lemma subcircuitWithInteractions_localLength_eq (circuit : FormalCircuitWithInteractions F β α) (input : Var β F) (offset : ℕ) :
  (circuit.toSubcircuit offset input).localLength = circuit.localLength input := rfl
end Circuit

-- subcircuit composability for `ComputableWitnesses`

namespace ElaboratedCircuit
/--
For formal circuits, to prove `ComputableWitnesses`, we assume that the input
only contains variables below the current offset `n`.
 -/
def ComputableWitnesses' (circuit : ElaboratedCircuit F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F),
    Environment.OnlyAccessedBelow n (eval · input) →
      (circuit.main input).ComputableWitnesses n

/--
This reformulation of `ComputableWitnesses'` is easier to prove in a formal circuit,
because we have all necessary assumptions at each circuit operation step.
 -/
def ComputableWitnesses (circuit : ElaboratedCircuit F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F) env env',
  circuit.main input |>.operations n |>.forAllFlat n {
    witness n _ compute :=
      env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env' }

/--
`ComputableWitnesses` is stronger than `ComputableWitnesses'` (so it's fine to only prove the former).
-/
lemma computableWitnesses_implies {circuit : ElaboratedCircuit F β α} :
    circuit.ComputableWitnesses → circuit.ComputableWitnesses' := by
  simp only [ComputableWitnesses, ComputableWitnesses']
  intro h_computable n input input_only_accesses_n env env'
  specialize h_computable n input env env'
  specialize input_only_accesses_n env env'
  simp only [Operations.ComputableWitnesses, ←Operations.forAll_toFlat_iff] at *
  generalize ((circuit.main input).operations n).toFlat = ops at *
  revert h_computable
  apply FlatOperation.forAll_implies
  simp only [Condition.implies, Condition.ignoreSubcircuit, imp_self]
  induction ops using FlatOperation.induct generalizing n with
  | empty => trivial
  | assert | lookup | interact => simp_all [FlatOperation.forAll]
  | witness m c ops ih =>
    simp_all only [FlatOperation.forAll, forall_const, implies_true, true_and]
    apply ih (m + n)
    intro h_agrees
    apply input_only_accesses_n
    exact Environment.agreesBelow_of_le h_agrees (by linarith)

/--
Composability for `ComputableWitnesses`: If
- in the parent circuit, we prove that input variables are < `n`,
- and the child circuit provides `ElaboratedCircuit.ComputableWitnesses`,
then we can conclude that the subcircuit, evaluated at this particular input,
satisfies `ComputableWitnesses` in the original sense.
-/
theorem compose_computableWitnesses (circuit : ElaboratedCircuit F β α) (input : Var β F) (n : ℕ) :
  Environment.OnlyAccessedBelow n (eval · input) ∧ circuit.ComputableWitnesses →
    (circuit.main input).ComputableWitnesses n := by
  intro ⟨ h_input, h_computable ⟩
  apply ElaboratedCircuit.computableWitnesses_implies h_computable
  exact h_input
end ElaboratedCircuit

theorem Circuit.subcircuit_computableWitnesses (circuit : FormalCircuit F β α) (input : Var β F) (n : ℕ) :
  Environment.OnlyAccessedBelow n (eval · input) ∧ circuit.ComputableWitnesses →
    (subcircuit circuit input).ComputableWitnesses n := by
  intro h env env'
  simp only [circuit_norm, FormalCircuit.toSubcircuit, Operations.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact circuit.compose_computableWitnesses input n h env env'

-- simplification of subcircuits in `circuit_norm`

section
variable {F : Type} [Field F] [DecidableEq F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
variable {env : Environment F} {input_var : Var Input F} {n : ℕ}

-- Simplification lemmas for toSubcircuit.localLength

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_localLength (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_localLength (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_localLength (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

@[circuit_norm]
theorem FormalCircuitWithInteractions.toSubcircuit_localLength
  (circuit : FormalCircuitWithInteractions F Input Output) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

-- Simplification lemmas for toSubcircuit.localAdds

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_localAdds (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localAdds env = 0 := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_localAdds (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localAdds env = 0 := rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_localAdds (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).localAdds env = 0 := rfl

@[circuit_norm]
theorem FormalCircuitWithInteractions.toSubcircuit_localAdds (circuit : FormalCircuitWithInteractions F Input Output) :
  (circuit.toSubcircuit n input_var).localAdds env = circuit.localAdds (eval env input_var) n env := rfl

-- Simplification lemmas for toSubcircuit.Soundness

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_soundness (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Soundness env =
  (circuit.Assumptions (eval env input_var) → circuit.Spec (eval env input_var) (eval env (circuit.output input_var n))) := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_soundness (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Soundness env =
  circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data := rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_soundness (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).Soundness env =
  (circuit.Assumptions (eval env input_var) → circuit.Spec (eval env input_var)) := rfl

@[circuit_norm]
theorem FormalCircuitWithInteractions.toSubcircuit_soundness (circuit : FormalCircuitWithInteractions F Input Output) :
  (circuit.toSubcircuit n input_var).Soundness env =
    circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env := rfl

-- Simplification lemmas for toSubcircuit.Completeness

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_completeness  (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Completeness env =
    circuit.Assumptions (eval env input_var) := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_completeness (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Completeness env =
    circuit.Assumptions (eval env input_var) env.data := rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_completeness (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).Completeness env =
    (circuit.Assumptions (eval env input_var) ∧ circuit.Spec (eval env input_var)) := rfl

@[circuit_norm]
theorem FormalCircuitWithInteractions.toSubcircuit_completeness (circuit : FormalCircuitWithInteractions F Input Output) :
  (circuit.toSubcircuit n input_var).Completeness env =
    circuit.Assumptions (eval env input_var) env := rfl

-- Simplification lemmas for toSubcircuit.UsesLocalWitnesses

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_usesLocalWitnesses (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).UsesLocalWitnesses env =
  (circuit.Assumptions (eval env input_var)
    → circuit.Spec (eval env input_var) (eval env (circuit.output input_var n))) := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_usesLocalWitnesses (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).UsesLocalWitnesses env =
  (circuit.Assumptions (eval env input_var) env.data →
    circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data) := rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_usesLocalWitnesses (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).UsesLocalWitnesses env = True := rfl

@[circuit_norm]
theorem FormalCircuitWithInteractions.toSubcircuit_usesLocalWitnesses
  (circuit : FormalCircuitWithInteractions F Input Output) :
  (circuit.toSubcircuit n input_var).UsesLocalWitnesses env =
  (circuit.Assumptions (eval env input_var) env →
    circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env) := rfl

-- Simplification lemmas for toSubcircuit channelsWithGuarantees and channelsWithRequirements

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_channelsWithGuarantees (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = [] := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_channelsWithGuarantees
  (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = [] := rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_channelsWithGuarantees (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = [] := rfl

@[circuit_norm]
theorem FormalCircuitWithInteractions.toSubcircuit_channelsWithGuarantees
  (circuit : FormalCircuitWithInteractions F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = circuit.channelsWithGuarantees := rfl

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_channelsWithRequirements (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = [] := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_channelsWithRequirements
  (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = [] := rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_channelsWithRequirements (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = [] := rfl

@[circuit_norm]
theorem FormalCircuitWithInteractions.toSubcircuit_channelsWithRequirements
  (circuit : FormalCircuitWithInteractions F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = circuit.channelsWithRequirements := rfl

end
