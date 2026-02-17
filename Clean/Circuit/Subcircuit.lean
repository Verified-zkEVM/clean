import Clean.Circuit.Basic
import Clean.Circuit.Theorems

variable {F : Type} [Field F]

namespace FlatOperation
open Circuit (ConstraintsHold.Completeness ConstraintsHold)

omit [Field F] in
lemma constraints_append {ops1 ops2 : List (FlatOperation F)} :
    constraints (ops1 ++ ops2) = constraints ops1 ++ constraints ops2 := by
  induction ops1 using FlatOperation.induct <;> simp_all [constraints]

omit [Field F] in
lemma lookups_append {ops1 ops2 : List (FlatOperation F)} :
    lookups (ops1 ++ ops2) = lookups ops1 ++ lookups ops2 := by
  induction ops1 using FlatOperation.induct <;> simp_all [lookups]

lemma constraints_toFlat {ops : Operations F} :
    constraints ops.toFlat = ops.constraints := by
  induction ops using Operations.induct <;>
    simp_all [Operations.toFlat, Operations.constraints, constraints, constraints_append]

lemma lookups_toFlat {ops : Operations F} :
    lookups ops.toFlat = ops.lookups := by
  induction ops using Operations.induct <;>
    simp_all [Operations.toFlat, Operations.lookups, lookups, lookups_append]

lemma interactions_toFlat {ops : Operations F} :
    interactions ops.toFlat = ops.interactions := by
  induction ops using Operations.induct <;>
    simp_all [Operations.toFlat, Operations.interactions, interactions, interactions_append]

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

lemma channelGuarantees_of_guarantees
  {env : Environment F} {ops : List (FlatOperation F)} {channel : RawChannel F} :
    FlatOperation.Guarantees env ops → FlatOperation.ChannelGuarantees channel env ops := by
  simp_all [circuit_norm]

lemma channelGuarantees_toFlat
  {env : Environment F} {ops : Operations F} {channel : RawChannel F} :
    FlatOperation.ChannelGuarantees channel env ops.toFlat ↔
    ops.ChannelGuarantees channel env := by
  simp_all [circuit_norm, interactions_toFlat]

lemma guarantees_toFlat {env : Environment F} {ops : Operations F} :
    FlatOperation.Guarantees env ops.toFlat ↔ ops.FullGuarantees env := by
  simp_all [guarantees_iff_forall_mem, Operations.FullGuarantees, interactions_toFlat]

lemma requirements_toFlat {env : Environment F} {ops : Operations F} :
    FlatOperation.Requirements env ops.toFlat ↔ ops.FullRequirements env := by
  simp_all [requirements_iff_forall_mem, Operations.FullRequirements, interactions_toFlat]

lemma inChannelsOrGuarantees_toFlat {env : Environment F} {ops : Operations F}
  {channels : List (RawChannel F)} :
    FlatOperation.InChannelsOrGuarantees channels env ops.toFlat ↔
    ops.InChannelsOrGuaranteesFull channels env := by
  simp_all [inChannelsOrGuarantees_iff_forall_mem, Operations.InChannelsOrGuaranteesFull,
    interactions_toFlat]

lemma inChannelsOrRequirements_toFlat {env : Environment F} {ops : Operations F}
  {channels : List (RawChannel F)} :
    FlatOperation.InChannelsOrRequirements channels env ops.toFlat ↔
    ops.InChannelsOrRequirementsFull channels env := by
  simp_all [inChannelsOrRequirements_iff_forall_mem, Operations.InChannelsOrRequirementsFull,
    interactions_toFlat]
end FlatOperation

@[circuit_norm]
lemma Operations.toNested_toFlat (ops : Operations F) {name : String} :
    (NestedOperations.nested ⟨ name, ops.toNested ⟩).toFlat = ops.toFlat := by
  induction ops using Operations.induct
  <;> simp_all [toNested, toFlat, NestedOperations.toFlat]

/--
Consistency theorem which proves that flattened constraints are equivalent to the
constraints created from the inductive `Operations` type, using flat constraints for subcircuits.
-/
theorem Circuit.constraintsHold_toFlat_iff {ops : Operations F} {env : Environment F} :
    ConstraintsHoldFlat env ops.toFlat ↔ ops.ConstraintsHold env := by
  simp only [FlatOperation.constraintsHoldFlat_iff_forall_mem, Operations.ConstraintsHold,
    FlatOperation.constraints_toFlat, FlatOperation.lookups_toFlat]

variable {α β: TypeMap} [ProvableType α] [ProvableType β]
variable [DecidableEq F]

section
open Circuit
open FlatOperation (constraintsHold_cons constraintsHold_append)

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
    ConstraintsHoldFlat env nestedOps.toFlat →
    FlatOperation.Guarantees env nestedOps.toFlat →
    ((circuit.Assumptions input → circuit.Spec input output) ∧
      FlatOperation.Requirements env nestedOps.toFlat) := by
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env input output h_holds _
    rw [ops.toNested_toFlat] at h_holds
    refine ⟨ ?_, ?_ ⟩

    -- by soundness of the circuit, the spec is satisfied if only the constraints hold
    · intro as
      suffices h: ConstraintsHold.Soundness env ops by
        exact circuit.soundness n env input_var input rfl as h

    -- so we just need to go from flattened constraints to constraints
      guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env ops.toFlat
      stop
      apply can_replace_soundness
      exact constraintsHold_toFlat_iff.mp h_holds
    · sorry

  have implied_by_completeness : ∀ env : Environment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.Assumptions (eval env input_var) →
      ConstraintsHoldFlat env nestedOps.toFlat ∧ FlatOperation.Guarantees env nestedOps.toFlat := by
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
    have h_holds_inter : ConstraintsHoldWithInteractions.Completeness env ops := by
      sorry

    -- so we just need to go from constraints to flattened constraints
    refine ⟨ ?_, ?_ ⟩
    · apply constraintsHold_toFlat_iff.mpr
      exact can_replace_completeness h_consistent h_env h_holds_inter
    · sorry

  {
    ops := nestedOps,
    Soundness env := circuit.Assumptions (eval env input_var) →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    Completeness env := circuit.Assumptions (eval env input_var),
    UsesLocalWitnesses env := circuit.Assumptions (eval env input_var) →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    localLength := circuit.localLength input_var

    imply_soundness := by
      intro env h_constraints h_guarantees
      exact imply_soundness env h_constraints h_guarantees
    implied_by_completeness
    imply_usesLocalWitnesses := by
      intro env h_env as
      -- by completeness, the constraints hold
      have h_holds := implied_by_completeness env h_env as
      -- by soundness, this implies the spec
      exact (imply_soundness env h_holds.1 h_holds.2).1 as

    localLength_eq := by
      rw [ops.toNested_toFlat, ←circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    guarantees_iff := sorry
    requirements_iff := sorry
    localAdds_eq := by sorry
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
      intro env h_holds _
      let input : β F := eval env input_var
      refine ⟨ ?_, ?_ ⟩
      · intro as
        rw [ops.toNested_toFlat] at h_holds

        -- by soundness of the circuit, the spec is satisfied if only the constraints hold
        suffices h: ConstraintsHold.Soundness env ops by
          exact circuit.soundness n env input_var input rfl as h

        -- so we just need to go from flattened constraints to constraints
        guard_hyp h_holds : FlatOperation.ConstraintsHoldFlat env ops.toFlat
        stop
        apply can_replace_soundness
        exact constraintsHold_toFlat_iff.mp h_holds
      · sorry

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
      have h_holds_inter : ConstraintsHoldWithInteractions.Completeness env ops := by
        sorry

      -- so we just need to go from constraints to flattened constraints
      refine ⟨ ?_, ?_ ⟩
      · apply constraintsHold_toFlat_iff.mpr
        exact can_replace_completeness h_consistent h_env h_holds_inter
      · sorry

    imply_usesLocalWitnesses := by intros; exact trivial

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    guarantees_iff := sorry
    requirements_iff := sorry
    localAdds_eq := by sorry
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
      ConstraintsHoldFlat env nestedOps.toFlat →
      FlatOperation.Guarantees env nestedOps.toFlat →
      (circuit.Spec input output env.data ∧ FlatOperation.Requirements env nestedOps.toFlat) := by
    intro env input output h_holds _
    rw [ops.toNested_toFlat] at h_holds
    refine ⟨ ?_, ?_ ⟩
    · apply circuit.soundness n env input_var input rfl
      stop
      apply can_replace_soundness
      exact constraintsHold_toFlat_iff.mp h_holds
    · sorry

  have implied_by_completeness : ∀ env : Environment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.Assumptions (eval env input_var) env.data →
      ConstraintsHoldFlat env nestedOps.toFlat ∧ FlatOperation.Guarantees env nestedOps.toFlat := by
    intro env h_env assumptions
    set input := eval env input_var
    rw [ops.toNested_toFlat] at h_env ⊢
    rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env
    rw [constraintsHold_toFlat_iff]
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    have h_holds := circuit.completeness n env input_var h_env_completeness input rfl assumptions
    have h_holds_inter : ConstraintsHoldWithInteractions.Completeness env ops := by
      sorry
    refine ⟨ ?_, ?_ ⟩
    · exact can_replace_completeness h_consistent h_env h_holds_inter
    · sorry

  {
    ops := nestedOps,
    Soundness env := circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data,
    Completeness env := circuit.Assumptions (eval env input_var) env.data,
    UsesLocalWitnesses env := circuit.Assumptions (eval env input_var) env.data →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data,
    localLength := circuit.localLength input_var

    imply_soundness := by
      intro env h_constraints h_guarantees
      exact imply_soundness env h_constraints h_guarantees
    implied_by_completeness
    imply_usesLocalWitnesses env h_env assumptions :=
      -- constraints hold by completeness, which implies the spec by soundness
      (implied_by_completeness env h_env assumptions |>
        fun h => imply_soundness env h.1 h.2).1

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    guarantees_iff := sorry
    requirements_iff := sorry
    localAdds_eq := by sorry
  }

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
      ConstraintsHoldFlat env nestedOps.toFlat →
      FlatOperation.Guarantees env nestedOps.toFlat →
      (circuit.Spec input output env ∧ FlatOperation.Requirements env nestedOps.toFlat) := by
    intro env input output h_holds h_guarantees
    rw [ops.toNested_toFlat] at *
    rw [constraintsHold_toFlat_iff] at h_holds
    rw [FlatOperation.guarantees_toFlat] at h_guarantees
    rw [FlatOperation.requirements_toFlat]
    have h_soundness_input : ConstraintsHoldWithInteractions.Soundness env ops :=
      can_replace_soundness h_holds h_guarantees
    have ⟨ h_spec, h_req ⟩ := circuit.soundness n env input_var input rfl h_soundness_input
    use h_spec
    exact requirements_toFlat_of_soundness h_holds h_guarantees h_req

  have implied_by_completeness : ∀ env : Environment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.Assumptions (eval env input_var) env →
      ConstraintsHoldFlat env nestedOps.toFlat ∧ FlatOperation.Guarantees env nestedOps.toFlat := by
    intro env h_env assumptions
    set input := eval env input_var
    rw [ops.toNested_toFlat] at h_env ⊢
    rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    have h_holds_inter := circuit.completeness n env input_var h_env_completeness input rfl assumptions
    rw [constraintsHold_toFlat_iff, FlatOperation.guarantees_toFlat]
    exact can_replace_completeness_and_guarantees h_consistent h_env h_holds_inter

  {
    ops := nestedOps,
    Soundness env := circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env,
    Completeness env := circuit.Assumptions (eval env input_var) env,
    UsesLocalWitnesses env := circuit.Assumptions (eval env input_var) env →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env,
    localLength := circuit.localLength input_var
    localAdds env := circuit.localAdds (eval env input_var) n env

    imply_soundness := by
      intro env h_constraints h_guarantees
      exact imply_soundness env h_constraints h_guarantees
    implied_by_completeness
    imply_usesLocalWitnesses env h_env assumptions :=
      -- constraints hold by completeness, which implies the spec by soundness
      (implied_by_completeness env h_env assumptions |>
        fun h => imply_soundness env h.1 h.2).1

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]
    localAdds_eq := by
      intro env
      rw [ops.toNested_toFlat, FlatOperation.localAdds_toFlat]
      -- TODO we need to switch from exact equality to .toFinsupp equality here,
      -- or in the other direction in circuit.localAdds_eq
      -- rw [← circuit.localAdds_eq]
      sorry

    channelsWithGuarantees := circuit.channelsWithGuarantees
    channelsWithRequirements := circuit.channelsWithRequirements

    guarantees_iff := by
      intro env
      rw [ops.toNested_toFlat, FlatOperation.inChannelsOrGuarantees_toFlat]
      apply in_channels_or_guarantees_full
    requirements_iff := by
      intro env
      rw [ops.toNested_toFlat, FlatOperation.inChannelsOrRequirements_toFlat]
      apply in_channels_or_requirements_full
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
