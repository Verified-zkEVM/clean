import Clean.Circuit.Formal
import Clean.Circuit.Theorems

variable {F : Type} [Field F]

namespace FlatOperation

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
  simp_all [circuit_norm]

lemma guarantees_toFlat {env : Environment F} {ops : Operations F} :
    FlatOperation.Guarantees env ops.toFlat ↔ ops.FullGuarantees env := by
  simp_all [guarantees_iff_forall_mem, Operations.FullGuarantees, circuit_norm]

lemma requirements_toFlat {env : Environment F} {ops : Operations F} :
    FlatOperation.Requirements env ops.toFlat ↔ ops.FullRequirements env := by
  simp_all [requirements_iff_forall_mem, Operations.FullRequirements, circuit_norm]

lemma inChannelsOrGuarantees_toFlat {env : Environment F} {ops : Operations F}
  {channels : List (RawChannel F)} :
    FlatOperation.InChannelsOrGuarantees channels env ops.toFlat ↔
    ops.InChannelsOrGuaranteesFull channels env := by
  simp_all [inChannelsOrGuarantees_iff_forall_mem, Operations.InChannelsOrGuaranteesFull,
    circuit_norm]

lemma inChannelsOrRequirements_toFlat {env : Environment F} {ops : Operations F}
  {channels : List (RawChannel F)} :
    FlatOperation.InChannelsOrRequirements channels env ops.toFlat ↔
    ops.InChannelsOrRequirementsFull channels env := by
  simp_all [inChannelsOrRequirements_iff_forall_mem, Operations.InChannelsOrRequirementsFull,
    circuit_norm]
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
    circuit_norm]

variable {α β: TypeMap} [ProvableType α] [ProvableType β]

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

  have soundness : ∀ env : Environment F,
    let input := eval env input_var
    let output := eval env (circuit.output input_var n)
    circuit.Assumptions input →
    ConstraintsHoldFlat env nestedOps.toFlat →
    FlatOperation.Guarantees env nestedOps.toFlat →
    circuit.Spec input output ∧ FlatOperation.Requirements env nestedOps.toFlat := by
    -- we are given an environment where the constraints hold, and can assume the assumptions are true
    intro env input output as h_holds h_guarantees
    rw [ops.toNested_toFlat] at h_holds
    rw [ops.toNested_toFlat, FlatOperation.guarantees_toFlat] at h_guarantees
    refine ⟨ ?_, ?_ ⟩
    · have h := can_replace_soundness (constraintsHold_toFlat_iff.mp h_holds) h_guarantees
      exact (circuit.soundness n env input_var input rfl as h).1
    · have h_nested : nestedOps.toFlat = ops.toFlat := by
        dsimp only [nestedOps]
        exact ops.toNested_toFlat
      rw [h_nested]
      rw [FlatOperation.requirements_toFlat]
      have h := can_replace_soundness (constraintsHold_toFlat_iff.mp h_holds) h_guarantees
      exact requirements_toFlat_of_soundness (circuit.subcircuitChannelsLawful input_var n)
        (constraintsHold_toFlat_iff.mp h_holds) h_guarantees
        (circuit.soundness n env input_var input rfl as h).2

  have completeness : ∀ env : ProverEnvironment F,
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
    have h_holds_inter := circuit.completeness n env input_var h_env_completeness input rfl as

    -- so we just need to go from constraints to flattened constraints
    refine ⟨ ?_, ?_ ⟩
    · apply constraintsHold_toFlat_iff.mpr
      exact can_replace_completeness h_consistent h_env h_holds_inter
    · rw [FlatOperation.guarantees_toFlat]
      exact can_replace_completeness_guarantees h_consistent h_env h_holds_inter

  {
    ops := nestedOps,
    Assumptions env := circuit.Assumptions (eval env input_var),
    Spec env := circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    ProverAssumptions env := circuit.Assumptions (eval env input_var),
    ProverSpec env := circuit.Assumptions (eval env input_var) →
      circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)),
    localLength := circuit.localLength input_var
    channelsWithGuarantees := circuit.channelsWithGuarantees
    channelsWithRequirements := circuit.channelsWithRequirements

    soundness := by
      intro env assumptions h_constraints h_guarantees
      exact soundness env assumptions h_constraints h_guarantees
    completeness := by
      intro env h_env
      use completeness env h_env
      intro as
      -- by completeness, the constraints hold
      have h_holds := completeness env h_env as
      -- by soundness, this implies the spec
      simp only [circuit_norm] at as ⊢
      exact (soundness env as h_holds.1 h_holds.2).1

    localLength_eq := by
      rw [ops.toNested_toFlat, ←circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

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
    Assumptions env := circuit.Assumptions (eval env input_var),
    Spec env := circuit.Spec (eval env input_var),
    ProverAssumptions env := circuit.Assumptions (eval env input_var) ∧ circuit.Spec (eval env input_var),
    ProverSpec _ := True,
    localLength := circuit.localLength input_var
    channelsWithGuarantees := circuit.channelsWithGuarantees
    channelsWithRequirements := circuit.channelsWithRequirements

    soundness := by
      -- we are given an environment where the constraints hold, and can assume the assumptions are true
      intro env as h_holds h_guarantees
      let input : β F := eval env input_var
      refine ⟨ ?_, ?_ ⟩
      · rw [ops.toNested_toFlat] at h_holds
        rw [ops.toNested_toFlat, FlatOperation.guarantees_toFlat] at h_guarantees

        -- by soundness of the circuit, the spec is satisfied if only the constraints hold
        have h := can_replace_soundness (constraintsHold_toFlat_iff.mp h_holds) h_guarantees
        exact (circuit.soundness n env input_var input rfl as h).1
      · rw [ops.toNested_toFlat] at h_holds
        rw [ops.toNested_toFlat, FlatOperation.guarantees_toFlat] at h_guarantees
        have h_nested : nestedOps.toFlat = ops.toFlat := by
          dsimp only [nestedOps]
          exact ops.toNested_toFlat
        rw [h_nested]
        rw [FlatOperation.requirements_toFlat]
        have h := can_replace_soundness (constraintsHold_toFlat_iff.mp h_holds) h_guarantees
        exact requirements_toFlat_of_soundness (circuit.subcircuitChannelsLawful input_var n)
          (constraintsHold_toFlat_iff.mp h_holds) h_guarantees
          (circuit.soundness n env input_var input rfl as h).2

    completeness := by
      -- we are given that the assumptions and the spec are true
      intro env h_env
      simp only [and_true]
      intro assumptions

      let input := eval env input_var
      have as : circuit.Assumptions input ∧ circuit.Spec input := assumptions
      rw [ops.toNested_toFlat] at h_env ⊢

      have h_env : env.UsesLocalWitnesses n ops := by
        guard_hyp h_env : env.ExtendsVector (FlatOperation.localWitnesses env ops.toFlat) n
        rw [env.usesLocalWitnesses_iff_flat, env.usesLocalWitnessesFlat_iff_extends]
        exact h_env
      have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env

      -- by completeness of the circuit, this means we can make the constraints hold
      have h_holds_inter := circuit.completeness n env input_var h_env_completeness input rfl as.left as.right

      -- so we just need to go from constraints to flattened constraints
      constructor
      · apply constraintsHold_toFlat_iff.mpr
        exact can_replace_completeness h_consistent h_env h_holds_inter
      · rw [FlatOperation.guarantees_toFlat]
        exact can_replace_completeness_guarantees h_consistent h_env h_holds_inter

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

  }

/--
Theorem and implementation that allows us to take a general formal circuit and use it as a subcircuit.
-/
def GeneralFormalCircuit.WithHint.toSubcircuit [CircuitType α] [CircuitType β]
    (circuit : GeneralFormalCircuit.WithHint F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  let ops := circuit.main input_var |>.operations n
  let nestedOps : NestedOperations F := .nested ⟨ circuit.name, ops.toNested ⟩
  have h_consistent : ops.SubcircuitsConsistent n := circuit.subcircuitsConsistent input_var n

  have soundness : ∀ env : Environment F,
      let input := eval env input_var
      let output := eval env (circuit.output input_var n)
      circuit.Assumptions input env.data →
      ConstraintsHoldFlat env nestedOps.toFlat →
      FlatOperation.Guarantees env nestedOps.toFlat →
      circuit.Spec input output env.data ∧ FlatOperation.Requirements env nestedOps.toFlat := by
    intro env input output assumptions constraints guarantees
    rw [ops.toNested_toFlat] at *
    refine ⟨ ?_, ?_ ⟩
    · rw [FlatOperation.guarantees_toFlat] at guarantees
      exact (circuit.soundness n env input_var input rfl assumptions
        (can_replace_soundness (constraintsHold_toFlat_iff.mp constraints) guarantees)).1
    · rw [FlatOperation.requirements_toFlat]
      rw [FlatOperation.guarantees_toFlat] at guarantees
      have h_soundness_input : ConstraintsHold.Soundness env ops :=
        can_replace_soundness (constraintsHold_toFlat_iff.mp constraints) guarantees
      have h_req := (circuit.soundness n env input_var input rfl assumptions h_soundness_input).2
      exact requirements_toFlat_of_soundness (circuit.subcircuitChannelsLawful input_var n)
        (constraintsHold_toFlat_iff.mp constraints) guarantees h_req

  have implied_by_assumptions : ∀ env : ProverEnvironment F,
      env.ExtendsVector (FlatOperation.localWitnesses env nestedOps.toFlat) n →
      circuit.ProverAssumptions (eval env input_var) env.data env.hint →

      ConstraintsHoldFlat env nestedOps.toFlat ∧ FlatOperation.Guarantees env nestedOps.toFlat := by
    intro env h_env assumptions
    set input := eval env input_var
    rw [ops.toNested_toFlat] at h_env ⊢
    rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env
    have h_env_completeness := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
    have h_holds_inter := (circuit.completeness n env input_var h_env_completeness input rfl assumptions).1
    rw [constraintsHold_toFlat_iff, FlatOperation.guarantees_toFlat]
    exact can_replace_completeness_and_guarantees h_consistent h_env h_holds_inter

  {
    ops := nestedOps,

    Assumptions env := circuit.Assumptions (eval env input_var) env.data,

    Spec env := circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data,

    ProverAssumptions env := circuit.ProverAssumptions (eval env input_var) env.data env.hint,

    ProverSpec env :=
      circuit.ProverAssumptions (eval env input_var) env.data env.hint →
      (circuit.Assumptions (eval env.toEnvironment input_var) env.data →
        circuit.Spec (eval env.toEnvironment input_var)
          (eval env.toEnvironment (circuit.output input_var n)) env.data)
      ∧ circuit.ProverSpec (eval env input_var) (eval env (circuit.output input_var n)) env.hint,

    localLength := circuit.localLength input_var

    soundness := by
      intro env assumptions h_constraints h_guarantees
      exact soundness env assumptions h_constraints h_guarantees
    completeness := by
      intro env h_env
      constructor
      · intro assumptions
        exact implied_by_assumptions env h_env assumptions
      -- constraints hold by completeness, which implies the spec by soundness
      intro assumptions
      have h_holds := implied_by_assumptions env h_env assumptions
      have h_env_completeness : env.UsesLocalWitnessesCompleteness n ops := by
        rw [ops.toNested_toFlat] at h_env
        rw [←env.usesLocalWitnessesFlat_iff_extends, ←env.usesLocalWitnesses_iff_flat] at h_env
        exact env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
      refine ⟨?_, (circuit.completeness n env input_var h_env_completeness _ rfl assumptions).2⟩
      intro verifier_assumptions
      exact (soundness env.toEnvironment verifier_assumptions h_holds.1 h_holds.2).1

    localLength_eq := by
      rw [ops.toNested_toFlat, ← circuit.localLength_eq input_var n,
        FlatOperation.localLength_toFlat]

    channelsWithGuarantees := circuit.channelsWithGuarantees
    channelsWithRequirements := circuit.channelsWithRequirements
  }

/--
Theorem and implementation that allows us to take a pure general formal circuit
and use it as a subcircuit. The implementation delegates to the hint-aware
variant through the default `ProvableType.toCircuitType` instance.
-/
def GeneralFormalCircuit.toSubcircuit (circuit : GeneralFormalCircuit F β α)
    (n : ℕ) (input_var : Var β F) : Subcircuit F n :=
  circuit.toWithHint.toSubcircuit n input_var
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
def subcircuitWithAssertion (circuit : GeneralFormalCircuit F β α) (b : Var β F) :
    Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

/-- Include a hint-aware general subcircuit. -/
@[circuit_norm]
def subcircuitWithHintAssertion [CircuitType α] [CircuitType β]
    (circuit : GeneralFormalCircuit.WithHint F β α) (b : Var β F) :
    Circuit F (Var α F) :=
  fun offset =>
    let a := circuit.output b offset
    let subcircuit := circuit.toSubcircuit offset b
    (a, [.subcircuit subcircuit])

-- we'd like to use subcircuits like functions

instance : CoeFun (FormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuit circuit input

instance : CoeFun (FormalAssertion F β) (fun _ => Var β F → Circuit F Unit) where
  coe circuit input := assertion circuit input

instance :
    CoeFun (GeneralFormalCircuit F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuitWithAssertion circuit input

instance [CircuitType α] [CircuitType β] :
    CoeFun (GeneralFormalCircuit.WithHint F β α) (fun _ => Var β F → Circuit F (Var α F)) where
  coe circuit input := subcircuitWithHintAssertion circuit input

-- subcircuit composability for `ComputableWitnesses`

namespace FormalCircuitBase
/--
For formal circuits, to prove `ComputableWitnesses`, we assume that the input
only contains variables below the current offset `n`.
 -/
def ComputableWitnesses' (circuit : FormalCircuitBase F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F),
    ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input) →
      (circuit.main input).ComputableWitnesses n

/--
This reformulation of `ComputableWitnesses'` is easier to prove in a formal circuit,
because we have all necessary assumptions at each circuit operation step.
 -/
def ComputableWitnesses (circuit : FormalCircuitBase F β α) : Prop :=
  ∀ (n : ℕ) (input : Var β F) (env env' : ProverEnvironment F),
  circuit.main input |>.operations n |>.forAllFlat n {
    witness n _ compute :=
      env.AgreesBelow n env' → eval env input = eval env' input → compute env = compute env' }

/--
`ComputableWitnesses` is stronger than `ComputableWitnesses'` (so it's fine to only prove the former).
-/
lemma computableWitnesses_implies {circuit : FormalCircuitBase F β α} :
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
    exact ProverEnvironment.agreesBelow_of_le h_agrees (by linarith)

/--
Composability for `ComputableWitnesses`: If
- in the parent circuit, we prove that input variables are < `n`,
- and the child circuit provides `ElaboratedCircuit.ComputableWitnesses`,
then we can conclude that the subcircuit, evaluated at this particular input,
satisfies `ComputableWitnesses` in the original sense.
-/
theorem compose_computableWitnesses (circuit : FormalCircuitBase F β α) (input : Var β F) (n : ℕ) :
  ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input) ∧ circuit.ComputableWitnesses →
    (circuit.main input).ComputableWitnesses n := by
  intro ⟨ h_input, h_computable ⟩
  apply FormalCircuitBase.computableWitnesses_implies h_computable
  exact h_input
end FormalCircuitBase

theorem Circuit.subcircuit_computableWitnesses (circuit : FormalCircuit F β α)
    (input : Var β F) (n : ℕ) :
  ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input) ∧ circuit.ComputableWitnesses →
    (subcircuit circuit input).ComputableWitnesses n := by
  intro h env env'
  simp only [circuit_norm, FormalCircuit.toSubcircuit, Operations.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact circuit.compose_computableWitnesses input n h env env'

-- simplification of subcircuits in `circuit_norm`

section
variable {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
variable {env : Environment F} {env_p : ProverEnvironment F} {input_var : Var Input F} {n : ℕ}

-- Simplification lemmas for toSubcircuit.localLength

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_localLength (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_localLength (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

/--
Simplifies localLength for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_localLength
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := by
  rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_localLength (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

-- Simplification lemmas for toSubcircuit.Soundness

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_assumptions (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Assumptions env =
    circuit.Assumptions (eval env input_var) := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_assumptions (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Assumptions env =
    circuit.Assumptions (eval env input_var) env.data := by
  simp [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_assumptions
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) (env : Environment F) :
    (circuit.toSubcircuit n input_var).Assumptions env =
    circuit.Assumptions (eval env input_var) env.data := by
  rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_assumptions (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).Assumptions env =
    circuit.Assumptions (eval env input_var) := rfl

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_soundness (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Spec env =
    circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_soundness (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).Spec env =
    circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data := by
  simp [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]

/--
Simplifies Soundness for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_soundness
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) (env : Environment F) :
    (circuit.toSubcircuit n input_var).Spec env =
    circuit.Spec (eval env input_var) (eval env (circuit.output input_var n)) env.data := by
  rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_soundness (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).Spec env =
    circuit.Spec (eval env input_var) := rfl

-- Simplification lemmas for toSubcircuit.Completeness

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_completeness  (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).ProverAssumptions env_p =
    circuit.Assumptions (eval env_p input_var) := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_completeness (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).ProverAssumptions env_p =
    circuit.ProverAssumptions (eval env_p input_var) env_p.data env_p.hint := by
  simp [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]

/--
Simplifies Completeness for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_completeness
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) (env : ProverEnvironment F) :
    (circuit.toSubcircuit n input_var).ProverAssumptions env =
    circuit.ProverAssumptions (eval env input_var) env.data env.hint := by
  rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_completeness (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).ProverAssumptions env_p =
    (circuit.Assumptions (eval env_p input_var) ∧ circuit.Spec (eval env_p input_var)) := rfl

-- Simplification lemmas for toSubcircuit.UsesLocalWitnesses

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_usesLocalWitnesses (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).ProverSpec env_p =
  (circuit.Assumptions (eval env_p input_var)
    → circuit.Spec (eval env_p input_var) (eval env_p (circuit.output input_var n))) := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_usesLocalWitnesses (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).ProverSpec env_p =
  (circuit.ProverAssumptions (eval env_p input_var) env_p.data env_p.hint →
    (circuit.Assumptions (eval env_p.toEnvironment input_var) env_p.data →
      circuit.Spec (eval env_p.toEnvironment input_var)
        (eval env_p.toEnvironment (circuit.output input_var n)) env_p.data) ∧
    circuit.ProverSpec (eval env_p input_var) (eval env_p (circuit.output input_var n)) env_p.hint) := by
  simp [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]

/--
Simplifies ProverSpec for GeneralFormalCircuit.WithHint.toSubcircuit to avoid unfolding the entire subcircuit structure.
-/
@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_usesLocalWitnesses
    {F : Type} [Field F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (n : ℕ)
    (input_var : Var Input F) (env : ProverEnvironment F) :
  (circuit.toSubcircuit n input_var).ProverSpec env =
  (circuit.ProverAssumptions (eval env input_var) env.data env.hint →
    (circuit.Assumptions (eval env.toEnvironment input_var) env.data →
      circuit.Spec (eval env.toEnvironment input_var)
        (eval env.toEnvironment (circuit.output input_var n)) env.data) ∧
    circuit.ProverSpec (eval env input_var) (eval env (circuit.output input_var n)) env.hint) := by
  rfl

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_usesLocalWitnesses (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).ProverSpec env_p = True := rfl

-- Simplification lemmas for toSubcircuit channelsWithGuarantees and channelsWithRequirements

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_channelsWithGuarantees (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = circuit.channelsWithGuarantees := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_channelsWithGuarantees
  (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = circuit.channelsWithGuarantees := by
  simp [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_channelsWithGuarantees (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = circuit.channelsWithGuarantees := rfl

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_channelsWithRequirements (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = circuit.channelsWithRequirements := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_channelsWithRequirements
  (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = circuit.channelsWithRequirements := by
  simp [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_channelsWithRequirements (circuit : FormalAssertion F Input) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = circuit.channelsWithRequirements := rfl

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_channelsLawful
    (circuit : FormalCircuit F Input Output) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  constructor
  · intro env
    simp only [FormalCircuit.toSubcircuit]
    rw [Operations.toNested_toFlat, FlatOperation.inChannelsOrGuarantees_toFlat]
    exact circuit.in_channels_or_guarantees_full input_var n env
  constructor
  · intro env
    simp only [FormalCircuit.toSubcircuit]
    rw [Operations.toNested_toFlat, FlatOperation.inChannelsOrRequirements_toFlat]
    exact circuit.in_channels_or_requirements_full input_var n env
  · simp only [FormalCircuit.toSubcircuit]
    rw [Operations.toNested_toFlat, Operations.channels_toFlat]
    exact circuit.channels_subset input_var n

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_channelsLawful
    (circuit : FormalAssertion F Input) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  constructor
  · intro env
    simp only [FormalAssertion.toSubcircuit]
    rw [Operations.toNested_toFlat, FlatOperation.inChannelsOrGuarantees_toFlat]
    exact circuit.in_channels_or_guarantees_full input_var n env
  constructor
  · intro env
    simp only [FormalAssertion.toSubcircuit]
    rw [Operations.toNested_toFlat, FlatOperation.inChannelsOrRequirements_toFlat]
    exact circuit.in_channels_or_requirements_full input_var n env
  · simp only [FormalAssertion.toSubcircuit]
    rw [Operations.toNested_toFlat, Operations.channels_toFlat]
    exact circuit.channels_subset input_var n

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_channelsLawful
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  constructor
  · intro env
    simp only [GeneralFormalCircuit.WithHint.toSubcircuit]
    rw [Operations.toNested_toFlat, FlatOperation.inChannelsOrGuarantees_toFlat]
    exact circuit.in_channels_or_guarantees_full input_var n env
  constructor
  · intro env
    simp only [GeneralFormalCircuit.WithHint.toSubcircuit]
    rw [Operations.toNested_toFlat, FlatOperation.inChannelsOrRequirements_toFlat]
    exact circuit.in_channels_or_requirements_full input_var n env
  · simp only [GeneralFormalCircuit.WithHint.toSubcircuit]
    rw [Operations.toNested_toFlat, Operations.channels_toFlat]
    have shallowChannels_subset := circuit.mem_channelsWithGuarantees_or_mem_channelsWithRequirements_of_mem_shallowChannels input_var n
    have channelsWithGuarantees_subset := circuit.subcircuitChannelsWithGuarantees_subset_channelsWithGuarantees input_var n
    have channelsWithRequirements_subset := circuit.subcircuitChannelsWithRequirements_subset_channelsWithRequirements input_var n
    simp only at *
    set ops := (circuit.main input_var).operations n
    trans ops.shallowChannels ++ ops.subcircuitChannelsWithGuarantees ++ ops.subcircuitChannelsWithRequirements
    · apply Operations.channels_subset
      exact circuit.subcircuitChannelsLawful input_var n
    · simp_all only [List.append_assoc, List.append_subset, List.subset_append_of_subset_left,
        List.subset_append_of_subset_right, and_self, and_true]
      simp only [List.subset_def, List.mem_append]
      tauto

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_channelsLawful
    (circuit : GeneralFormalCircuit F Input Output) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  exact GeneralFormalCircuit.WithHint.toSubcircuit_channelsLawful circuit.toWithHint input_var

attribute [explicit_circuit_no_unfold] subcircuit assertion subcircuitWithAssertion subcircuitWithHintAssertion

namespace ExplicitCircuit
-- TODO AUTOELAB the other subcircuit types below (`assertion`, `subcircuitWithAssertion`,
-- `subcircuitWithHintAssertion`) are still picked up via `infer_instance`; probably worth
-- tagging them `@[explicit_circuit_constructor]` too so they go through head dispatch.
@[explicit_circuit_constructor]
instance fromSubcircuit (circuit : FormalCircuit F Input Output) (input : Var Input F) :
    ExplicitCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
  channelsWithRequirements _ := circuit.channelsWithRequirements
  subcircuitsConsistent n := by
    change Operations.SubcircuitsConsistent n [.subcircuit (_)]
    simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    exact ⟨trivial, trivial⟩
  channelsLawful := by simp [circuit_norm]

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuit_output {circuit : FormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuit circuit input).output n = circuit.output input n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuit_localLength {circuit : FormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuit circuit input).localLength n = circuit.localLength input := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuit_operations {circuit : FormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuit circuit input).operations n = [.subcircuit (circuit.toSubcircuit n input)] := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuit_channelsWithGuarantees {circuit : FormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuit circuit input).channelsWithGuarantees n = circuit.channelsWithGuarantees := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuit_channelsWithRequirements {circuit : FormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuit circuit input).channelsWithRequirements n = circuit.channelsWithRequirements := rfl
end ExplicitCircuit

instance {β : TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ExplicitCircuit (assertion circuit input) where
  output n := ()
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
  channelsWithRequirements _ := circuit.channelsWithRequirements
  subcircuitsConsistent n := by
    change Operations.SubcircuitsConsistent n [.subcircuit (_)]
    simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    exact ⟨trivial, trivial⟩

instance {β α: TypeMap} [ProvableType α] [ProvableType β]
    {circuit : GeneralFormalCircuit F β α} {input} :
    ExplicitCircuit (subcircuitWithAssertion circuit input) where
  output n := circuit.output input n
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
  channelsWithRequirements _ := circuit.channelsWithRequirements
  subcircuitsConsistent n := by
    change Operations.SubcircuitsConsistent n [.subcircuit (_)]
    simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    exact ⟨trivial, trivial⟩

instance {β α: TypeMap} [CircuitType α] [CircuitType β]
    {circuit : GeneralFormalCircuit.WithHint F β α} {input} :
    ExplicitCircuit (subcircuitWithHintAssertion circuit input) where
  output n := circuit.output input n
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
  channelsWithRequirements _ := circuit.channelsWithRequirements
  subcircuitsConsistent n := by
    change Operations.SubcircuitsConsistent n [.subcircuit (_)]
    simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    exact ⟨trivial, trivial⟩

-- simplification lemmas for FlatOperations.interactions (toSubcircuit ..).ops.toFlat

theorem FormalCircuit.toSubcircuit_interactions (circuit : FormalCircuit F Input Output) :
  FlatOperation.interactions (circuit.toSubcircuit n input_var).ops.toFlat =
    (circuit.main input_var |>.operations n |>.interactions) := by
  simp only [FormalCircuit.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.interactions_toFlat]

theorem GeneralFormalCircuit.toSubcircuit_interactions
    (circuit : GeneralFormalCircuit F Input Output) :
  FlatOperation.interactions (circuit.toSubcircuit n input_var).ops.toFlat =
    (circuit.main input_var |>.operations n |>.interactions) := by
  simp only [GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.interactions_toFlat]

theorem FormalAssertion.toSubcircuit_interactions (circuit : FormalAssertion F Input) :
  FlatOperation.interactions (circuit.toSubcircuit n input_var).ops.toFlat =
    (circuit.main input_var |>.operations n |>.interactions) := by
  simp only [FormalAssertion.toSubcircuit]
  rw [Operations.toNested_toFlat, Operations.interactions_toFlat]

end
