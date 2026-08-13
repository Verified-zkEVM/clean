import Clean.Circuit.Formal
import Clean.Circuit.Theorems

variable {F : Type} [FiniteField F]

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

lemma shallowConstraints_of_constraintsHoldFlat {env : Environment F} {ops : Operations F} :
    ConstraintsHoldFlat env ops.toFlat → ConstraintsHold.Shallow env ops := by
  intro h_constraints
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem,
    Operations.constraints_toFlat, Operations.lookups_toFlat,
    Operations.forall_constraints_iff, Operations.forall_lookups_iff] at h_constraints
  rw [constraintsHold_shallow_iff_forall_mem]
  constructor
  · exact h_constraints.1.1
  · intro l h_mem
    exact l.table.imply_soundness _ _ (h_constraints.2.1 l h_mem)
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
      exact circuit.soundness n env input_var input rfl as h |>.1
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
      have h := can_replace_soundness (constraintsHold_toFlat_iff.mp constraints) guarantees
      exact circuit.soundness n env input_var input rfl assumptions h |>.1
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

/--
Bridge from the plain (`input_eq`) computability of a flat op list to the `OnlyAccessedBelow` form:
each witness carries its own `AgreesBelow n'` guard, which is enough to obtain `P` from `h` and
then read off that witness's agreement from the plain statement.
-/
lemma FlatOperation.forAll_agree_of_imp {F} [FiniteField F] {P : Prop}
    (env env' : ProverEnvironment F) (ops : List (FlatOperation F)) :
    ∀ n, (P → FlatOperation.forAll n { witness n' _ c := env.AgreesBelow n' env' → c.eval env = c.eval env' } ops) →
    (env.AgreesBelow n env' → P) →
    FlatOperation.forAll n { witness n' _ c := env.AgreesBelow n' env' → c.eval env = c.eval env' } ops := by
  induction ops with
  | nil => intro n _ _; trivial
  | cons op ops ih =>
    intro n h_src h
    rw [FlatOperation.forAll_cons]
    refine ⟨?_, ?_⟩
    · cases op with
      | witness m c => intro h_agrees; exact (FlatOperation.forAll_cons.mp (h_src (h h_agrees))).1 h_agrees
      | assert e | lookup l | interact i => simp [Condition.applyFlat]
    · exact ih (n + op.singleLocalLength)
        (fun hP => (FlatOperation.forAll_cons.mp (h_src hP)).2)
        (fun h_agrees => h (ProverEnvironment.agreesBelow_of_le h_agrees (Nat.le_add_right n op.singleLocalLength)))

/-- A uniform premise commutes out of the `ComputableWitnesses` conditions: obligations
whose conditions all carry the same hypothesis (e.g. the parent's input equality) follow
from the premise-free obligation. Used when a parent inlines a child circuit's `main`, so
the child's operations appear in the parent's obligation directly. -/
theorem Operations.computableWitnesses_of_premise {F : Type} [FiniteField F] {P : Prop}
    {n : ℕ} {ops : Operations F} {env env' : ProverEnvironment F}
    (h : P → ops.ComputableWitnesses n env env') :
    ops.forAll n {
      witness := fun n' _ compute => P → env.AgreesBelow n' env' →
        compute.eval env = compute.eval env'
      subcircuit := fun n' _ s => P → s.ComputableWitnesses n' env env' } := by
  simp only [Operations.ComputableWitnesses] at h
  induction ops generalizing n with
  | nil => trivial
  | cons op ops ih =>
    rw [Operations.forAll_cons]
    refine ⟨?_, ih fun hp => (Operations.forAll_cons.mp (h hp)).2⟩
    cases op <;> simp only [Condition.apply] <;> intro hp <;>
      simpa [Condition.apply] using (Operations.forAll_cons.mp (h hp)).1

namespace FormalCircuitBase
variable {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]

/-
Composability for `ComputableWitnesses`:
- If in the parent circuit, we prove that input variables are < `n`,
- and since the child circuit provides `FormalCircuitBase.ComputableWitnesses`,
we can conclude that the subcircuit, evaluated at this particular input,
satisfies `ComputableWitnesses` in the original sense.
-/
def ComputableWitnesses' (circuit : FormalCircuitBase F Input Output) [ElaboratedCircuit F Input Output circuit.main] : Prop :=
  ∀ {n : ℕ} {input : Var Input F} {env env' : ProverEnvironment F},
    eval env input = eval env' input →
      -- the witnesses are computable from input agreement
      (circuit.main input).ComputableWitnesses n env env' ∧
      -- and a similar conclusion holds for the output, made up of input and this circuit's witnesses
      (env.AgreesBelow (n + circuit.localLength input) env' →
        eval env (circuit.output input n) = eval env' (circuit.output input n))
/--
`ComputableWitnesses` is stronger than `ComputableWitnesses'` (so it's fine to only prove the former).
-/
lemma computableWitnesses' {circuit : FormalCircuitBase F Input Output} [ElaboratedCircuit F Input Output circuit.main] :
    circuit.ComputableWitnesses' := by
  intro n input env env' input_eq
  exact circuit.computableWitnesses n input env env' input_eq

/--
`OnlyAccessedBelow`-flavored companion to `computableWitnesses'`: the witnesses are computable
whenever the input is only accessed below `n`. Proved from the plain form by the flat transport
(`FlatOperation.forAll_agree_of_imp`), so the per-formal-circuit lemmas stay one-liners.
-/
lemma computableWitnesses'_onlyAccessedBelow {circuit : FormalCircuitBase F Input Output}
    [ElaboratedCircuit F Input Output circuit.main]
    {n : ℕ} {input : Var Input F} {env env' : ProverEnvironment F}
    (h : ProverEnvironment.OnlyAccessedBelow n (eval · input) env env') :
    (circuit.main input).ComputableWitnesses n env env' := by
  change ((circuit.main input).operations n).forAllFlat n
    { witness n' _ c := env.AgreesBelow n' env' → c.eval env = c.eval env' }
  rw [← Operations.forAll_toFlat_iff]
  refine FlatOperation.forAll_agree_of_imp env env' _ n (fun input_eq => ?_) h
  rw [Operations.forAll_toFlat_iff]
  exact (circuit.computableWitnesses' input_eq).1

/--
The output agrees between two environments that agree below `n`, given input agreement.
(Companion `.2` of `computableWitnesses'`, exposed for output reasoning in parent proofs.)
-/
lemma output_of_input_eq {circuit : FormalCircuitBase F Input Output}
    [ElaboratedCircuit F Input Output circuit.main]
    {n : ℕ} {input : Var Input F} {env env' : ProverEnvironment F}
    (input_eq : eval env input = eval env' input)
    (h_agrees : env.AgreesBelow (n + circuit.localLength input) env') :
    eval env (circuit.output input n) = eval env' (circuit.output input n) :=
  (circuit.computableWitnesses' input_eq).2 h_agrees

/--
`OnlyAccessedBelow`-flavored: the output of a formal circuit only accesses the environment below
`n + localLength`, so it can feed the `OnlyAccessedBelow` premise of a *following* subcircuit.
-/
lemma output_onlyAccessedBelow {circuit : FormalCircuitBase F Input Output}
    [ElaboratedCircuit F Input Output circuit.main]
    {n : ℕ} {input : Var Input F} {env env' : ProverEnvironment F}
    (h : ProverEnvironment.OnlyAccessedBelow n (eval · input) env env') :
    ProverEnvironment.OnlyAccessedBelow (n + circuit.localLength input) (eval · (circuit.output input n)) env env' := by
  intro h_agrees
  have hn := ProverEnvironment.agreesBelow_of_le h_agrees (Nat.le_add_right n (circuit.localLength input))
  exact (circuit.computableWitnesses' (h hn)).2 h_agrees
end FormalCircuitBase

-- simplification of subcircuits in `circuit_norm`

section
variable {F : Type} [FiniteField F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
-- `input_var` at the concrete `Input (Expression F)` type (not `Var Input F`): per the
-- normal-form doctrine in `Provable.lean`, eval lemmas must elaborate at the concrete
-- type so their `@eval` atoms are congruent with goal terms inside `grind`.
variable {env : Environment F} {env_p : ProverEnvironment F} {input_var : Input (Expression F)} {n : ℕ}

section computableWitnessesLaws
variable {n : ℕ} {env env' : ProverEnvironment F}
variable {β' α' : TypeMap} [ProvableType β'] [ProvableType α'] {β'' α'' : TypeMap}

/-!
`Circuit.ComputableWitnesses` laws for the subcircuit inclusions (see the primitive laws
in `Clean.Circuit.Basic`): each inclusion is exactly one per-node obligation.
-/

@[computable_witnesses_norm]
theorem subcircuit_computableWitnesses (circuit : FormalCircuit F β' α') (b : Var β' F) :
    (subcircuit circuit b).ComputableWitnesses n env env' ↔
      (circuit.toSubcircuit n b).ComputableWitnesses n env env' := by
  simp [subcircuit, Circuit.ComputableWitnesses, Operations.ComputableWitnesses,
    Circuit.operations, Operations.forAll]

@[computable_witnesses_norm]
theorem assertion_computableWitnesses (circuit : FormalAssertion F β') (b : Var β' F) :
    (assertion circuit b).ComputableWitnesses n env env' ↔
      (circuit.toSubcircuit n b).ComputableWitnesses n env env' := by
  simp [assertion, Circuit.ComputableWitnesses, Operations.ComputableWitnesses,
    Circuit.operations, Operations.forAll]

@[computable_witnesses_norm]
theorem subcircuitWithAssertion_computableWitnesses (circuit : GeneralFormalCircuit F β' α')
    (b : Var β' F) :
    (subcircuitWithAssertion circuit b).ComputableWitnesses n env env' ↔
      (circuit.toSubcircuit n b).ComputableWitnesses n env env' := by
  simp [subcircuitWithAssertion, Circuit.ComputableWitnesses, Operations.ComputableWitnesses,
    Circuit.operations, Operations.forAll]

@[computable_witnesses_norm]
theorem subcircuitWithHintAssertion_computableWitnesses [CircuitType β''] [CircuitType α'']
    {circuit : GeneralFormalCircuit.WithHint F β'' α''} {b : Var β'' F} :
    (subcircuitWithHintAssertion circuit b).ComputableWitnesses n env env' ↔
      (circuit.toSubcircuit n b).ComputableWitnesses n env env' := by
  simp [subcircuitWithHintAssertion, Circuit.ComputableWitnesses,
    Operations.ComputableWitnesses, Circuit.operations, Operations.forAll]

@[computable_witnesses_norm]
theorem subcircuit_localLength (circuit : FormalCircuit F β' α') (b : Var β' F) :
    (subcircuit circuit b).localLength n = circuit.localLength b := rfl

@[computable_witnesses_norm]
theorem subcircuit_output (circuit : FormalCircuit F β' α') (b : Var β' F) :
    (subcircuit circuit b).output n = circuit.output b n := rfl

@[computable_witnesses_norm]
theorem assertion_localLength (circuit : FormalAssertion F β') (b : Var β' F) :
    (assertion circuit b).localLength n = circuit.localLength b := rfl

@[computable_witnesses_norm]
theorem subcircuitWithAssertion_localLength (circuit : GeneralFormalCircuit F β' α')
    (b : Var β' F) :
    (subcircuitWithAssertion circuit b).localLength n = circuit.localLength b := rfl

@[computable_witnesses_norm]
theorem subcircuitWithAssertion_output (circuit : GeneralFormalCircuit F β' α')
    (b : Var β' F) :
    (subcircuitWithAssertion circuit b).output n = circuit.output b n := rfl

@[computable_witnesses_norm]
theorem subcircuitWithHintAssertion_localLength [CircuitType β''] [CircuitType α'']
    {circuit : GeneralFormalCircuit.WithHint F β'' α''} {b : Var β'' F} :
    (subcircuitWithHintAssertion circuit b).localLength n = circuit.localLength b := rfl

@[computable_witnesses_norm]
theorem subcircuitWithHintAssertion_output [CircuitType β''] [CircuitType α'']
    {circuit : GeneralFormalCircuit.WithHint F β'' α''} {b : Var β'' F} :
    (subcircuitWithHintAssertion circuit b).output n = circuit.output b n := rfl

end computableWitnessesLaws

-- Simplification lemmas for toSubcircuit.localLength

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_localLength (circuit : FormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_localLength (circuit : GeneralFormalCircuit F Input Output) :
  (circuit.toSubcircuit n input_var).localLength = circuit.localLength input_var := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_localLength
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
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
    {F : Type} [FiniteField F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
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

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_soundness
    {F : Type} [FiniteField F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
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

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_completeness
    {F : Type} [FiniteField F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
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

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_usesLocalWitnesses
    {F : Type} [FiniteField F] {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
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

-- (One-directional) simplification lemmas for toSubcircuit.ComputableWitnesses

@[grind ←]
theorem FormalCircuit.toSubcircuit_computableWitnesses {env env' : ProverEnvironment F}
    (circuit : FormalCircuit F Input Output)
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var) :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' := by
  haveI := circuit.elaborated
  simp only [circuit_norm, FormalCircuit.toSubcircuit, Subcircuit.ComputableWitnesses,
    Operations.forAll_toFlat_iff, Operations.forAllFlat]
  exact (circuit.computableWitnesses' (by simpa only [CircuitType.eval_var_prover_to_verifier] using input_eq)).1

theorem FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow {env env' : ProverEnvironment F}
    (circuit : FormalCircuit F Input Output)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F) (fun e => eval e.toEnvironment input_var) env env') :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' := by
  haveI := circuit.elaborated
  simp only [circuit_norm, FormalCircuit.toSubcircuit, Subcircuit.ComputableWitnesses,
    Operations.forAll_toFlat_iff, Operations.forAllFlat]
  exact circuit.computableWitnesses'_onlyAccessedBelow (by simpa only [CircuitType.eval_var_prover_to_verifier] using h)

/-- Backward-reasoning form used by `grind`. The separate offsets let E-matching find
the composition rule before arithmetic normalization proves that they agree. -/
@[grind ←]
theorem FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
    {m n : ℕ} {env env' : ProverEnvironment F}
    (circuit : FormalCircuit F Input Output)
    (h_offset : m = n)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F)
      (fun e => eval e.toEnvironment input_var) env env') :
    (circuit.toSubcircuit m input_var).ComputableWitnesses n env env' := by
  subst m
  exact circuit.toSubcircuit_computableWitnesses_onlyAccessedBelow h

/-- ProvableType (verifier-eval) form of `FormalCircuitBase.output_of_input_eq`; shadows it for
`FormalCircuit` values so parent proofs see the normal-form `eval env.toEnvironment`. -/
@[grind ←]
theorem FormalCircuit.output_of_input_eq {env env' : ProverEnvironment F}
    (circuit : FormalCircuit F Input Output)
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var)
    (h_agrees : env.AgreesBelow (n + circuit.localLength input_var) env') :
    eval env.toEnvironment (circuit.output input_var n) = eval env'.toEnvironment (circuit.output input_var n) := by
  haveI := circuit.elaborated
  have h := (circuit.computableWitnesses'
    (by simpa only [CircuitType.eval_var_prover_to_verifier] using input_eq)).2 h_agrees
  simpa only [CircuitType.eval_var_prover_to_verifier] using h

/-- ProvableType (verifier-eval) form of `FormalCircuitBase.output_onlyAccessedBelow`. -/
@[grind ←]
theorem FormalCircuit.output_onlyAccessedBelow {env env' : ProverEnvironment F}
    (circuit : FormalCircuit F Input Output)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F) (fun e => eval e.toEnvironment input_var) env env') :
    ProverEnvironment.OnlyAccessedBelow (n + circuit.localLength input_var)
      (fun e => eval e.toEnvironment (circuit.output input_var n)) env env' := by
  haveI := circuit.elaborated
  intro h_agrees
  have hn := ProverEnvironment.agreesBelow_of_le h_agrees (Nat.le_add_right n (circuit.localLength input_var))
  have hin : eval env input_var = eval env' input_var := by
    simpa only [CircuitType.eval_expression_prover_to_verifier] using h hn
  have hout := (circuit.computableWitnesses' hin).2 h_agrees
  simpa only [CircuitType.eval_expression_prover_to_verifier] using hout

/-- Elementwise companion to `output_of_input_eq` for `fields`-valued outputs. Parent witness
expressions embed the child's output per element, as `Expression.eval … (output)[i]`, so the
composite-`eval` rules never match there; the multi-pattern below keys this rule on the pair of
element spellings instead. Stated on `FormalCircuitBase` so it covers every bundle kind
(`FormalCircuit`, `GeneralFormalCircuit`, …) through their `base` projection. -/
theorem FormalCircuitBase.output_getElem_of_input_eq {env env' : ProverEnvironment F} {m : ℕ}
    (circuit : FormalCircuitBase F Input (fields m))
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var)
    (h_agrees : env.AgreesBelow (n + circuit.localLength input_var) env')
    (i : ℕ) (hi : i < m) :
    Expression.eval env.toEnvironment (circuit.output input_var n)[i]
      = Expression.eval env'.toEnvironment (circuit.output input_var n)[i] := by
  haveI := circuit.elaborated
  have h := circuit.output_of_input_eq
    (by simpa only [CircuitType.eval_var_prover_to_verifier] using input_eq) h_agrees
  rw [ProvableType.getElem_eval_fields_prover _ i hi, ProvableType.getElem_eval_fields_prover _ i hi, h]

grind_pattern FormalCircuitBase.output_getElem_of_input_eq =>
  Expression.eval env.toEnvironment (circuit.output input_var n)[i],
  Expression.eval env'.toEnvironment (circuit.output input_var n)[i]

/-- `field`-output companion to `output_of_input_eq`, keyed on the plain `Expression.eval`
spelling that parent witness expressions contain. -/
theorem FormalCircuitBase.output_field_of_input_eq {env env' : ProverEnvironment F}
    (circuit : FormalCircuitBase F Input field)
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var)
    (h_agrees : env.AgreesBelow (n + circuit.localLength input_var) env') :
    Expression.eval env.toEnvironment (circuit.output input_var n)
      = Expression.eval env'.toEnvironment (circuit.output input_var n) := by
  haveI := circuit.elaborated
  have h := circuit.output_of_input_eq
    (by simpa only [CircuitType.eval_var_prover_to_verifier] using input_eq) h_agrees
  simpa only [circuit_norm] using h

grind_pattern FormalCircuitBase.output_field_of_input_eq =>
  Expression.eval env.toEnvironment (circuit.output input_var n),
  Expression.eval env'.toEnvironment (circuit.output input_var n)

theorem FormalAssertion.toSubcircuit_computableWitnesses {env env' : ProverEnvironment F}
    (circuit : FormalAssertion F Input)
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var) :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' := by
  haveI := circuit.elaborated
  simp only [circuit_norm, FormalAssertion.toSubcircuit, Subcircuit.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact (circuit.computableWitnesses' (by simpa only [CircuitType.eval_var_prover_to_verifier] using input_eq)).1

theorem FormalAssertion.toSubcircuit_computableWitnesses_onlyAccessedBelow {env env' : ProverEnvironment F}
    (circuit : FormalAssertion F Input)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F) (fun e => eval e.toEnvironment input_var) env env') :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' := by
  haveI := circuit.elaborated
  simp only [circuit_norm, FormalAssertion.toSubcircuit, Subcircuit.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact circuit.computableWitnesses'_onlyAccessedBelow (by simpa only [CircuitType.eval_var_prover_to_verifier] using h)

/-- Backward-reasoning form used by `grind`. Keeping the subcircuit's type-index offset
separate from the computability offset lets E-matching find the rule before arithmetic
normalization proves that the offsets agree. -/
@[grind ←]
theorem FormalAssertion.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
    {m n : ℕ} {env env' : ProverEnvironment F}
    (circuit : FormalAssertion F Input)
    (h_offset : m = n)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F)
      (fun e => eval e.toEnvironment input_var) env env') :
    (circuit.toSubcircuit m input_var).ComputableWitnesses n env env' := by
  subst m
  exact circuit.toSubcircuit_computableWitnesses_onlyAccessedBelow h

theorem GeneralFormalCircuit.WithHint.toSubcircuit_computableWitnesses
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output] {env env' : ProverEnvironment F}
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input_var : Var Input F)
    (input_eq : eval env input_var = eval env' input_var) :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' := by
  haveI := circuit.elaborated
  simp only [circuit_norm, GeneralFormalCircuit.WithHint.toSubcircuit, Subcircuit.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact (circuit.computableWitnesses' input_eq).1

theorem GeneralFormalCircuit.WithHint.toSubcircuit_computableWitnesses_onlyAccessedBelow
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output] {env env' : ProverEnvironment F}
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input_var : Var Input F)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input_var) env env') :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' := by
  haveI := circuit.elaborated
  simp only [circuit_norm, GeneralFormalCircuit.WithHint.toSubcircuit, Subcircuit.ComputableWitnesses,
    Operations.forAllFlat, Operations.forAll_toFlat_iff]
  exact circuit.computableWitnesses'_onlyAccessedBelow h

/-- Backward-reasoning form used by `grind`; see the `FormalCircuit` variant. -/
@[grind ←]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {m n : ℕ} {env env' : ProverEnvironment F}
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input_var : Var Input F)
    (h_offset : m = n)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F) (eval · input_var) env env') :
    (circuit.toSubcircuit m input_var).ComputableWitnesses n env env' := by
  subst m
  exact circuit.toSubcircuit_computableWitnesses_onlyAccessedBelow input_var h

theorem GeneralFormalCircuit.toSubcircuit_computableWitnesses {env env' : ProverEnvironment F}
    (circuit : GeneralFormalCircuit F Input Output)
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var) :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' :=
  GeneralFormalCircuit.WithHint.toSubcircuit_computableWitnesses circuit.toWithHint input_var
    (by simpa only [CircuitType.eval_var_prover_to_verifier] using input_eq)

theorem GeneralFormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow {env env' : ProverEnvironment F}
    (circuit : GeneralFormalCircuit F Input Output)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F) (fun e => eval e.toEnvironment input_var) env env') :
    (circuit.toSubcircuit n input_var).ComputableWitnesses n env env' :=
  GeneralFormalCircuit.WithHint.toSubcircuit_computableWitnesses_onlyAccessedBelow circuit.toWithHint input_var
    (by simpa only [CircuitType.eval_var_prover_to_verifier] using h)

/-- Backward-reasoning form used by `grind`; see the `FormalCircuit` variant. -/
@[grind ←]
theorem GeneralFormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq
    {m n : ℕ} {env env' : ProverEnvironment F}
    (circuit : GeneralFormalCircuit F Input Output)
    (h_offset : m = n)
    (h : ProverEnvironment.OnlyAccessedBelow n (F:=F)
      (fun e => eval e.toEnvironment input_var) env env') :
    (circuit.toSubcircuit m input_var).ComputableWitnesses n env env' := by
  subst m
  exact circuit.toSubcircuit_computableWitnesses_onlyAccessedBelow h

theorem GeneralFormalCircuit.output_of_input_eq
    {env env' : ProverEnvironment F} (circuit : GeneralFormalCircuit F Input Output)
    (input_eq : eval env.toEnvironment input_var = eval env'.toEnvironment input_var)
    (h_agrees : env.AgreesBelow (n + circuit.localLength input_var) env') :
    eval env.toEnvironment (circuit.output input_var n) = eval env'.toEnvironment (circuit.output input_var n) := by
  haveI := circuit.elaborated
  have h := circuit.base.output_of_input_eq ?_ h_agrees
  <;> simp_all only [circuit_norm]

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
theorem GeneralFormalCircuit.WithHint.toSubcircuit_channelsWithGuarantees
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input_var : Var Input F) :
  (circuit.toSubcircuit n input_var).channelsWithGuarantees = circuit.channelsWithGuarantees := rfl

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_channelsWithRequirements
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input_var : Var Input F) :
  (circuit.toSubcircuit n input_var).channelsWithRequirements = circuit.channelsWithRequirements := rfl

@[circuit_norm]
theorem FormalCircuit.toSubcircuit_channelsLawful
    (circuit : FormalCircuit F Input Output) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  simp only [Subcircuit.ChannelsLawful, FormalCircuit.toSubcircuit, Operations.toNested_toFlat]
  constructor
  · intro env
    rw [FlatOperation.inChannelsOrGuarantees_toFlat]
    exact circuit.in_channels_or_guarantees_full input_var n env
  constructor
  · intro env h_constraints
    rw [Circuit.constraintsHold_toFlat_iff] at h_constraints
    rw [FlatOperation.inChannelsOrRequirements_toFlat]
    exact circuit.in_channels_or_requirements_full_of_constraints h_constraints
  · rw [Operations.channels_toFlat]
    exact circuit.channels_subset input_var n

@[circuit_norm]
theorem FormalAssertion.toSubcircuit_channelsLawful
    (circuit : FormalAssertion F Input) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  simp only [Subcircuit.ChannelsLawful, FormalAssertion.toSubcircuit, Operations.toNested_toFlat]
  constructor
  · intro env
    rw [FlatOperation.inChannelsOrGuarantees_toFlat]
    exact circuit.in_channels_or_guarantees_full input_var n env
  constructor
  · intro env h_constraints
    rw [FlatOperation.inChannelsOrRequirements_toFlat]
    exact circuit.in_channels_or_requirements_full_of_constraints
      (Circuit.constraintsHold_toFlat_iff.mp h_constraints)
  · rw [Operations.channels_toFlat]
    exact circuit.channels_subset input_var n

@[circuit_norm]
theorem GeneralFormalCircuit.WithHint.toSubcircuit_channelsLawful
    {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input_var : Var Input F) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  simp only [Subcircuit.ChannelsLawful, GeneralFormalCircuit.WithHint.toSubcircuit,
    Operations.toNested_toFlat]
  constructor
  · intro env
    rw [FlatOperation.inChannelsOrGuarantees_toFlat]
    exact circuit.in_channels_or_guarantees_full input_var n env
  constructor
  · intro env h_constraints
    rw [FlatOperation.inChannelsOrRequirements_toFlat]
    exact circuit.in_channels_or_requirements_full_of_constraints
      (Circuit.constraintsHold_toFlat_iff.mp h_constraints)
  · rw [Operations.channels_toFlat]
    exact circuit.channels_subset input_var n

@[circuit_norm]
theorem GeneralFormalCircuit.toSubcircuit_channelsLawful
    (circuit : GeneralFormalCircuit F Input Output) :
    (circuit.toSubcircuit n input_var).ChannelsLawful := by
  exact GeneralFormalCircuit.WithHint.toSubcircuit_channelsLawful circuit.toWithHint input_var

attribute [explicit_circuit_no_unfold] subcircuit assertion subcircuitWithAssertion subcircuitWithHintAssertion

namespace ExplicitCircuit
@[explicit_circuit_constructor]
instance fromSubcircuit (circuit : FormalCircuit F Input Output) (input : Var Input F) :
    ExplicitCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
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

@[explicit_circuit_constructor]
instance fromAssertion (circuit : FormalAssertion F Input) (input : Var Input F) :
    ExplicitCircuit (assertion circuit input) where
  output _ := ()
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
  subcircuitsConsistent n := by
    change Operations.SubcircuitsConsistent n [.subcircuit (_)]
    simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    exact ⟨trivial, trivial⟩
  channelsLawful := by simp [circuit_norm]

@[circuit_norm, explicit_circuit_norm]
theorem fromAssertion_output {circuit : FormalAssertion F Input} {input} {n : ℕ} :
    (fromAssertion circuit input).output n = () := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromAssertion_localLength {circuit : FormalAssertion F Input} {input} {n : ℕ} :
    (fromAssertion circuit input).localLength n = circuit.localLength input := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromAssertion_operations {circuit : FormalAssertion F Input} {input} {n : ℕ} :
    (fromAssertion circuit input).operations n = [.subcircuit (circuit.toSubcircuit n input)] := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromAssertion_channelsWithGuarantees {circuit : FormalAssertion F Input} {input} {n : ℕ} :
    (fromAssertion circuit input).channelsWithGuarantees n = circuit.channelsWithGuarantees := rfl

@[explicit_circuit_constructor]
instance fromSubcircuitWithAssertion (circuit : GeneralFormalCircuit F Input Output) (input : Var Input F) :
    ExplicitCircuit (subcircuitWithAssertion circuit input) where
  output n := circuit.output input n
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
  subcircuitsConsistent n := by
    change Operations.SubcircuitsConsistent n [.subcircuit (_)]
    simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    exact ⟨trivial, trivial⟩
  channelsLawful := by simp [circuit_norm]

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithAssertion_output {circuit : GeneralFormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithAssertion circuit input).output n = circuit.output input n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithAssertion_localLength {circuit : GeneralFormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithAssertion circuit input).localLength n = circuit.localLength input := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithAssertion_operations {circuit : GeneralFormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithAssertion circuit input).operations n = [.subcircuit (circuit.toSubcircuit n input)] := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithAssertion_channelsWithGuarantees {circuit : GeneralFormalCircuit F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithAssertion circuit input).channelsWithGuarantees n = circuit.channelsWithGuarantees := rfl

@[explicit_circuit_constructor]
instance fromSubcircuitWithHintAssertion {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    (circuit : GeneralFormalCircuit.WithHint F Input Output) (input : Var Input F) :
    ExplicitCircuit (subcircuitWithHintAssertion circuit input) where
  output n := circuit.output input n
  localLength _ := circuit.localLength input
  operations n := [.subcircuit (circuit.toSubcircuit n input)]
  channelsWithGuarantees _ := circuit.channelsWithGuarantees
  subcircuitsConsistent n := by
    change Operations.SubcircuitsConsistent n [.subcircuit (_)]
    simp only [Operations.SubcircuitsConsistent, Operations.forAll]
    exact ⟨trivial, trivial⟩
  channelsLawful := by simp [circuit_norm]

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithHintAssertion_output {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : GeneralFormalCircuit.WithHint F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithHintAssertion circuit input).output n = circuit.output input n := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithHintAssertion_localLength {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : GeneralFormalCircuit.WithHint F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithHintAssertion circuit input).localLength n = circuit.localLength input := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithHintAssertion_operations {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : GeneralFormalCircuit.WithHint F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithHintAssertion circuit input).operations n = [.subcircuit (circuit.toSubcircuit n input)] := rfl

@[circuit_norm, explicit_circuit_norm]
theorem fromSubcircuitWithHintAssertion_channelsWithGuarantees {Input Output : TypeMap} [CircuitType Input] [CircuitType Output]
    {circuit : GeneralFormalCircuit.WithHint F Input Output} {input} {n : ℕ} :
    (fromSubcircuitWithHintAssertion circuit input).channelsWithGuarantees n = circuit.channelsWithGuarantees := rfl
end ExplicitCircuit

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
